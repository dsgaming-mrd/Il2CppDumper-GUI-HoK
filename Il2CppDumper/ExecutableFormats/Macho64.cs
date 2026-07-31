using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Windows.Media;
using static Il2CppDumper.ArmUtils;

namespace Il2CppDumper
{
    public sealed class Macho64 : Il2Cpp
    {
        private static readonly byte[] FeatureBytes1 = { 0x2, 0x0, 0x80, 0xD2 };//MOV X2, #0
        private static readonly byte[] FeatureBytes2 = { 0x3, 0x0, 0x80, 0x52 };//MOV W3, #0
        private readonly List<MachoSection64Bit> sections = new();
        private readonly ulong vmaddr;
        /// <summary>File offset where appended BSS zeros start (0 = not expanded).</summary>
        private readonly ulong bssFileBase;

        public Macho64(Stream stream) : base(stream)
        {
            Position += 16; //skip magic, cputype, cpusubtype, filetype
            var ncmds = ReadUInt32();
            Position += 12; //skip sizeofcmds, flags, reserved
            for (var i = 0; i < ncmds; i++)
            {
                var pos = Position;
                var cmd = ReadUInt32();
                var cmdsize = ReadUInt32();
                switch (cmd)
                {
                    case 0x19: //LC_SEGMENT_64
                        var segname = Encoding.UTF8.GetString(ReadBytes(16)).TrimEnd('\0');
                        if (segname == "__TEXT") //__PAGEZERO
                        {
                            vmaddr = ReadUInt64();
                        }
                        else
                        {
                            Position += 8;
                        }
                        Position += 32; //skip vmsize, fileoff, filesize, maxprot, initprot
                        var nsects = ReadUInt32();
                        Position += 4; //skip flags
                        for (var j = 0; j < nsects; j++)
                        {
                            var section = new MachoSection64Bit();
                            sections.Add(section);
                            section.sectname = Encoding.UTF8.GetString(ReadBytes(16)).TrimEnd('\0');
                            Position += 16; //skip segname
                            section.addr = ReadUInt64();
                            section.size = ReadUInt64();
                            section.offset = ReadUInt32();
                            Position += 12; //skip align, reloff, nreloc
                            section.flags = ReadUInt32();
                            Position += 12; //skip reserved1, reserved2, reserved3
                        }
                        break;
                    case 0x2C: //LC_ENCRYPTION_INFO_64
                        Position += 8;
                        var cryptID = ReadUInt32();
                        if (cryptID != 0)
                        {
                            MainForm.Log("ERROR: This Mach-O executable is encrypted and cannot be processed.", Brushes.Orange);
                        }
                        break;
                }
                Position = pos + cmdsize;//skip
            }

            // Detect pre-expanded image: stream longer than highest file-backed section end,
            // trailing region used as BSS backing for MapVATR.
            ulong maxFileEnd = 0;
            foreach (var s in sections)
            {
                if (s.offset != 0)
                {
                    var end = s.offset + s.size;
                    if (end > maxFileEnd) maxFileEnd = end;
                }
            }
            if ((ulong)Length > maxFileEnd + 0x1000)
            {
                bssFileBase = maxFileEnd;
                // Fix zero-offset bss/common sections to point into trailing region
                ulong cursor = bssFileBase;
                foreach (var section in sections.Where(s =>
                             (s.sectname is "__bss" or "__common" or "__thread_bss") && s.offset == 0 && s.size > 0))
                {
                    section.offset = cursor;
                    cursor += section.size;
                }
            }
        }

        /// <summary>
        /// Expand a static Mach-O so __bss/__common become file-backed (zero-filled),
        /// allowing MapVATR of CodeRegistration/MetadataRegistration addresses in BSS.
        /// Does not decrypt runtime data — tables stay zero until a real memory dump / CSB decrypt.
        /// </summary>
        public static byte[] ExpandBssToFile(byte[] data)
        {
            if (data == null || data.Length < 32)
                return data;
            if (BitConverter.ToUInt32(data, 0) != 0xFEEDFACF)
                return data;

            using var ms = new MemoryStream(data, writable: false);
            using var br = new BinaryReader(ms, Encoding.UTF8, leaveOpen: true);
            ms.Position = 16;
            var ncmds = br.ReadUInt32();
            ms.Position = 32;
            var bssRegions = new List<(long headerOffset, ulong size)>();
            for (var i = 0; i < ncmds; i++)
            {
                var pos = ms.Position;
                var cmd = br.ReadUInt32();
                var cmdsize = br.ReadUInt32();
                if (cmd == 0x19)
                {
                    ms.Position = pos + 8 + 16; // skip segname
                    ms.Position += 8 + 8 + 8 + 8 + 4 + 4; // vmaddr..initprot
                    var nsects = br.ReadUInt32();
                    ms.Position += 4;
                    for (var j = 0; j < nsects; j++)
                    {
                        var sectPos = ms.Position;
                        var sectname = Encoding.UTF8.GetString(br.ReadBytes(16)).TrimEnd('\0');
                        ms.Position += 16; // segname
                        ms.Position += 8; // addr
                        var size = br.ReadUInt64();
                        var offsetFieldPos = ms.Position;
                        var offset = br.ReadUInt32();
                        ms.Position = sectPos + 80;
                        if ((sectname is "__bss" or "__common" or "__thread_bss") && offset == 0 && size > 0 && size < int.MaxValue)
                        {
                            bssRegions.Add((offsetFieldPos, size));
                        }
                    }
                }
                ms.Position = pos + cmdsize;
            }

            if (bssRegions.Count == 0)
                return data;

            var totalBss = bssRegions.Aggregate(0UL, (a, b) => a + b.size);
            if (totalBss > 256UL * 1024 * 1024) // safety
                return data;

            var expanded = new byte[data.Length + (int)totalBss];
            Buffer.BlockCopy(data, 0, expanded, 0, data.Length);
            var cursor = (uint)data.Length;
            foreach (var (headerOffset, size) in bssRegions)
            {
                // patch section offset field
                Buffer.BlockCopy(BitConverter.GetBytes(cursor), 0, expanded, (int)headerOffset, 4);
                cursor += (uint)size;
            }
            return expanded;
        }

        public override ulong MapVATR(ulong addr)
        {
            if (addr == 0)
                return 0;
            var section = sections.FirstOrDefault(x => addr >= x.addr && addr < x.addr + x.size);
            if (section == null)
            {
                // last-byte inclusive fallback (original Il2CppDumper used <=)
                section = sections.FirstOrDefault(x => addr >= x.addr && addr <= x.addr + x.size);
            }
            if (section == null)
                throw new Exception($"Address 0x{addr:X} is not in any Mach-O section.");
            // BSS/common: prefer file-backed offset if present (expanded image / memory dump).
            if (section.sectname is "__bss" or "__common" or "__thread_bss")
            {
                if (IsDumped)
                {
                    return addr - ImageBase;
                }
                if (section.offset != 0)
                {
                    return addr - section.addr + section.offset;
                }
                // Fallback: if stream was expanded past original file, map into trailing BSS region.
                if (bssFileBase != 0)
                {
                    return bssFileBase + (addr - section.addr);
                }
                throw new Exception($"Address 0x{addr:X} is in {section.sectname} (not present in static Mach-O). Use a runtime memory dump.");
            }
            return addr - section.addr + section.offset;
        }

        public override ulong MapRTVA(ulong addr)
        {
            var section = sections.FirstOrDefault(x => addr >= x.offset && addr <= x.offset + x.size);
            if (section == null)
            {
                return 0;
            }
            if (section.sectname is "__bss" or "__common" or "__thread_bss")
            {
                if (IsDumped)
                {
                    return addr + ImageBase;
                }
                throw new Exception();
            }
            return addr - section.offset + section.addr;
        }

        public override bool Search()
        {
            var codeRegistration = 0ul;
            var metadataRegistration = 0ul;

            // Modern Unity / protected builds (e.g. HOK Escher):
            //   ADRP X0, page
            //   ADD  X0, X0, #cr_lo
            //   ADD  X1, X0, #(MR - CR)
            //   ADD  X2, X0, #(opts - CR)
            //   B    il2cpp_codegen_register
            // Tables may live in __bss (runtime-only). Still recover addresses for manual / memory dump.
            if (codeRegistration == 0 && Version >= 24)
            {
                if (TryFindCodegenRegisterRefs(out codeRegistration, out metadataRegistration))
                {
                    CodeRegistrationAddress = codeRegistration;
                    MetadataRegistrationAddress = metadataRegistration;
                    MainForm.Log("CodeRegistration : {0:x}", codeRegistration);
                    MainForm.Log("MetadataRegistration : {0:x}", metadataRegistration);
                    try
                    {
                        Init(codeRegistration, metadataRegistration);
                        if (types != null && types.Length > 0)
                            return true;
                    }
                    catch
                    {
                    }
                    return false;
                }
            }

            if (Version < 23)
            {
                var __mod_init_func = sections.First(x => x.sectname == "__mod_init_func");
                var addrs = ReadClassArray<ulong>(__mod_init_func.offset, __mod_init_func.size / 8);
                foreach (var i in addrs)
                {
                    if (i > 0)
                    {
                        var flag = false;
                        var subaddr = 0ul;
                        Position = MapVATR(i);
                        var buff = ReadBytes(4);
                        if (FeatureBytes1.SequenceEqual(buff))
                        {
                            buff = ReadBytes(4);
                            if (FeatureBytes2.SequenceEqual(buff))
                            {
                                Position += 8;
                                var inst = ReadBytes(4);
                                if (IsAdr(inst))
                                {
                                    subaddr = DecodeAdr(i + 16, inst);
                                    flag = true;
                                }
                            }
                        }
                        else
                        {
                            Position += 0xc;
                            buff = ReadBytes(4);
                            if (FeatureBytes2.SequenceEqual(buff))
                            {
                                buff = ReadBytes(4);
                                if (FeatureBytes1.SequenceEqual(buff))
                                {
                                    Position -= 0x10;
                                    var inst = ReadBytes(4);
                                    if (IsAdr(inst))
                                    {
                                        subaddr = DecodeAdr(i + 8, inst);
                                        flag = true;
                                    }
                                }
                            }
                        }
                        if (flag)
                        {
                            var rsubaddr = MapVATR(subaddr);
                            Position = rsubaddr;
                            codeRegistration = DecodeAdrp(subaddr, ReadBytes(4));
                            codeRegistration += DecodeAdd(ReadBytes(4));
                            Position = rsubaddr + 8;
                            metadataRegistration = DecodeAdrp(subaddr + 8, ReadBytes(4));
                            metadataRegistration += DecodeAdd(ReadBytes(4));
                        }
                    }
                }
            }
            if (Version == 23)
            {
                /* ADRP X0, unk
                 * ADD X0, X0, unk
                 * ADR X1, sub
                 * NOP
                 * MOV X2, #0
                 * MOV W3, #0
                 * B sub
                 */
                var __mod_init_func = sections.First(x => x.sectname == "__mod_init_func");
                var addrs = ReadClassArray<ulong>(__mod_init_func.offset, __mod_init_func.size / 8);
                foreach (var i in addrs)
                {
                    if (i > 0)
                    {
                        Position = MapVATR(i) + 16;
                        var buff = ReadBytes(4);
                        if (FeatureBytes1.SequenceEqual(buff))
                        {
                            buff = ReadBytes(4);
                            if (FeatureBytes2.SequenceEqual(buff))
                            {
                                Position -= 16;
                                var subaddr = DecodeAdr(i + 8, ReadBytes(4));
                                var rsubaddr = MapVATR(subaddr);
                                Position = rsubaddr;
                                codeRegistration = DecodeAdrp(subaddr, ReadBytes(4));
                                codeRegistration += DecodeAdd(ReadBytes(4));
                                Position = rsubaddr + 8;
                                metadataRegistration = DecodeAdrp(subaddr + 8, ReadBytes(4));
                                metadataRegistration += DecodeAdd(ReadBytes(4));
                            }
                        }
                    }
                }
            }
            if (Version >= 24)
            {
                /* ADRP X0, unk
                 * ADD X0, X0, unk
                 * ADR X1, sub
                 * NOP
                 * MOV W3, #0
                 * MOV X2, #0
                 * B sub
                 */
                var __mod_init_func = sections.First(x => x.sectname == "__mod_init_func");
                var addrs = ReadClassArray<ulong>(__mod_init_func.offset, __mod_init_func.size / 8);
                foreach (var i in addrs)
                {
                    if (i > 0)
                    {
                        Position = MapVATR(i) + 16;
                        var buff = ReadBytes(4);
                        if (FeatureBytes2.SequenceEqual(buff))
                        {
                            buff = ReadBytes(4);
                            if (FeatureBytes1.SequenceEqual(buff))
                            {
                                Position -= 16;
                                var subaddr = DecodeAdr(i + 8, ReadBytes(4));
                                var rsubaddr = MapVATR(subaddr);
                                Position = rsubaddr;
                                codeRegistration = DecodeAdrp(subaddr, ReadBytes(4));
                                codeRegistration += DecodeAdd(ReadBytes(4));
                                Position = rsubaddr + 8;
                                metadataRegistration = DecodeAdrp(subaddr + 8, ReadBytes(4));
                                metadataRegistration += DecodeAdd(ReadBytes(4));
                            }
                        }
                    }
                }
            }
            if (codeRegistration != 0 && metadataRegistration != 0)
            {
                MainForm.Log("CodeRegistration : {0:x}", codeRegistration);
                MainForm.Log("MetadataRegistration : {0:x}", metadataRegistration);
                try
                {
                    Init(codeRegistration, metadataRegistration);
                    return true;
                }
                catch
                {
                    // silently continue to allow synthetic fallback
                }
            }
            return false;
        }

        public override bool PlusSearch(int methodCount, int typeDefinitionsCount, int imageCount)
        {
            var sectionHelper = GetSectionHelper(methodCount, typeDefinitionsCount, imageCount);
            var codeRegistration = sectionHelper.FindCodeRegistration();
            var metadataRegistration = sectionHelper.FindMetadataRegistration();
            return AutoPlusInit(codeRegistration, metadataRegistration);
        }

        public override bool SymbolSearch()
        {
            return false;
        }

        public override ulong GetRVA(ulong pointer)
        {
            return pointer - vmaddr;
        }
        
        public override SectionHelper GetSectionHelper(int methodCount, int typeDefinitionsCount, int imageCount)
        {
            // Include all readable file-backed data-like sections (not only __const/__data names).
            var data = sections.Where(x =>
                x.offset != 0 && x.size > 0 &&
                (x.sectname is "__const" or "__cstring" or "__data" or "__got" or "__mod_init_func" or
                 "__cfstring" or "__objc_const" or "__objc_data" ||
                 x.flags == 0 || x.flags == 0x2)).ToArray();
            if (data.Length == 0)
            {
                data = sections.Where(x => x.offset != 0 && x.size > 0 && (x.flags & 0x80000000) == 0).ToArray();
            }
            var code = sections.Where(x => x.flags == 0x80000400).ToArray();
            var bss = sections.Where(x => x.flags == 1u).ToArray();
            var sectionHelper = new SectionHelper(this, methodCount, typeDefinitionsCount, metadataUsagesCount, imageCount);
            sectionHelper.SetSection(SearchSectionType.Exec, code);
            sectionHelper.SetSection(SearchSectionType.Data, data);
            sectionHelper.SetSection(SearchSectionType.Bss, bss);
            return sectionHelper;
        }

        public override bool CheckDump() => false;
		
		public override ulong ReadUIntPtr()
        {
            var pointer = ReadUInt64();
            if (pointer > vmaddr + 0xFFFFFFFF)
            {
                var addr = Position;
                var section = sections.First(x => addr >= x.offset && addr <= x.offset + x.size);
                if (section.sectname == "__const" || section.sectname == "__data")
                {
                    var rva = pointer - vmaddr;
                    rva &= 0xFFFFFFFF;
                    pointer = rva + vmaddr;
                }
            }
            return pointer;
        }

        private bool TryFindCodegenRegisterRefs(out ulong codeRegistration, out ulong metadataRegistration)
        {
            codeRegistration = 0;
            metadataRegistration = 0;
            try
            {
                // Scan executable text for:
                //   ADRP X0, page / ADD X0,X0,#lo / ADD X1,X0,#delta / ADD X2,X0,#opts
                var textSecs = sections.Where(x => x.flags == 0x80000400 && x.offset != 0 && x.size > 16).ToArray();
                foreach (var sec in textSecs)
                {
                    var size = (int)Math.Min(sec.size, int.MaxValue - 16);
                    Position = sec.offset;
                    var buff = ReadBytes(size);
                    for (var off = 0; off + 16 <= buff.Length; off += 4)
                    {
                        var inst0 = BitConverter.ToUInt32(buff, off);
                        if ((inst0 & 0x9F00001F) != 0x90000000) // ADRP X0
                            continue;
                        var inst1 = BitConverter.ToUInt32(buff, off + 4);
                        if ((inst1 & 0xFFC003FF) != 0x91000000) // ADD X0, X0, #imm
                            continue;
                        var inst2 = BitConverter.ToUInt32(buff, off + 8);
                        if ((inst2 & 0xFFC003FF) != 0x91000001) // ADD X1, X0, #imm
                            continue;
                        var inst3 = BitConverter.ToUInt32(buff, off + 12);
                        if ((inst3 & 0xFFC003FF) != 0x91000002) // ADD X2, X0, #imm (options)
                            continue;

                        var pc = sec.addr + (ulong)off;
                        var page = DecodeAdrpPage(pc, inst0);
                        var cr = page + DecodeAddImm(inst1);
                        var mr = cr + DecodeAddImm(inst2);
                        if (mr <= cr)
                            continue;

                        var crSec = sections.FirstOrDefault(x => cr >= x.addr && cr < x.addr + x.size);
                        var mrSec = sections.FirstOrDefault(x => mr >= x.addr && mr < x.addr + x.size);
                        if (crSec == null || mrSec == null)
                            continue;

                        codeRegistration = cr;
                        metadataRegistration = mr;
                        return true;
                    }
                }
            }
            catch
            {
                // ignored
            }
            return false;
        }

        private static ulong DecodeAdrpPage(ulong pc, uint inst)
        {
            var immlo = (inst >> 29) & 3u;
            var immhi = (inst >> 5) & 0x7FFFFu;
            long imm = (long)((immhi << 2) | immlo);
            if ((imm & (1L << 20)) != 0)
                imm |= ~((1L << 21) - 1);
            imm <<= 12;
            var page = (long)(pc & ~0xFFFUL) + imm;
            return (ulong)page;
        }

        private static ulong DecodeAddImm(uint inst)
        {
            var imm = (inst >> 10) & 0xFFFu;
            var shift = (inst >> 22) & 3u;
            if (shift == 1) imm <<= 12;
            return imm;
        }

        private static ulong DecodeAdrp(ulong pc, byte[] inst)
        {
            return DecodeAdrpPage(pc, BitConverter.ToUInt32(inst, 0));
        }

        private static ulong DecodeAdd(byte[] inst)
        {
            return DecodeAddImm(BitConverter.ToUInt32(inst, 0));
        }
    }
}
