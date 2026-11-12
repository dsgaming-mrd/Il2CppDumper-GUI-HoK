using System;
using System.Collections.Generic;
using System.Linq;
using System.Security.Cryptography;
using System.Text;
using static Il2CppDumper.Il2CppConstants;

namespace Il2CppDumper
{
    internal readonly record struct MachoSectionInfo(string SegName, MachoSection64Bit Section);

    internal static class HoKEscherRecovery
    {
        private readonly record struct PointerRun(int StartSlot, int EndSlot, int NonZeroCount, ulong FirstVa, ulong LastVa, MachoSection64Bit Section);
        private readonly record struct GlobalAnchor(int Slot, int ImgRank, int Weight, int ImgIdx, int MethodSeq, int ApproxSeq = -1);
        private readonly record struct CstrTag(int Rank, int ImgIdx, int Weight, int MethodIdx, int MethodSeq, bool IsMethodExact, int TypeDefIdx, int ApproxSeq = -1);
        private readonly record struct DelegateInfo(int ImgIdx, int TdIdx, int CtorMethodIdx, int CtorSeq);

        public static bool TryRecover(
            Macho64 macho,
            Metadata meta,
            ulong textSegmentVmaddr,
            IReadOnlyList<MachoSectionInfo> sectionInfos,
            uint funcStartsOffset,
            uint funcStartsSize,
            uint exportTrieOffset,
            uint exportTrieSize)
        {
            if (macho == null || meta == null || macho.Is32Bit || sectionInfos == null || sectionInfos.Count == 0)
            {
                return false;
            }

            if (!TryGetSection(sectionInfos, "__TEXT", "__text", out var textSec))
            {
                return false;
            }
            if (funcStartsOffset == 0 || funcStartsSize == 0)
            {
                return false;
            }

            var textVa = textSec.addr;
            var textSize = textSec.size;
            var textEnd = textVa + textSize;

            // 1. Discover Run[0], Run[1], Run[2] pointer runs across non-executable data sections first
            // so standard non-Escher binaries bail out without reading the full __text section.
            if (!TryFindPointerRuns(macho, sectionInfos, textVa, textEnd, out var run0, out var run2, out var dense))
            {
                return false;
            }

            // 2. Parse LC_FUNCTION_STARTS dynamically.
            var allFuncs = ParseFunctionStarts(macho, funcStartsOffset, funcStartsSize, textSegmentVmaddr, textVa, textEnd);
            if (allFuncs.Length < 1000)
            {
                return false;
            }

            var textBytes = ReadStreamSlice(macho, textSec.offset, checked((int)textSize));

            var cstrSec = FindCStringSection(sectionInfos);
            var cstrVa = cstrSec?.addr ?? 0;
            var cstrBytes = cstrSec != null && cstrSec.size > 0
                ? ReadStreamSlice(macho, cstrSec.offset, checked((int)cstrSec.size))
                : Array.Empty<byte>();

            // 3. Detect ObjectHeaderSize (8 vs 16) dynamically from _il2cpp_object_header_size export or AdjustorThunks.
            var objHdrSize = DetectObjectHeaderSize(macho, textBytes, textVa, textSize, allFuncs, exportTrieOffset, exportTrieSize, textSegmentVmaddr);
            var hasObjectMonitor = objHdrSize >= 16;

            // 4. Identify monoEnd, lastCodeSlot, altMask, cgSlot, r2First inside Run[0].
            var r2First = run2.FirstVa;
            var monoEnd = FindMonoEnd(dense, r2First);
            var lastCodeSlot = -1;
            var r0Set = new HashSet<ulong>(monoEnd);
            for (var k = 0; k < monoEnd; k++)
            {
                var v = dense[k];
                if (v != 0 && v < r2First)
                {
                    lastCodeSlot = k;
                    r0Set.Add(v);
                }
            }
            if (lastCodeSlot <= 0)
            {
                return false;
            }

            var altMask = BuildAltZeroMask(dense, monoEnd);
            var cgSlot = FindCodegenRegistrationSlot(dense, lastCodeSlot, altMask, textBytes, textVa);
            if (TryResolveRegistrationAddresses(dense, cgSlot, textBytes, textVa, out var regCode, out var regMeta))
            {
                Logger.Log("CodeRegistration : {0:x}", regCode);
                Logger.Log("MetadataRegistration : {0:x}", regMeta);
            }

            // 5. Build metadata indices & type/method maps.
            var imgs = meta.imageDefs;
            var tds = meta.typeDefs;
            var mts = meta.methodDefs;
            var fields = meta.fieldDefs;
            var paramDefs = meta.parameterDefs;

            var imgNames = new string[imgs.Length];
            var tdToImg = new int[tds.Length];
            for (var ii = 0; ii < imgs.Length; ii++)
            {
                imgNames[ii] = meta.GetStringFromIndex(imgs[ii].nameIndex);
                var start = imgs[ii].typeStart;
                var end = Math.Min(tds.Length, start + (int)imgs[ii].typeCount);
                for (var ti = start; ti < end; ti++)
                {
                    tdToImg[ti] = ii;
                }
            }

            var bvToTd = new Dictionary<int, int>(tds.Length);
            for (var ti = 0; ti < tds.Length; ti++)
            {
                var bv = tds[ti].byvalTypeIndex;
                if (bv >= 0 && !bvToTd.ContainsKey(bv))
                {
                    bvToTd[bv] = ti;
                }
            }

            var isTdGen = new bool[tds.Length];
            for (var ti = 0; ti < tds.Length; ti++)
            {
                var cur = ti;
                while (cur >= 0)
                {
                    if (tds[cur].genericContainerIndex >= 0)
                    {
                        isTdGen[ti] = true;
                        break;
                    }
                    var dt = tds[cur].declaringTypeIndex;
                    cur = bvToTd.TryGetValue(dt, out var parentTd) ? parentTd : -1;
                }
            }

            // Collect per-image compiled non-generic non-abstract methods in metadata order, plus anchor dictionaries.
            var imgMethods = new List<(int tdIdx, int methodIdx)>[imgs.Length];
            var methodIdxToSeq = new int[mts.Length];
            Array.Fill(methodIdxToSeq, -1);
            for (var i = 0; i < imgs.Length; i++)
            {
                imgMethods[i] = new List<(int, int)>();
            }

            var icallGlobal = new Dictionary<string, List<(int imgIdx, int methodIdx)>>(StringComparer.Ordinal);
            var pinvGlobal = new Dictionary<string, List<(int imgIdx, int methodIdx)>>(StringComparer.Ordinal);
            var pchkGlobal = new Dictionary<string, List<(int imgIdx, int methodIdx)>>(StringComparer.Ordinal);
            var marshalGlobal = new Dictionary<string, List<(int imgIdx, int tdIdx)>>(StringComparer.Ordinal);
            var delegateMethodSet = new HashSet<int>();
            var delegateRawList = new List<(int imgIdx, int tdIdx, int ctorMi, string p0Key)>();
            var tdFirstSeq = new int[tds.Length];
            Array.Fill(tdFirstSeq, -1);
            var tdFullCache = new string[tds.Length];
            var tdSlashCache = new string[tds.Length];

            string GetTdFull(int ti, char sep)
            {
                var cache = sep == '/' ? tdSlashCache : tdFullCache;
                if (cache[ti] != null) return cache[ti];
                var td = tds[ti];
                var nm = meta.GetStringFromIndex(td.nameIndex);
                var dt = td.declaringTypeIndex;
                string res;
                if (dt >= 0 && bvToTd.TryGetValue(dt, out var enclosingTd))
                {
                    res = GetTdFull(enclosingTd, sep) + sep + nm;
                }
                else
                {
                    var ns = meta.GetStringFromIndex(td.namespaceIndex);
                    res = string.IsNullOrEmpty(ns) ? nm : ns + "." + nm;
                }
                cache[ti] = res;
                return res;
            }

            var tprivMap = new Dictionary<string, (int imgIdx, int tdIdx)>(StringComparer.Ordinal);
            var tprivAmbiguous = new HashSet<string>(StringComparer.Ordinal);

            void AddTprivHash(string fullTypeName, string imgNoExt, int ii, int ti)
            {
                var hash = Sha1Utf16LeHex(fullTypeName + ", " + imgNoExt);
                if (tprivAmbiguous.Contains(hash)) return;
                if (tprivMap.TryGetValue(hash, out var existing))
                {
                    if (existing.imgIdx != ii || existing.tdIdx != ti)
                    {
                        tprivMap.Remove(hash);
                        tprivAmbiguous.Add(hash);
                    }
                }
                else
                {
                    tprivMap[hash] = (ii, ti);
                }
            }

            for (var ti = 0; ti < tds.Length; ti++)
            {
                var td = tds[ti];
                var ii = tdToImg[ti];
                var imgNoExt = imgNames[ii].EndsWith(".dll", StringComparison.OrdinalIgnoreCase)
                    ? imgNames[ii][..^4]
                    : imgNames[ii];
                var fullSlash = GetTdFull(ti, '/');
                AddTprivHash(fullSlash, imgNoExt, ii, ti);
                if (td.declaringTypeIndex >= 0)
                {
                    var fullPlus = GetTdFull(ti, '+');
                    if (fullPlus != fullSlash)
                    {
                        AddTprivHash(fullPlus, imgNoExt, ii, ti);
                    }
                }

                var tdName = meta.GetStringFromIndex(td.nameIndex);
                var genT = isTdGen[ti];

                if (!genT && td.fieldStart >= 0 && td.field_count > 0)
                {
                    var fEnd = Math.Min(fields.Length, td.fieldStart + td.field_count);
                    for (var fi = td.fieldStart; fi < fEnd; fi++)
                    {
                        var fName = meta.GetStringFromIndex(fields[fi].nameIndex);
                        var key = $"Cannot marshal field '{fName}' of type '{tdName}'";
                        if (!marshalGlobal.TryGetValue(key, out var ml))
                        {
                            ml = new List<(int, int)>();
                            marshalGlobal[key] = ml;
                        }
                        ml.Add((ii, ti));
                    }
                }

                if (td.methodStart < 0 || td.method_count == 0) continue;
                var mEnd = Math.Min(mts.Length, td.methodStart + td.method_count);

                if (!genT && td.method_count >= 2 && td.method_count <= 4)
                {
                    var isDelegateTd = true;
                    var ctorMi = -1;
                    var invokeP0Key = string.Empty;
                    var hasInvoke = false;
                    for (var mi = td.methodStart; mi < mEnd; mi++)
                    {
                        var mt = mts[mi];
                        var mn = meta.GetStringFromIndex(mt.nameIndex);
                        if (mn == ".ctor" && mt.parameterCount == 2)
                        {
                            ctorMi = mi;
                        }
                        else if (mn == "Invoke")
                        {
                            hasInvoke = true;
                            if (mt.parameterStart >= 0 && mt.parameterCount > 0 && mt.parameterStart < paramDefs.Length)
                            {
                                invokeP0Key = $"___0_{meta.GetStringFromIndex(paramDefs[mt.parameterStart].nameIndex)}";
                            }
                        }
                        else if (mn != "BeginInvoke" && mn != "EndInvoke")
                        {
                            isDelegateTd = false;
                            break;
                        }
                    }
                    if (isDelegateTd && ctorMi >= 0 && hasInvoke)
                    {
                        for (var mi = td.methodStart; mi < mEnd; mi++)
                        {
                            delegateMethodSet.Add(mi);
                        }
                        if (!string.IsNullOrEmpty(invokeP0Key))
                        {
                            delegateRawList.Add((ii, ti, ctorMi, invokeP0Key));
                        }
                    }
                }

                for (var mi = td.methodStart; mi < mEnd; mi++)
                {
                    var mt = mts[mi];
                    if (genT || mt.genericContainerIndex >= 0 || (mt.flags & METHOD_ATTRIBUTE_ABSTRACT) != 0)
                    {
                        continue;
                    }
                    var seq = imgMethods[ii].Count;
                    imgMethods[ii].Add((ti, mi));
                    methodIdxToSeq[mi] = seq;

                    var mName = meta.GetStringFromIndex(mt.nameIndex);
                    if ((mt.iflags & 0x1000) != 0) // INTERNAL_CALL
                    {
                        var icallKey = $"{fullSlash}::{mName}(";
                        if (!icallGlobal.TryGetValue(icallKey, out var il))
                        {
                            il = new List<(int, int)>();
                            icallGlobal[icallKey] = il;
                        }
                        il.Add((ii, mi));
                    }
                    else if ((mt.flags & METHOD_ATTRIBUTE_PINVOKE_IMPL) != 0 && mName.Length >= 6)
                    {
                        if (!pinvGlobal.TryGetValue(mName, out var pl))
                        {
                            pl = new List<(int, int)>();
                            pinvGlobal[mName] = pl;
                        }
                        pl.Add((ii, mi));
                    }

                    if (mt.parameterStart >= 0 && mt.parameterCount > 0)
                    {
                        var pEnd = Math.Min(paramDefs.Length, mt.parameterStart + mt.parameterCount);
                        for (var pi = mt.parameterStart; pi < pEnd; pi++)
                        {
                            var pName = meta.GetStringFromIndex(paramDefs[pi].nameIndex);
                            var pchkKey = $"___{pi - mt.parameterStart}_{pName}";
                            if (!pchkGlobal.TryGetValue(pchkKey, out var kl))
                            {
                                kl = new List<(int, int)>();
                                pchkGlobal[pchkKey] = kl;
                            }
                            kl.Add((ii, mi));
                        }
                    }
                }
            }

            // Sort each image's compiled methods by metadata MethodDef RID to match compiler emission order
            // (resolves nested types interleaved differently in TypeDef order vs RID order).
            for (var ii = 0; ii < imgs.Length; ii++)
            {
                var list = imgMethods[ii];
                if (list.Count > 1)
                {
                    list.Sort((a, b) =>
                    {
                        var ra = mts[a.methodIdx].token & 0x00FFFFFFu;
                        var rb = mts[b.methodIdx].token & 0x00FFFFFFu;
                        var c = ra.CompareTo(rb);
                        return c != 0 ? c : a.methodIdx.CompareTo(b.methodIdx);
                    });
                }
                for (var seq = 0; seq < list.Count; seq++)
                {
                    var (ti, mi) = list[seq];
                    methodIdxToSeq[mi] = seq;
                    if (tdFirstSeq[ti] < 0) tdFirstSeq[ti] = seq;
                }
            }

            // Approximate TypeDef sequence position for methodless types (e.g., field-only marshal tags) from nearest siblings in the same image.
            var tdApproxSeq = new int[tds.Length];
            Array.Copy(tdFirstSeq, tdApproxSeq, tds.Length);
            for (var ii = 0; ii < imgs.Length; ii++)
            {
                var t0 = imgs[ii].typeStart;
                var t1 = Math.Min(tds.Length, t0 + (int)imgs[ii].typeCount);
                var prevArr = new int[Math.Max(0, t1 - t0)];
                var prev = -1;
                for (var ti = t0; ti < t1; ti++)
                {
                    if (tdFirstSeq[ti] >= 0) prev = tdFirstSeq[ti];
                    prevArr[ti - t0] = prev;
                }
                var next = -1;
                for (var ti = t1 - 1; ti >= t0; ti--)
                {
                    if (tdFirstSeq[ti] >= 0)
                    {
                        next = tdFirstSeq[ti];
                        continue;
                    }
                    var p = prevArr[ti - t0];
                    if (p >= 0 && next >= 0) tdApproxSeq[ti] = (p + next) / 2;
                    else if (p >= 0) tdApproxSeq[ti] = p;
                    else if (next >= 0) tdApproxSeq[ti] = next;
                }
            }

            var delegateP0Map = new Dictionary<string, List<DelegateInfo>>(delegateRawList.Count, StringComparer.Ordinal);
            foreach (var (dImg, dTd, dCtorMi, dP0Key) in delegateRawList)
            {
                var cSeq = methodIdxToSeq[dCtorMi];
                if (cSeq < 0) continue;
                if (!delegateP0Map.TryGetValue(dP0Key, out var dList))
                {
                    dList = new List<DelegateInfo>(2);
                    delegateP0Map[dP0Key] = dList;
                }
                dList.Add(new DelegateInfo(dImg, dTd, dCtorMi, cSeq));
            }

            // Ordinal ASCII sort key matches il2cpp compiler output order: (stem_no_dll + "_")
            var orderedImgs = Enumerable.Range(0, imgs.Length)
                .OrderBy(ii => (imgNames[ii].EndsWith(".dll", StringComparison.OrdinalIgnoreCase)
                    ? imgNames[ii][..^4]
                    : imgNames[ii]) + "_", StringComparer.Ordinal)
                .ToArray();
            var imgRank = new int[imgs.Length];
            for (var r = 0; r < orderedImgs.Length; r++)
            {
                imgRank[orderedImgs[r]] = r;
            }

            // 6. Single-pass scan of __cstring into global/local anchor maps.
            ScanCStringAnchors(
                cstrBytes, cstrVa, imgRank, tds, methodIdxToSeq, tdFirstSeq, tdApproxSeq,
                icallGlobal, pinvGlobal, pchkGlobal, marshalGlobal, tprivMap, delegateMethodSet,
                out var cstrGlobalMap, out var cstrGlobalPages,
                out var cstrMultiMap, out var cstrMultiPages,
                out var cstrLocalByImg, out var cstrLocalPagesByImg,
                out var marshalAllCstrs, out var marshalAnchors,
                out var p0CstrMap, out var p0CstrPages, out var delThisCstrVas,
                out var lStrVas, out var lStrPages);

            // 7. Pre-filter LC_FUNCTION_STARTS, resolve non-generic delegate .ctors, and exclude closed-generic delegate clusters
            //    before image window anchoring and slot partitioning.
            var allFuncsPreFiltered = PreFilterFunctionStarts(
                allFuncs, r0Set, objHdrSize, macho, textBytes, textVa, textSize,
                imgs.Length, imgRank, marshalAllCstrs, marshalAnchors,
                delegateP0Map, p0CstrMap, p0CstrPages, delThisCstrVas, lStrVas, lStrPages,
                out var marshalLocalByImg, out var funcGlobalAnchors, out var delMultiFuncMap,
                out var excludedClusterVas, out var funcSizesFiltered, out var hasExplicitAdjFiltered);

            // 8. Weighted LIS in Run[0] (+ bracket-disambiguated multi-image anchors) to obtain image anchor brackets.
            var anchorsByImg = FindWindowAnchorsWithFenwickLis(
                dense, lastCodeSlot, cgSlot, altMask, r2First,
                textBytes, textVa, orderedImgs.Length, cstrGlobalMap, cstrGlobalPages,
                cstrMultiMap, cstrMultiPages, funcGlobalAnchors, delMultiFuncMap);

            // 9. Convert image anchors + cgSlot + invokerEndSlot + method weights into VA windows per image.
            var invokerEndSlot = FindInvokerEndSlot(
                dense, cgSlot, lastCodeSlot, anchorsByImg, orderedImgs,
                textBytes, textVa, cstrVa, (ulong)cstrBytes.Length);
            var imgWindows = ComputeImageWindows(
                dense, lastCodeSlot, cgSlot, invokerEndSlot, r2First,
                orderedImgs, imgMethods, anchorsByImg, excludedClusterVas);

            // 10. Align methods inside each image window using filtered LC_FUNCTION_STARTS + local anchors.
            var recoveredModules = new Dictionary<string, Il2CppCodeGenModule>(imgs.Length, StringComparer.OrdinalIgnoreCase);
            var recoveredModuleMethodPointers = new Dictionary<string, ulong[]>(imgs.Length, StringComparer.OrdinalIgnoreCase);

            var vtInstArr = new bool[mts.Length];
            for (var ti = 0; ti < tds.Length; ti++)
            {
                var td = tds[ti];
                if (!td.IsValueType || td.IsEnum || td.methodStart < 0 || td.method_count == 0) continue;
                var mEnd = Math.Min(mts.Length, td.methodStart + td.method_count);
                for (var mi = td.methodStart; mi < mEnd; mi++)
                {
                    if ((mts[mi].flags & 0x0010) == 0) // !STATIC
                    {
                        vtInstArr[mi] = true;
                    }
                }
            }

            for (var r = 0; r < orderedImgs.Length; r++)
            {
                var ii = orderedImgs[r];
                var imgDef = imgs[ii];
                var imgName = imgNames[ii];
                var methodsSeq = imgMethods[ii];

                uint maxRid = 0;
                var typeEnd = Math.Min(tds.Length, imgDef.typeStart + (int)imgDef.typeCount);
                for (var ti = imgDef.typeStart; ti < typeEnd; ti++)
                {
                    var td = tds[ti];
                    if (td.methodStart < 0 || td.method_count == 0) continue;
                    var mEnd = Math.Min(mts.Length, td.methodStart + td.method_count);
                    for (var mi = td.methodStart; mi < mEnd; mi++)
                    {
                        var rid = mts[mi].token & 0x00FFFFFFu;
                        if (rid > maxRid) maxRid = rid;
                    }
                }

                var modPtrs = maxRid > 0 ? new ulong[maxRid] : Array.Empty<ulong>();
                recoveredModules[imgName] = new Il2CppCodeGenModule
                {
                    moduleName = 0,
                    methodPointerCount = modPtrs.Length
                };
                recoveredModuleMethodPointers[imgName] = modPtrs;

                if (methodsSeq.Count == 0 || modPtrs.Length == 0)
                {
                    continue;
                }

                var (vaStart, vaEnd) = imgWindows[r];
                if (vaStart == 0 || vaEnd <= vaStart)
                {
                    continue;
                }

                var fIdx0 = LowerBound(allFuncsPreFiltered, vaStart);
                var fIdx1 = LowerBound(allFuncsPreFiltered, vaEnd);
                var fCount = fIdx1 - fIdx0;
                if (fCount <= 0)
                {
                    continue;
                }

                var localCstrs = cstrLocalByImg[ii];
                var localPages = cstrLocalPagesByImg[ii];
                var marshalLocals = marshalLocalByImg[ii];
                var hits = new List<(int funcRelIdx, int seq)>();
                if ((localCstrs != null && localCstrs.Count > 0) || (marshalLocals != null && marshalLocals.Count > 0))
                {
                    var hasLocalCstrs = localCstrs != null && localCstrs.Count > 0;
                    var regs = new ulong[32];
                    var regValid = new bool[32];
                    for (var rel = 0; rel < fCount; rel++)
                    {
                        var va = allFuncsPreFiltered[fIdx0 + rel];
                        if (marshalLocals != null && marshalLocals.TryGetValue(va, out var marshalSeq))
                        {
                            hits.Add((rel, marshalSeq));
                        }
                        if (!hasLocalCstrs) continue;
                        var nextPos = LowerBound(allFuncs, va) + 1;
                        var nva = nextPos < allFuncs.Length ? allFuncs[nextPos] : textEnd;
                        var insCount = (int)Math.Min(128, Math.Max(1, (long)(nva - va) / 4));
                        var textOff = (int)(va - textVa);
                        if (textOff >= 0 && TryFindFirstPageAddTarget(
                            textBytes, textOff, insCount, va, localPages, null, localCstrs, regs, regValid,
                            out _, out var seq))
                        {
                            hits.Add((rel, seq));
                        }
                    }
                }

                // Decompose into primary + secondary piecewise-monotone chunks (handles split .cpp units like UIElementsModule).
                var chunks = ExtractMonotoneChunks(hits);
                FillMethodsFromChunks(
                    allFuncsPreFiltered, funcSizesFiltered, hasExplicitAdjFiltered,
                    fIdx0, fCount, methodsSeq, chunks, mts, vtInstArr, modPtrs,
                    textBytes, textVa, objHdrSize);
            }

            // 10. Recover Il2CppType[] and synthetic field offsets without hardcoded guesses.
            RecoverTypesAndFieldOffsets(
                macho, meta, objHdrSize, bvToTd,
                out var recoveredTypes, out var recoveredTypeDic, out var recoveredSyntheticStructs, out var recoveredFieldOffsets);

            // Extract Run[2] generic method pointers.
            var recoveredGenericMethodPointers = new ulong[run2.NonZeroCount];
            var gIdx = 0;
            for (var s = run2.StartSlot; s < run2.EndSlot && gIdx < recoveredGenericMethodPointers.Length; s++)
            {
                var v = ReadSectionU64(macho, run2.Section, s);
                if (v != 0)
                {
                    recoveredGenericMethodPointers[gIdx++] = v;
                }
            }

            macho.ApplySyntheticRecovery(
                hasObjectMonitor,
                recoveredGenericMethodPointers,
                recoveredTypes,
                recoveredTypeDic,
                recoveredSyntheticStructs,
                recoveredFieldOffsets,
                recoveredModules,
                recoveredModuleMethodPointers);

            macho.StringLiteralTableBase = RecoverStringTableBase(macho, meta, sectionInfos);

            return true;
        }

        private static ulong RecoverStringTableBase(
            Macho64 macho,
            Metadata meta,
            IReadOnlyList<MachoSectionInfo> sectionInfos)
        {
            try
            {
                int litIdx = -1;
                for (int i = 0; i < meta.stringLiterals.Length; i++)
                {
                    var s = meta.GetStringLiteralFromIndex((uint)i);
                    if (s.Contains("LegacyNetMsgRegister.RegisterAllNetMsgHandlers,msgCount="))
                    {
                        litIdx = i;
                        break;
                    }
                }

                if (litIdx >= 0)
                {
                    for (int imgIdx = 0; imgIdx < meta.imageDefs.Length; imgIdx++)
                    {
                        var img = meta.imageDefs[imgIdx];
                        var imgName = meta.GetStringFromIndex(img.nameIndex);

                        for (int tIdx = 0; tIdx < img.typeCount; tIdx++)
                        {
                            var typeDef = meta.typeDefs[img.typeStart + tIdx];
                            for (int mIdx = 0; mIdx < typeDef.method_count; mIdx++)
                            {
                                var def = meta.methodDefs[typeDef.methodStart + mIdx];
                                var name = meta.GetStringFromIndex(def.nameIndex);
                                if (name == "RegisterAllNetMsgHandlers")
                                {
                                    var ptr = macho.GetMethodPointer(imgName, def);
                                    if (ptr > 0)
                                    {
                                        macho.Position = macho.MapVATR(ptr);
                                        var instBytes = macho.ReadBytes(0x300);
                                        for (int p = 0; p < instBytes.Length - 8; p += 4)
                                        {
                                            uint inst1 = BitConverter.ToUInt32(instBytes, p);
                                            if ((inst1 & 0x9F000000) == 0x90000000) // ADRP
                                            {
                                                uint rd1 = inst1 & 0x1F;
                                                uint immlo = (inst1 >> 29) & 3;
                                                uint immhi = (inst1 >> 5) & 0x7FFFF;
                                                ulong imm = (immhi << 2) | immlo;
                                                if ((imm & 0x100000) != 0) imm |= 0xFFFFFFFFFFE00000UL;
                                                ulong pcPage = (ptr + (ulong)p) & ~0xFFFUL;
                                                ulong targetPage = pcPage + (imm << 12);

                                                uint inst2 = BitConverter.ToUInt32(instBytes, p + 4);
                                                if ((inst2 & 0xFFC00000) == 0xF9400000) // LDR
                                                {
                                                    uint rn2 = (inst2 >> 5) & 0x1F;
                                                    if (rn2 == rd1)
                                                    {
                                                        uint imm12 = ((inst2 >> 10) & 0xFFF) << 3;
                                                        ulong targetAddr = targetPage + imm12;
                                                        var baseAddr = targetAddr - (ulong)litIdx * 8;
                                                        Logger.Log($"String literal table base recovered: 0x{baseAddr:X} (via anchor method RegisterAllNetMsgHandlers)");
                                                        return baseAddr;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            catch (Exception ex)
            {
                Logger.Warning($"String literal base recovery failed: {ex.Message}");
            }

            if (TryGetSection(sectionInfos, "__DATA", "__bss", out var bssSec))
            {
                return bssSec.addr;
            }
            return 0;
        }

        private static void RecoverTypesAndFieldOffsets(
            Macho64 macho,
            Metadata meta,
            ulong objHdrSize,
            Dictionary<int, int> bvToTd,
            out Il2CppType[] recoveredTypes,
            out Dictionary<ulong, Il2CppType> recoveredTypeDic,
            out Dictionary<ulong, object> recoveredSyntheticStructs,
            out Dictionary<int, int[]> recoveredFieldOffsets)
        {
            var tds = meta.typeDefs;
            var fields = meta.fieldDefs;
            var mts = meta.methodDefs;
            var paramDefs = meta.parameterDefs;
            var events = meta.eventDefs;

            var maxTypeIdx = 0;
            void TrackMax(int tIdx)
            {
                if (tIdx > maxTypeIdx) maxTypeIdx = tIdx;
            }

            var minBv = int.MaxValue;
            foreach (var td in tds)
            {
                TrackMax(td.byvalTypeIndex);
                TrackMax(td.declaringTypeIndex);
                TrackMax(td.parentIndex);
                TrackMax(td.elementTypeIndex);
                if (td.byvalTypeIndex >= 0 && td.byvalTypeIndex < minBv)
                {
                    minBv = td.byvalTypeIndex;
                }
            }
            if (minBv == int.MaxValue) minBv = 0;

            foreach (var f in fields) TrackMax(f.typeIndex);
            foreach (var m in mts) TrackMax(m.returnType);
            foreach (var p in paramDefs) TrackMax(p.typeIndex);
            if (events != null) foreach (var e in events) TrackMax(e.typeIndex);
            if (meta.interfaceIndices != null) foreach (var t in meta.interfaceIndices) TrackMax(t);
            if (meta.constraintIndices != null) foreach (var t in meta.constraintIndices) TrackMax(t);
            if (meta.fieldRefs != null) foreach (var fr in meta.fieldRefs) TrackMax(fr.typeIndex);
            if (meta.parameterDefs != null)
            {
                for (var pi = 0; pi < meta.parameterDefs.Length; pi++)
                {
                    if (meta.GetParameterDefaultValueFromIndex(pi, out var pdv)) TrackMax(pdv.typeIndex);
                }
            }
            for (var fi = 0; fi < fields.Length; fi++)
            {
                if (meta.GetFieldDefaultValueFromIndex(fi, out var fdv)) TrackMax(fdv.typeIndex);
            }

            // Sorted (bv, tdIdx) for O(log N) typeIndex -> owning TypeDef resolution on [minBv .. maxTypeIdx].
            var bvList = new List<(int bv, int tdIdx)>(bvToTd.Count);
            foreach (var kv in bvToTd)
            {
                if (kv.Key >= 0) bvList.Add((kv.Key, kv.Value));
            }
            bvList.Sort((a, b) => a.bv.CompareTo(b.bv));
            var bvKeys = new int[bvList.Count];
            for (var i = 0; i < bvList.Count; i++) bvKeys[i] = bvList[i].bv;

            int ResolveTdFromTypeIdx(int typeIdx)
            {
                if (typeIdx < minBv || bvKeys.Length == 0) return -1;
                var pos = UpperBound(bvKeys, typeIdx) - 1;
                return pos >= 0 ? bvList[pos].tdIdx : -1;
            }

            // Identify per-slot const / static-class / static-cycle / non-const uses across all fields.
            var imgs = meta.imageDefs;
            var tdToImg = new int[tds.Length];
            for (var ii = 0; ii < imgs.Length; ii++)
            {
                var start = imgs[ii].typeStart;
                var end = Math.Min(tds.Length, start + (int)imgs[ii].typeCount);
                for (var t = start; t < end; t++) tdToImg[t] = ii;
            }
            var hasCctor = new bool[tds.Length];
            for (var ti = 0; ti < tds.Length; ti++)
            {
                var td = tds[ti];
                if (td.methodStart < 0 || td.method_count == 0) continue;
                var mEnd = Math.Min(mts.Length, td.methodStart + td.method_count);
                for (var mi = td.methodStart; mi < mEnd; mi++)
                {
                    if (meta.GetStringFromIndex(mts[mi].nameIndex) == ".cctor")
                    {
                        hasCctor[ti] = true;
                        break;
                    }
                }
            }

            var hasFieldDefUse = new bool[maxTypeIdx + 1];
            var hasParamDefUse = new bool[maxTypeIdx + 1];
            var hasParamDefaultUse = new bool[maxTypeIdx + 1];
            var hasParamNoDefaultUse = new bool[maxTypeIdx + 1];
            var hasFdvUse = new bool[maxTypeIdx + 1];
            var hasEnumConstUse = new bool[maxTypeIdx + 1];
            var hasEnumValueUse = new bool[maxTypeIdx + 1];
            var hasStaticClassUse = new bool[maxTypeIdx + 1];
            var hasSelfVtUse = new bool[maxTypeIdx + 1];
            var hasOtherFieldUse = new bool[maxTypeIdx + 1];
            var otherUseCount = new int[maxTypeIdx + 1];
            var otherCctorCount = new int[maxTypeIdx + 1];
            var otherFirstImg = new int[maxTypeIdx + 1];
            var otherSecondImg = new int[maxTypeIdx + 1];
            var otherImgMulti3 = new bool[maxTypeIdx + 1];
            Array.Fill(otherFirstImg, -1);
            Array.Fill(otherSecondImg, -1);

            static bool IsStaticClrClass(Il2CppTypeDefinition td) =>
                (td.flags & (TYPE_ATTRIBUTE_ABSTRACT | TYPE_ATTRIBUTE_SEALED)) == (TYPE_ATTRIBUTE_ABSTRACT | TYPE_ATTRIBUTE_SEALED) &&
                !td.IsValueType && !td.IsEnum && (td.flags & TYPE_ATTRIBUTE_INTERFACE) == 0;

            for (var ti = 0; ti < tds.Length; ti++)
            {
                var td = tds[ti];
                if (td.fieldStart < 0 || td.field_count == 0) continue;
                var fEnd = Math.Min(fields.Length, td.fieldStart + td.field_count);
                var isVt = td.IsValueType;
                var isEnum = td.IsEnum;
                var isStaticClass = IsStaticClrClass(td);
                var tdName = meta.GetStringFromIndex(td.nameIndex);
                var isCompilerClosure = tdName == "<>c" ||
                    (tdName.StartsWith("<>c__", StringComparison.Ordinal) && !tdName.Contains("DisplayClass", StringComparison.Ordinal));
                var ii = tdToImg[ti];

                for (var fi = td.fieldStart; fi < fEnd; fi++)
                {
                    var ft = fields[fi].typeIndex;
                    if (ft < 0 || ft > maxTypeIdx) continue;
                    hasFieldDefUse[ft] = true;
                    var fName = meta.GetStringFromIndex(fields[fi].nameIndex);
                    if (meta.GetFieldDefaultValueFromIndex(fi, out _))
                    {
                        hasFdvUse[ft] = true;
                        continue;
                    }
                    if (isEnum)
                    {
                        if (fName == "value__") hasEnumValueUse[ft] = true;
                        else hasEnumConstUse[ft] = true;
                        continue;
                    }
                    if (isStaticClass || (isCompilerClosure && (fName == "<>9" || fName.StartsWith("<>9__", StringComparison.Ordinal))))
                    {
                        hasStaticClassUse[ft] = true;
                        continue;
                    }
                    var rt = ResolveTdFromTypeIdx(ft);
                    if (isVt && rt == ti)
                    {
                        hasSelfVtUse[ft] = true;
                        continue;
                    }
                    hasOtherFieldUse[ft] = true;
                    otherUseCount[ft]++;
                    if (hasCctor[ti]) otherCctorCount[ft]++;
                    if (otherFirstImg[ft] < 0) otherFirstImg[ft] = ii;
                    else if (otherFirstImg[ft] != ii)
                    {
                        if (otherSecondImg[ft] < 0) otherSecondImg[ft] = ii;
                        else if (otherSecondImg[ft] != ii) otherImgMulti3[ft] = true;
                    }
                }
            }

            for (var pi = 0; pi < paramDefs.Length; pi++)
            {
                var pt = paramDefs[pi].typeIndex;
                if (pt < 0 || pt > maxTypeIdx) continue;
                hasParamDefUse[pt] = true;
                if (meta.GetParameterDefaultValueFromIndex(pi, out var pdv) && pdv.dataIndex != -1)
                    hasParamDefaultUse[pt] = true;
                else
                    hasParamNoDefaultUse[pt] = true;
            }

            // Detect multi-hop ValueType field cycles (only non-static instance cycles among ValueTypes)
            // Any edge inside an SCC of ValueTypes whose slot is not otherwise committed gets marked static.
            var vtOut = new Dictionary<int, List<int>>();
            for (var ti = 0; ti < tds.Length; ti++)
            {
                var td = tds[ti];
                if (!td.IsValueType || td.IsEnum || td.fieldStart < 0 || td.field_count == 0) continue;
                var fEnd = Math.Min(fields.Length, td.fieldStart + td.field_count);
                for (var fi = td.fieldStart; fi < fEnd; fi++)
                {
                    var ft = fields[fi].typeIndex;
                    if (ft < 0 || ft > maxTypeIdx || hasFdvUse[ft] || hasSelfVtUse[ft]) continue;
                    var rt = ResolveTdFromTypeIdx(ft);
                    if (rt >= 0 && rt != ti && tds[rt].IsValueType && !tds[rt].IsEnum)
                    {
                        if (!vtOut.TryGetValue(ti, out var list))
                        {
                            list = new List<int>();
                            vtOut[ti] = list;
                        }
                        list.Add(rt);
                    }
                }
            }

            var cycleVtPairs = FindValueTypeCycleEdges(tds.Length, vtOut);
            if (cycleVtPairs.Count > 0)
            {
                foreach (var (fromTi, toTi) in cycleVtPairs)
                {
                    var td = tds[fromTi];
                    var fEnd = Math.Min(fields.Length, td.fieldStart + td.field_count);
                    for (var fi = td.fieldStart; fi < fEnd; fi++)
                    {
                        var ft = fields[fi].typeIndex;
                        if (ft >= 0 && ft <= maxTypeIdx && ResolveTdFromTypeIdx(ft) == toTi && !hasFdvUse[ft])
                        {
                            // Mark only if not also used as an obviously non-cyclic instance field elsewhere or if needed to break cycle
                            if (!hasOtherFieldUse[ft])
                            {
                                hasSelfVtUse[ft] = true;
                            }
                        }
                    }
                }
            }

            // Determine static / literal status per field typeIndex.
            // Because IL2CPP interns Il2CppType by FieldAttributes, any non-const slot proven static via
            // CLR static class (abstract sealed) or ValueType self/cycle ref is statically typed for all users.
            var isLiteralSlot = new bool[maxTypeIdx + 1];
            var isStaticSlot = new bool[maxTypeIdx + 1];
            for (var t = 0; t <= maxTypeIdx; t++)
            {
                if ((hasFdvUse[t] || hasEnumConstUse[t]) && !hasEnumValueUse[t])
                {
                    isLiteralSlot[t] = true;
                    isStaticSlot[t] = true;
                }
                else if (hasStaticClassUse[t] ||
                         (hasSelfVtUse[t] && !hasEnumValueUse[t]) ||
                         (!hasEnumValueUse[t] && otherUseCount[t] >= 4 && otherCctorCount[t] == otherUseCount[t] && otherImgMulti3[t]))
                {
                    isStaticSlot[t] = true;
                }
            }

            // Construct synthetic Il2CppType[] across [0 .. maxTypeIdx].
            recoveredTypes = new Il2CppType[maxTypeIdx + 1];
            recoveredTypeDic = new Dictionary<ulong, Il2CppType>(maxTypeIdx + 1);
            recoveredSyntheticStructs = new Dictionary<ulong, object>();

            const uint PARAM_ATTRIBUTE_OPTIONAL = 0x0010;
            const uint PARAM_ATTRIBUTE_HAS_DEFAULT = 0x1000;

            for (var i = 0; i <= maxTypeIdx; i++)
            {
                var tdIdx = ResolveTdFromTypeIdx(i);
                var td = tdIdx >= 0 ? tds[tdIdx] : null;

                uint attrs = 0x0000;
                if (hasFieldDefUse[i])
                {
                    attrs = 0x0001; // PRIVATE default for fields
                    if (isLiteralSlot[i])
                    {
                        attrs = (uint)(0x8000 | FIELD_ATTRIBUTE_LITERAL | FIELD_ATTRIBUTE_STATIC | FIELD_ATTRIBUTE_PUBLIC);
                    }
                    else if (isStaticSlot[i])
                    {
                        attrs = (uint)(FIELD_ATTRIBUTE_STATIC | FIELD_ATTRIBUTE_PUBLIC);
                    }
                    else if (hasEnumValueUse[i] && !hasOtherFieldUse[i])
                    {
                        attrs = 0x0606; // Public | SpecialName | RTSpecialName
                    }
                }
                else if (hasParamDefaultUse[i] && !hasParamNoDefaultUse[i])
                {
                    attrs = PARAM_ATTRIBUTE_OPTIONAL | PARAM_ATTRIBUTE_HAS_DEFAULT;
                }

                var typeEnum = Il2CppTypeEnum.IL2CPP_TYPE_OBJECT;
                ulong datapoint = 0;

                if (tdIdx >= 0 && td != null)
                {
                    datapoint = (ulong)tdIdx;
                    var ns = meta.GetStringFromIndex(td.namespaceIndex);
                    var nm = meta.GetStringFromIndex(td.nameIndex);
                    if (ns == "System" && td.declaringTypeIndex < 0 && TryMapSystemPrimitive(nm, out var primType))
                    {
                        typeEnum = primType;
                        datapoint = 0;
                    }
                    else
                    {
                        typeEnum = td.IsValueType
                            ? Il2CppTypeEnum.IL2CPP_TYPE_VALUETYPE
                            : Il2CppTypeEnum.IL2CPP_TYPE_CLASS;
                    }
                }

                var bits = (attrs & 0xFFFFu) | (((uint)typeEnum & 0xFFu) << 16);
                var tObj = new Il2CppType
                {
                    datapoint = datapoint,
                    bits = bits
                };
                tObj.Init(macho.Version);
                recoveredTypes[i] = tObj;
                recoveredTypeDic[0x8000000000000000UL + (uint)i] = tObj;
            }

            // Resolve parentTypeDef index including generic parent instantiations (parentIndex < minBv) via vtableMethods.
            var resolvedParentTd = ResolveAllParentTypeDefs(meta, tds, mts, minBv, ResolveTdFromTypeIdx);

            // Recover composite, generic parameter, byref, pointer, and array types in [0 .. minBv - 1].
            RecoverSubMinBvTypes(
                macho, meta, minBv, maxTypeIdx, bvToTd, resolvedParentTd,
                hasFieldDefUse, hasParamDefUse,
                recoveredTypes, recoveredTypeDic, recoveredSyntheticStructs);

            // Compute ValueType sizes & alignments + class/struct instance & static field offsets.
            var sizeAlignCache = new (int size, int align)[tds.Length];
            var sizeAlignState = new byte[tds.Length]; // 0=unvisited, 1=visiting, 2=done

            (int size, int align) GetTypeDefSizeAlign(int ti)
            {
                if (ti < 0 || ti >= tds.Length) return (8, 8);
                if (sizeAlignState[ti] == 2) return sizeAlignCache[ti];
                if (sizeAlignState[ti] == 1) return (8, 8); // cycle guard

                sizeAlignState[ti] = 1;
                var td = tds[ti];
                var ns = meta.GetStringFromIndex(td.namespaceIndex);
                var nm = meta.GetStringFromIndex(td.nameIndex);

                if (ns == "System" && td.declaringTypeIndex < 0 && TryGetPrimitiveSizeAlign(nm, (int)macho.PointerSize, out var psz, out var pal))
                {
                    sizeAlignCache[ti] = (psz, pal);
                    sizeAlignState[ti] = 2;
                    return (psz, pal);
                }

                if (td.IsEnum)
                {
                    var res = (4, 4);
                    if (td.elementTypeIndex >= 0)
                    {
                        var ut = ResolveTdFromTypeIdx(td.elementTypeIndex);
                        if (ut >= 0 && ut != ti)
                        {
                            res = GetTypeDefSizeAlign(ut);
                        }
                    }
                    sizeAlignCache[ti] = res;
                    sizeAlignState[ti] = 2;
                    return res;
                }

                if (!td.IsValueType)
                {
                    var res = ((int)macho.PointerSize, (int)macho.PointerSize);
                    sizeAlignCache[ti] = res;
                    sizeAlignState[ti] = 2;
                    return res;
                }

                var pack = DecodePackingSize(td.bitfield);
                var off = 0;
                var maxAlign = 1;
                if (td.fieldStart >= 0 && td.field_count > 0)
                {
                    var fEnd = Math.Min(fields.Length, td.fieldStart + td.field_count);
                    for (var fi = td.fieldStart; fi < fEnd; fi++)
                    {
                        var ft = fields[fi].typeIndex;
                        if (ft < 0 || ft > maxTypeIdx) continue;
                        if (meta.GetFieldDefaultValueFromIndex(fi, out _) || isStaticSlot[ft] || isLiteralSlot[ft])
                        {
                            continue;
                        }
                        var ftd = ResolveTdFromTypeIdx(ft);
                        if (ftd == ti)
                        {
                            continue;
                        }
                        var (fsz, fal) = (ftd >= 0 && tds[ftd].IsValueType)
                            ? GetTypeDefSizeAlign(ftd)
                            : ((int)macho.PointerSize, (int)macho.PointerSize);
                        if (pack > 0 && fal > pack) fal = pack;
                        if (fal < 1) fal = 1;
                        off = (off + fal - 1) & ~(fal - 1);
                        off += fsz;
                        if (fal > maxAlign) maxAlign = fal;
                    }
                }

                if (off == 0) off = 1;
                var structAlign = pack > 0 ? Math.Min(maxAlign, pack) : maxAlign;
                if (structAlign < 1) structAlign = 1;
                off = (off + structAlign - 1) & ~(structAlign - 1);
                var result = (off, structAlign);
                sizeAlignCache[ti] = result;
                sizeAlignState[ti] = 2;
                return result;
            }

            (int size, int align) GetFieldSizeAlign(int typeIndex, int ownerTdIdx, bool isOwnerEnum)
            {
                if (typeIndex < 0 || typeIndex > maxTypeIdx) return ((int)macho.PointerSize, (int)macho.PointerSize);
                var ftd = ResolveTdFromTypeIdx(typeIndex);
                if (ftd < 0) return ((int)macho.PointerSize, (int)macho.PointerSize);
                if (!tds[ftd].IsValueType) return ((int)macho.PointerSize, (int)macho.PointerSize);
                if (ftd == ownerTdIdx && !isOwnerEnum) return ((int)macho.PointerSize, (int)macho.PointerSize);
                return GetTypeDefSizeAlign(ftd);
            }

            // Identify open generic type-parameter Singleton fields (e.g. MonoSingleton<T>._instance) whose staticness cannot be inferred via static classes.
            var isGenericSingletonClass = new bool[tds.Length];
            for (var ti = 0; ti < tds.Length; ti++)
            {
                var td = tds[ti];
                if (td.genericContainerIndex >= 0 && !td.IsValueType && (td.flags & TYPE_ATTRIBUTE_INTERFACE) == 0 && td.methodStart >= 0)
                {
                    var mEnd = Math.Min(mts.Length, td.methodStart + td.method_count);
                    for (var mi = td.methodStart; mi < mEnd; mi++)
                    {
                        if ((mts[mi].flags & 0x0010) != 0) // METHOD_ATTRIBUTE_STATIC
                        {
                            var mn = meta.GetStringFromIndex(mts[mi].nameIndex);
                            if (mn.Equals("get_Instance", StringComparison.OrdinalIgnoreCase) ||
                                mn.Equals("CreateInstance", StringComparison.OrdinalIgnoreCase))
                            {
                                isGenericSingletonClass[ti] = true;
                                break;
                            }
                        }
                    }
                    if (!isGenericSingletonClass[ti] &&
                        meta.GetStringFromIndex(td.nameIndex).IndexOf("Singleton", StringComparison.OrdinalIgnoreCase) >= 0)
                    {
                        isGenericSingletonClass[ti] = true;
                    }
                }
            }

            // Compute instance end offset (and individual instance offsets) for every TypeDef by walking parent chains.
            var fieldOffsetsMap = new Dictionary<int, int[]>(tds.Length);
            var instanceEndOffset = new int[tds.Length];
            var chainState = new byte[tds.Length];

            int ComputeTypeLayout(int ti)
            {
                if (chainState[ti] == 2) return instanceEndOffset[ti];
                if (chainState[ti] == 1) return (int)objHdrSize;
                chainState[ti] = 1;

                var td = tds[ti];
                var baseOffset = td.IsValueType ? 0 : (int)objHdrSize;
                if (!td.IsValueType && td.parentIndex >= 0)
                {
                    var pti = resolvedParentTd[ti];
                    if (pti >= 0 && pti != ti)
                    {
                        var pNs = meta.GetStringFromIndex(tds[pti].namespaceIndex);
                        var pNm = meta.GetStringFromIndex(tds[pti].nameIndex);
                        if (!(pNs == "System" && (pNm == "Object" || pNm == "ValueType" || pNm == "Enum")))
                        {
                            baseOffset = ComputeTypeLayout(pti);
                        }
                    }
                }

                var curOff = baseOffset;
                var staticOff = 0;
                var pack = DecodePackingSize(td.bitfield);
                var maxAlign = 1;
                var fOffsets = new int[td.field_count];

                if (td.fieldStart >= 0 && td.field_count > 0)
                {
                    for (var i = 0; i < td.field_count; i++)
                    {
                        var fi = td.fieldStart + i;
                        if (fi >= fields.Length)
                        {
                            fOffsets[i] = -1;
                            continue;
                        }
                        var ft = fields[fi].typeIndex;
                        var fName = meta.GetStringFromIndex(fields[fi].nameIndex);
                        var isConst = meta.GetFieldDefaultValueFromIndex(fi, out _) || (ft >= 0 && ft <= maxTypeIdx && isLiteralSlot[ft]);
                        var isGenericSingletonField = ft >= 0 && ft < minBv && isGenericSingletonClass[ti] &&
                            (fName.Contains("instance", StringComparison.OrdinalIgnoreCase) ||
                             fName.Contains("intance", StringComparison.OrdinalIgnoreCase));
                        var isStatic = !isConst && ((td.IsEnum && fName != "value__") ||
                                                    (ft >= 0 && ft <= maxTypeIdx && isStaticSlot[ft]) ||
                                                    (td.IsValueType && !td.IsEnum && ResolveTdFromTypeIdx(ft) == ti) ||
                                                    isGenericSingletonField);

                        if (isConst)
                        {
                            fOffsets[i] = -1;
                            continue;
                        }

                        var (fsz, fal) = GetFieldSizeAlign(ft, ti, td.IsEnum);
                        if (pack > 0 && fal > pack) fal = pack;
                        if (fal < 1) fal = 1;

                        if (isStatic)
                        {
                            staticOff = (staticOff + fal - 1) & ~(fal - 1);
                            fOffsets[i] = staticOff;
                            staticOff += fsz;
                        }
                        else
                        {
                            curOff = (curOff + fal - 1) & ~(fal - 1);
                            fOffsets[i] = curOff;
                            curOff += fsz;
                            if (fal > maxAlign) maxAlign = fal;
                        }
                    }
                }

                fieldOffsetsMap[ti] = fOffsets;
                instanceEndOffset[ti] = curOff;
                chainState[ti] = 2;
                return curOff;
            }

            for (var ti = 0; ti < tds.Length; ti++)
            {
                ComputeTypeLayout(ti);
            }
            recoveredFieldOffsets = fieldOffsetsMap;
        }

        private static void RecoverSubMinBvTypes(
            Macho64 macho,
            Metadata meta,
            int minBv,
            int maxTypeIdx,
            Dictionary<int, int> bvToTd,
            int[] resolvedParentTd,
            bool[] hasFieldDefUse,
            bool[] hasParamDefUse,
            Il2CppType[] recoveredTypes,
            Dictionary<ulong, Il2CppType> recoveredTypeDic,
            Dictionary<ulong, object> recoveredSyntheticStructs)
        {
            if (minBv <= 0 || minBv > recoveredTypes.Length) return;

            var tds = meta.typeDefs;
            var fields = meta.fieldDefs;
            var mts = meta.methodDefs;
            var paramDefs = meta.parameterDefs;
            var gcs = meta.genericContainers;
            var gps = meta.genericParameters;

            const ulong SYNTH_TYPE_BASE = 0x8000000000000000UL;
            var nextExtraTypePtr = 0x8800000000000000UL;
            var nextSynthStructPtr = 0x9000000000000000UL;
            var extraTypeCache = new Dictionary<(Il2CppTypeEnum te, ulong dp, uint attrs, bool byref), ulong>();

            ulong AllocStruct(object obj)
            {
                var p = nextSynthStructPtr++;
                recoveredSyntheticStructs[p] = obj;
                return p;
            }

            uint MakeBits(Il2CppTypeEnum te, uint attrs, bool byref)
            {
                var byrefBit = byref ? (macho.Version >= 27.2 ? (1u << 29) : (1u << 30)) : 0u;
                return (attrs & 0xFFFFu) | (((uint)te & 0xFFu) << 16) | byrefBit;
            }

            void SetSlot(int ti, Il2CppTypeEnum te, ulong dp, bool byref = false, uint? overrideAttrs = null)
            {
                if (ti < 0 || ti >= recoveredTypes.Length) return;
                var attrs = overrideAttrs ?? recoveredTypes[ti].attrs;
                var tObj = new Il2CppType
                {
                    datapoint = dp,
                    bits = MakeBits(te, attrs, byref)
                };
                tObj.Init(macho.Version);
                recoveredTypes[ti] = tObj;
                recoveredTypeDic[SYNTH_TYPE_BASE + (uint)ti] = tObj;
            }

            ulong AllocExtraType(Il2CppTypeEnum te, ulong dp, uint attrs = 0, bool byref = false)
            {
                var key = (te, dp, attrs, byref);
                if (extraTypeCache.TryGetValue(key, out var existing)) return existing;
                var p = nextExtraTypePtr++;
                var tObj = new Il2CppType
                {
                    datapoint = dp,
                    bits = MakeBits(te, attrs, byref)
                };
                tObj.Init(macho.Version);
                recoveredTypeDic[p] = tObj;
                extraTypeCache[key] = p;
                return p;
            }

            ulong GetTypePtrForTd(int tdIdx)
            {
                if (tdIdx >= 0 && tdIdx < tds.Length)
                {
                    var bv = tds[tdIdx].byvalTypeIndex;
                    if (bv >= 0 && bv < recoveredTypes.Length)
                        return SYNTH_TYPE_BASE + (uint)bv;
                }
                return AllocExtraType(Il2CppTypeEnum.IL2CPP_TYPE_OBJECT, 0);
            }

            var voidPtr = AllocExtraType(Il2CppTypeEnum.IL2CPP_TYPE_VOID, 0);
            var objectPtr = AllocExtraType(Il2CppTypeEnum.IL2CPP_TYPE_OBJECT, 0);

            // Fast lookup tables for TypeDefs & enclosing generic contexts
            var tdByFullName = new Dictionary<string, int>(tds.Length, StringComparer.Ordinal);
            var tdByNestedName = new Dictionary<string, int>(2048, StringComparer.Ordinal);
            var tdNames = new string[tds.Length];
            var tdNamespaces = new string[tds.Length];
            var enclosingGcOfTd = new int[tds.Length];
            for (var t = 0; t < tds.Length; t++)
            {
                tdNames[t] = meta.GetStringFromIndex(tds[t].nameIndex);
                tdNamespaces[t] = meta.GetStringFromIndex(tds[t].namespaceIndex);
                if (tds[t].declaringTypeIndex < 0)
                {
                    var full = string.IsNullOrEmpty(tdNamespaces[t]) ? tdNames[t] : $"{tdNamespaces[t]}.{tdNames[t]}";
                    tdByFullName.TryAdd(full, t);
                }
                enclosingGcOfTd[t] = tds[t].genericContainerIndex;
            }
            for (var t = 0; t < tds.Length; t++)
            {
                if (tds[t].declaringTypeIndex >= 0 && bvToTd.TryGetValue(tds[t].declaringTypeIndex, out var parentTd))
                {
                    var pNs = tdNamespaces[parentTd];
                    var pNm = tdNames[parentTd];
                    var outerFull = string.IsNullOrEmpty(pNs) ? pNm : $"{pNs}.{pNm}";
                    tdByNestedName.TryAdd($"{outerFull}+{tdNames[t]}", t);
                }
                // Walk declaring chain for genericContainerIndex inheritance
                if (enclosingGcOfTd[t] < 0)
                {
                    var cur = t;
                    var guard = 0;
                    while (cur >= 0 && tds[cur].declaringTypeIndex >= 0 && guard++ < 8)
                    {
                        if (!bvToTd.TryGetValue(tds[cur].declaringTypeIndex, out cur)) break;
                        if (tds[cur].genericContainerIndex >= 0)
                        {
                            enclosingGcOfTd[t] = tds[cur].genericContainerIndex;
                            break;
                        }
                    }
                }
            }

            int FindTd(string fullName) =>
                tdByFullName.TryGetValue(fullName, out var ti) ? ti :
                (tdByNestedName.TryGetValue(fullName, out var ni) ? ni : -1);

            // Usage records for [0 .. minBv - 1]
            var slotFieldTd = new int[minBv];
            var slotFieldIdx = new int[minBv];
            var slotFieldCount = new int[minBv];
            var slotParamUses = new List<(int td, int md, int pd)>[minBv];
            var slotRetUses = new List<(int td, int md)>[minBv];
            var slotParentTds = new List<int>[minBv];
            var slotIfaceTds = new List<int>[minBv];
            var slotHasPic = new bool[minBv];
            var slotHasEvent = new bool[minBv];
            var slotHasGenMethod = new bool[minBv];
            var slotHasNonGenMethodParam = new bool[minBv];
            var slotMdGcs = new HashSet<int>[minBv];
            var slotTdGcs = new HashSet<int>[minBv];
            Array.Fill(slotFieldTd, -1);
            Array.Fill(slotFieldIdx, -1);

            for (var t = 0; t < tds.Length; t++)
            {
                var td = tds[t];
                if (td.parentIndex >= 0 && td.parentIndex < minBv)
                {
                    slotHasPic[td.parentIndex] = true;
                    (slotParentTds[td.parentIndex] ??= new List<int>()).Add(t);
                }
                if (td.interfaces_count > 0 && meta.interfaceIndices != null)
                {
                    for (var k = 0; k < td.interfaces_count && td.interfacesStart + k < meta.interfaceIndices.Length; k++)
                    {
                        var it = meta.interfaceIndices[td.interfacesStart + k];
                        if (it >= 0 && it < minBv)
                        {
                            slotHasPic[it] = true;
                            (slotIfaceTds[it] ??= new List<int>()).Add(t);
                        }
                    }
                }
                if (td.event_count > 0 && meta.eventDefs != null)
                {
                    for (var k = 0; k < td.event_count && td.eventStart + k < meta.eventDefs.Length; k++)
                    {
                        var et = meta.eventDefs[td.eventStart + k].typeIndex;
                        if (et >= 0 && et < minBv) slotHasEvent[et] = true;
                    }
                }
                if (td.fieldStart >= 0 && td.field_count > 0)
                {
                    var fEnd = Math.Min(fields.Length, td.fieldStart + td.field_count);
                    for (var fi = td.fieldStart; fi < fEnd; fi++)
                    {
                        var ft = fields[fi].typeIndex;
                        if (ft < 0 || ft >= minBv) continue;
                        if (slotFieldCount[ft] == 0)
                        {
                            slotFieldTd[ft] = t;
                            slotFieldIdx[ft] = fi;
                        }
                        slotFieldCount[ft]++;
                        if (enclosingGcOfTd[t] >= 0) (slotTdGcs[ft] ??= new HashSet<int>()).Add(enclosingGcOfTd[t]);
                    }
                }
                if (td.methodStart >= 0 && td.method_count > 0)
                {
                    var mEnd = Math.Min(mts.Length, td.methodStart + td.method_count);
                    for (var mi = td.methodStart; mi < mEnd; mi++)
                    {
                        var md = mts[mi];
                        if (md.returnType >= 0 && md.returnType < minBv)
                        {
                            var rt = md.returnType;
                            (slotRetUses[rt] ??= new List<(int, int)>()).Add((t, mi));
                            if (md.genericContainerIndex >= 0)
                            {
                                slotHasGenMethod[rt] = true;
                                (slotMdGcs[rt] ??= new HashSet<int>()).Add(md.genericContainerIndex);
                            }
                            if (enclosingGcOfTd[t] >= 0) (slotTdGcs[rt] ??= new HashSet<int>()).Add(enclosingGcOfTd[t]);
                        }
                        if (md.parameterStart >= 0 && md.parameterCount > 0)
                        {
                            var pEnd = Math.Min(paramDefs.Length, md.parameterStart + md.parameterCount);
                            for (var pi = md.parameterStart; pi < pEnd; pi++)
                            {
                                var pt = paramDefs[pi].typeIndex;
                                if (pt < 0 || pt >= minBv) continue;
                                (slotParamUses[pt] ??= new List<(int, int, int)>()).Add((t, mi, pi));
                                if (md.genericContainerIndex >= 0)
                                {
                                    slotHasGenMethod[pt] = true;
                                    (slotMdGcs[pt] ??= new HashSet<int>()).Add(md.genericContainerIndex);
                                }
                                else if (enclosingGcOfTd[t] >= 0)
                                {
                                    slotHasNonGenMethodParam[pt] = true;
                                }
                                if (enclosingGcOfTd[t] >= 0) (slotTdGcs[pt] ??= new HashSet<int>()).Add(enclosingGcOfTd[t]);
                            }
                        }
                    }
                }
            }
            if (meta.constraintIndices != null)
            {
                foreach (var ci in meta.constraintIndices)
                {
                    if (ci >= 0 && ci < minBv) slotHasPic[ci] = true;
                }
            }

            // -------- 1. Dynamic Zone Boundary Detection --------
            var varStart = 0;
            for (var i = 0; i < minBv; i++)
            {
                if (hasFieldDefUse[i] || slotHasNonGenMethodParam[i])
                {
                    varStart = i;
                    break;
                }
            }

            var genInstStart = varStart;
            for (var i = varStart; i < minBv; i++)
            {
                var hits = 0;
                var winEnd = Math.Min(minBv - 1, i + 7);
                for (var k = i; k <= winEnd; k++)
                {
                    if (slotFieldIdx[k] >= 0 && meta.GetStringFromIndex(fields[slotFieldIdx[k]].nameIndex) == "<>9")
                        hits++;
                }
                if (hits >= 5)
                {
                    genInstStart = i;
                    break;
                }
            }

            // Longest zero-field, zero-PIC, zero-event run inside [genInstStart .. minBv - 1]
            int bestRunStart = genInstStart, bestRunEnd = genInstStart - 1, curRunStart = -1;
            for (var i = genInstStart; i < minBv; i++)
            {
                if (!hasFieldDefUse[i] && !slotHasPic[i] && !slotHasEvent[i])
                {
                    if (curRunStart < 0) curRunStart = i;
                }
                else
                {
                    if (curRunStart >= 0 && (i - 1 - curRunStart) > (bestRunEnd - bestRunStart))
                    {
                        bestRunStart = curRunStart;
                        bestRunEnd = i - 1;
                    }
                    curRunStart = -1;
                }
            }
            if (curRunStart >= 0 && (minBv - 1 - curRunStart) > (bestRunEnd - bestRunStart))
            {
                bestRunStart = curRunStart;
                bestRunEnd = minBv - 1;
            }

            var byrefStart = bestRunStart;
            for (var i = bestRunStart; i < Math.Min(minBv, bestRunStart + 40); i++)
            {
                if (slotHasGenMethod[i])
                {
                    byrefStart = i;
                    break;
                }
            }

            var ptrStart = Math.Min(minBv, bestRunEnd + 1);
            if (bestRunEnd - bestRunStart >= 500)
            {
                for (var i = Math.Max(byrefStart, bestRunEnd - 80); i <= Math.Min(minBv - 1, bestRunEnd); i++)
                {
                    if (!slotHasGenMethod[i]) continue;
                    var isPtrCues = false;
                    if (slotParamUses[i] != null)
                    {
                        foreach (var (tdi, mdi, pdi) in slotParamUses[i])
                        {
                            var tn = tdNames[tdi];
                            var mn = meta.GetStringFromIndex(mts[mdi].nameIndex);
                            var pn = meta.GetStringFromIndex(paramDefs[pdi].nameIndex);
                            if (tn == "AllocatorManager" || pn == "pointer" || mn.Contains("Ptr", StringComparison.Ordinal))
                            {
                                isPtrCues = true;
                                break;
                            }
                        }
                    }
                    if (!isPtrCues && slotRetUses[i] != null)
                    {
                        foreach (var (tdi, mdi) in slotRetUses[i])
                        {
                            var mn = meta.GetStringFromIndex(mts[mdi].nameIndex);
                            if (tdNames[tdi] == "AllocatorManager" || mn.Contains("Ptr", StringComparison.Ordinal))
                            {
                                isPtrCues = true;
                                break;
                            }
                        }
                    }
                    if (isPtrCues)
                    {
                        ptrStart = i;
                        break;
                    }
                }
            }

            // Locate Byte[] via BitConverter.GetBytes to cap the PTR->SZARRAY search window
            var byteTdIdx = FindTd("System.Byte");
            var byteArrProbe = -1;
            var bcTdIdx = FindTd("System.BitConverter");
            if (bcTdIdx >= 0 && tds[bcTdIdx].methodStart >= 0)
            {
                var mEnd = Math.Min(mts.Length, tds[bcTdIdx].methodStart + tds[bcTdIdx].method_count);
                for (var mi = tds[bcTdIdx].methodStart; mi < mEnd; mi++)
                {
                    if (meta.GetStringFromIndex(mts[mi].nameIndex) == "GetBytes" && mts[mi].returnType >= ptrStart && mts[mi].returnType < minBv)
                    {
                        byteArrProbe = mts[mi].returnType;
                        break;
                    }
                }
            }

            var szLimit = (byteArrProbe > ptrStart && byteArrProbe < ptrStart + 1500)
                ? byteArrProbe
                : Math.Min(minBv, ptrStart + 600);
            var sysArrayTd = FindTd("System.Array");
            var unityAnimatorTd = FindTd("UnityEngine.Animator");
            var szarrayStart = szLimit;
            for (var i = ptrStart; i < szLimit; i++)
            {
                if (!slotHasGenMethod[i]) continue;
                var arrHits = 0;
                var wEnd = Math.Min(szLimit - 1, i + 15);
                for (var k = i; k <= wEnd; k++)
                {
                    if (!slotHasGenMethod[k]) continue;
                    var matchedArr = false;
                    if (slotParamUses[k] != null)
                    {
                        foreach (var (tdi, _, _) in slotParamUses[k])
                            if ((sysArrayTd >= 0 && tdi == sysArrayTd) || (unityAnimatorTd >= 0 && tdi == unityAnimatorTd)) { matchedArr = true; break; }
                    }
                    if (!matchedArr && slotRetUses[k] != null)
                    {
                        foreach (var (tdi, _) in slotRetUses[k])
                            if ((sysArrayTd >= 0 && tdi == sysArrayTd) || (unityAnimatorTd >= 0 && tdi == unityAnimatorTd)) { matchedArr = true; break; }
                    }
                    if (matchedArr) arrHits++;
                }
                if (arrHits >= 6)
                {
                    // Step back over leading MVAR[] slots (e.g. Animator/ArgHelper) to just after last concrete PTR slot
                    var s = i;
                    while (s > ptrStart && slotHasGenMethod[s - 1]) s--;
                    szarrayStart = s;
                    break;
                }
            }

            var arrayStart = minBv;
            for (var i = Math.Max(szarrayStart, minBv - 120); i < minBv; i++)
            {
                var hit = false;
                if (slotParamUses[i] != null)
                {
                    foreach (var (tdi, _, _) in slotParamUses[i])
                        if (tdNames[tdi] == "MultiDimArrayUtilities" || tdNames[tdi].Contains("2D`", StringComparison.Ordinal))
                        { hit = true; break; }
                }
                if (hit)
                {
                    arrayStart = i;
                    // Include immediately preceding Extensions.SetValues(array) slot if present
                    if (arrayStart > szarrayStart && slotParamUses[arrayStart - 1] != null &&
                        slotParamUses[arrayStart - 1].Any(u => meta.GetStringFromIndex(mts[u.md].nameIndex) == "SetValues"))
                    {
                        arrayStart--;
                    }
                    break;
                }
            }

            // -------- 2. Zone 1 & 2: MVAR & VAR ([0 .. genInstStart - 1]) --------
            var resolvedGpSlot = new int[genInstStart];
            var resolvedIsMvar = new bool[genInstStart];
            Array.Fill(resolvedGpSlot, -1);

            bool DoesTdOwnGc(int tdIdx, int targetGc)
            {
                var cur = tdIdx;
                var guard = 0;
                while (cur >= 0 && guard++ < 8)
                {
                    if (tds[cur].genericContainerIndex == targetGc) return true;
                    if (tds[cur].declaringTypeIndex < 0 || !bvToTd.TryGetValue(tds[cur].declaringTypeIndex, out cur)) break;
                }
                return false;
            }

            var gpSlotListByGc = new Dictionary<int, List<int>>();
            for (var i = 0; i < genInstStart; i++)
            {
                var mdGcs = slotMdGcs[i];
                var tdGcs = slotTdGcs[i];
                var hasF = hasFieldDefUse[i];
                var hasNonGmP = slotHasNonGenMethodParam[i];

                var pickMvar = false;
                var pickedGc = -1;

                if (!hasF && !hasNonGmP && mdGcs != null && mdGcs.Count == 1 && (i < varStart || tdGcs == null || tdGcs.Count == 0))
                {
                    pickMvar = true;
                    pickedGc = mdGcs.First();
                }
                else if ((hasF || hasNonGmP || mdGcs == null || mdGcs.Count == 0) && tdGcs != null && tdGcs.Count == 1)
                {
                    var gcCandidate = tdGcs.First();
                    // Verify all param/ret/field users belong cleanly to this declaring generic container chain
                    var allMatch = true;
                    if (slotParamUses[i] != null)
                        foreach (var (tdi, _, _) in slotParamUses[i]) if (!DoesTdOwnGc(tdi, gcCandidate)) { allMatch = false; break; }
                    if (allMatch && slotRetUses[i] != null)
                        foreach (var (tdi, _) in slotRetUses[i]) if (!DoesTdOwnGc(tdi, gcCandidate)) { allMatch = false; break; }
                    if (allMatch)
                    {
                        pickMvar = false;
                        pickedGc = gcCandidate;
                    }
                }
                else if (mdGcs != null && mdGcs.Count == 1 && tdGcs != null && tdGcs.Count == 1 && !hasF && !hasNonGmP)
                {
                    // Generic method inside a generic class with no field/non-gm usage: only assign if all usages share the exact same method gc
                    pickMvar = true;
                    pickedGc = mdGcs.First();
                }

                if (pickedGc >= 0 && pickedGc < gcs.Length)
                {
                    // Ensure all users are compatible if MVAR
                    var ok = true;
                    if (pickMvar)
                    {
                        if (slotParamUses[i] != null)
                            foreach (var (_, mdi, _) in slotParamUses[i]) if (mts[mdi].genericContainerIndex != pickedGc) { ok = false; break; }
                        if (ok && slotRetUses[i] != null)
                            foreach (var (_, mdi) in slotRetUses[i]) if (mts[mdi].genericContainerIndex != pickedGc) { ok = false; break; }
                    }
                    if (ok)
                    {
                        resolvedIsMvar[i] = pickMvar;
                        if (!gpSlotListByGc.TryGetValue(pickedGc, out var list))
                        {
                            list = new List<int>();
                            gpSlotListByGc[pickedGc] = list;
                        }
                        list.Add(i);
                    }
                }
            }

            foreach (var (gcIdx, slotList) in gpSlotListByGc)
            {
                var gc = gcs[gcIdx];
                if (gc.type_argc <= 0 || gc.genericParameterStart < 0 || gc.genericParameterStart + gc.type_argc > gps.Length) continue;
                slotList.Sort();
                if (gc.type_argc == 1)
                {
                    foreach (var s in slotList)
                    {
                        resolvedGpSlot[s] = gc.genericParameterStart;
                        SetSlot(s, resolvedIsMvar[s] ? Il2CppTypeEnum.IL2CPP_TYPE_MVAR : Il2CppTypeEnum.IL2CPP_TYPE_VAR, (ulong)gc.genericParameterStart);
                    }
                }
                else
                {
                    // Multi-parameter generic container: try name match first, then monotonic ordinal fallback
                    var gpNames = new string[gc.type_argc];
                    for (var p = 0; p < gc.type_argc; p++)
                        gpNames[p] = meta.GetStringFromIndex(gps[gc.genericParameterStart + p].nameIndex);

                    for (var k = 0; k < slotList.Count; k++)
                    {
                        var s = slotList[k];
                        var matchedPos = -1;
                        if (slotParamUses[s] != null && slotParamUses[s].Count > 0)
                        {
                            var (_, mdi, pdi) = slotParamUses[s][0];
                            var pn = meta.GetStringFromIndex(paramDefs[pdi].nameIndex);
                            if (pn.StartsWith("arg", StringComparison.Ordinal) && int.TryParse(pn.AsSpan(3), out var argNum) &&
                                argNum >= 1 && argNum <= gc.type_argc)
                            {
                                matchedPos = argNum - 1;
                            }
                            else
                            {
                                for (var p = 0; p < gc.type_argc; p++)
                                {
                                    if (string.Equals(gpNames[p], pn, StringComparison.OrdinalIgnoreCase) ||
                                        gpNames[p].StartsWith($"<{pn}>", StringComparison.OrdinalIgnoreCase))
                                    {
                                        matchedPos = p;
                                        break;
                                    }
                                }
                            }
                            if (matchedPos < 0 && mts[mdi].nameIndex >= 0 && tdNames[slotParamUses[s][0].td].StartsWith("Func`", StringComparison.Ordinal))
                                matchedPos = Math.Min(gc.type_argc - 1, pdi - mts[mdi].parameterStart);
                        }
                        if (matchedPos < 0 && slotRetUses[s] != null && slotRetUses[s].Count > 0)
                        {
                            var lastName = gpNames[gc.type_argc - 1];
                            if (lastName.Contains("Result", StringComparison.OrdinalIgnoreCase) ||
                                lastName.Contains("Ret", StringComparison.OrdinalIgnoreCase) ||
                                lastName.Contains("Out", StringComparison.OrdinalIgnoreCase))
                            {
                                matchedPos = gc.type_argc - 1;
                            }
                        }
                        if (matchedPos < 0)
                        {
                            matchedPos = slotList.Count <= gc.type_argc ? k : Math.Min(gc.type_argc - 1, (k * gc.type_argc) / slotList.Count);
                        }
                        var gpIdx = gc.genericParameterStart + matchedPos;
                        resolvedGpSlot[s] = gpIdx;
                        SetSlot(s, resolvedIsMvar[s] ? Il2CppTypeEnum.IL2CPP_TYPE_MVAR : Il2CppTypeEnum.IL2CPP_TYPE_VAR, (ulong)gpIdx);
                    }
                }
            }

            // -------- Helper to match BCL/Unity methods & fields --------
            int? FindMethodRetInRange(string fullTypeName, string methodName, int? paramCount, int lo, int hi)
            {
                var tdIdx = FindTd(fullTypeName);
                if (tdIdx < 0 || tds[tdIdx].methodStart < 0) return null;
                var mEnd = Math.Min(mts.Length, tds[tdIdx].methodStart + tds[tdIdx].method_count);
                for (var mi = tds[tdIdx].methodStart; mi < mEnd; mi++)
                {
                    var md = mts[mi];
                    if (meta.GetStringFromIndex(md.nameIndex) != methodName) continue;
                    if (paramCount.HasValue && md.parameterCount != paramCount.Value) continue;
                    if (md.returnType >= lo && md.returnType <= hi) return md.returnType;
                }
                return null;
            }

            int? FindMethodParamInRange(string fullTypeName, string methodName, int? paramCount, int paramPos, int lo, int hi)
            {
                var tdIdx = FindTd(fullTypeName);
                if (tdIdx < 0 || tds[tdIdx].methodStart < 0) return null;
                var mEnd = Math.Min(mts.Length, tds[tdIdx].methodStart + tds[tdIdx].method_count);
                for (var mi = tds[tdIdx].methodStart; mi < mEnd; mi++)
                {
                    var md = mts[mi];
                    if (meta.GetStringFromIndex(md.nameIndex) != methodName) continue;
                    if (paramCount.HasValue && md.parameterCount != paramCount.Value) continue;
                    if (paramPos < md.parameterCount && md.parameterStart + paramPos < paramDefs.Length)
                    {
                        var pt = paramDefs[md.parameterStart + paramPos].typeIndex;
                        if (pt >= lo && pt <= hi) return pt;
                    }
                }
                return null;
            }

            int? FindFieldTypeInRange(string fullTypeName, string fieldName, int lo, int hi)
            {
                var tdIdx = FindTd(fullTypeName);
                if (tdIdx < 0 || tds[tdIdx].fieldStart < 0) return null;
                var fEnd = Math.Min(fields.Length, tds[tdIdx].fieldStart + tds[tdIdx].field_count);
                for (var fi = tds[tdIdx].fieldStart; fi < fEnd; fi++)
                {
                    if (meta.GetStringFromIndex(fields[fi].nameIndex) == fieldName && fields[fi].typeIndex >= lo && fields[fi].typeIndex <= hi)
                        return fields[fi].typeIndex;
                }
                return null;
            }

            // -------- 3. Zone 6: SZARRAY ([szarrayStart .. arrayStart - 1]) --------
            var szAnchors = new Dictionary<int, int>(); // slot -> elemTdIdx
            void AnchorSzRet(string ftn, string mn, int? pc, string elemFullName)
            {
                var eTd = FindTd(elemFullName);
                var slot = FindMethodRetInRange(ftn, mn, pc, szarrayStart, arrayStart - 1);
                if (eTd >= 0 && slot.HasValue) szAnchors.TryAdd(slot.Value, eTd);
            }
            void AnchorSzParam(string ftn, string mn, int? pc, int pIdx, string elemFullName)
            {
                var eTd = FindTd(elemFullName);
                var slot = FindMethodParamInRange(ftn, mn, pc, pIdx, szarrayStart, arrayStart - 1);
                if (eTd >= 0 && slot.HasValue) szAnchors.TryAdd(slot.Value, eTd);
            }
            void AnchorSzField(string ftn, string fn, string elemFullName)
            {
                var eTd = FindTd(elemFullName);
                var slot = FindFieldTypeInRange(ftn, fn, szarrayStart, arrayStart - 1);
                if (eTd >= 0 && slot.HasValue) szAnchors.TryAdd(slot.Value, eTd);
            }

            AnchorSzRet("System.AppDomain", "GetAssemblies", 0, "System.Reflection.Assembly");
            AnchorSzRet("System.Reflection.Assembly", "GetReferencedAssemblies", 0, "System.Reflection.AssemblyName");
            AnchorSzRet("System.Reflection.Assembly", "GetTypes", 0, "System.Type");
            AnchorSzRet("System.Reflection.Assembly", "GetModules", 1, "System.Reflection.Module");
            AnchorSzRet("System.Type", "GetMethods", 0, "System.Reflection.MethodInfo");
            AnchorSzRet("System.Type", "GetFields", 0, "System.Reflection.FieldInfo");
            AnchorSzRet("System.Type", "GetProperties", 0, "System.Reflection.PropertyInfo");
            AnchorSzRet("System.Type", "GetConstructors", 0, "System.Reflection.ConstructorInfo");
            AnchorSzRet("System.Type", "GetEvents", 0, "System.Reflection.EventInfo");
            AnchorSzRet("System.Type", "GetMembers", 0, "System.Reflection.MemberInfo");
            AnchorSzRet("System.Type", "GetInterfaces", 0, "System.Type");
            AnchorSzRet("System.Type", "GetGenericArguments", 0, "System.Type");
            AnchorSzRet("System.Reflection.MethodBase", "GetParameters", 0, "System.Reflection.ParameterInfo");
            AnchorSzRet("System.Reflection.MemberInfo", "GetCustomAttributes", 1, "System.Object");
            AnchorSzRet("System.Diagnostics.StackTrace", "GetFrames", 0, "System.Diagnostics.StackFrame");
            AnchorSzRet("System.Net.Dns", "GetHostAddresses", 1, "System.Net.IPAddress");
            AnchorSzRet("System.Decimal", "GetBits", 1, "System.Int32");
            AnchorSzRet("System.BitConverter", "GetBytes", 1, "System.Byte");
            AnchorSzRet("System.Text.Encoding", "GetBytes", 1, "System.Byte");
            AnchorSzRet("System.Text.Encoding", "GetChars", 1, "System.Char");
            AnchorSzRet("System.String", "ToCharArray", 0, "System.Char");
            AnchorSzRet("System.String", "Split", 1, "System.String");
            AnchorSzParam("System.String", "Split", 1, 0, "System.Char");
            AnchorSzParam("System.String", "Join", 2, 1, "System.String");
            AnchorSzParam("System.ParamsArray", ".ctor", 1, 0, "System.Object");
            AnchorSzField("System.ParamsArray", "s_oneArgArray", "System.Object");
            AnchorSzRet("System.IO.BinaryReader", "ReadBytes", 1, "System.Byte");
            AnchorSzRet("System.IO.BinaryReader", "ReadChars", 1, "System.Char");
            AnchorSzParam("System.IO.MonoIO", "Write", 5, 1, "System.Byte");
            AnchorSzField("System.Collections.Generic.Dictionary`2", "_buckets", "System.Int32");
            AnchorSzField("System.Xml.Serialization.XmlMembersMapping", "_mapping", "System.Xml.Serialization.XmlMemberMapping");
            AnchorSzField("System.TimeZoneInfo", "_adjustmentRules", "System.TimeZoneInfo+AdjustmentRule");
            AnchorSzRet("System.TimeZoneInfo", "GetAdjustmentRules", 0, "System.TimeZoneInfo+AdjustmentRule");
            AnchorSzRet("UnityEngine.Camera", "get_allCameras", 0, "UnityEngine.Camera");
            AnchorSzRet("UnityEngine.GameObject", "GetComponents", 1, "UnityEngine.Component");
            AnchorSzRet("UnityEngine.SkinnedMeshRenderer", "get_bones", 0, "UnityEngine.Transform");
            AnchorSzRet("UnityEngine.Renderer", "get_materials", 0, "UnityEngine.Material");
            AnchorSzRet("UnityEngine.Renderer", "get_sharedMaterials", 0, "UnityEngine.Material");
            AnchorSzRet("UnityEngine.Physics", "OverlapSphere", 2, "UnityEngine.Collider");
            AnchorSzRet("UnityEngine.Physics2D", "RaycastAll", 2, "UnityEngine.RaycastHit2D");
            AnchorSzRet("UnityEngine.Physics2D", "OverlapPointAll", 1, "UnityEngine.Collider2D");
            AnchorSzRet("UnityEngine.RuntimeAnimatorController", "get_animationClips", 0, "UnityEngine.AnimationClip");
            AnchorSzRet("UnityEngine.Animator", "get_parameters", 0, "UnityEngine.AnimatorControllerParameter");
            AnchorSzRet("UnityEngine.Animator", "GetCurrentAnimatorClipInfo", 1, "UnityEngine.AnimatorClipInfo");
            AnchorSzRet("UnityEngine.Screen", "get_resolutions", 0, "UnityEngine.Resolution");
            AnchorSzRet("UnityEngine.Input", "get_touches", 0, "UnityEngine.Touch");
            AnchorSzRet("UnityEngine.Terrain", "get_activeTerrains", 0, "UnityEngine.Terrain");
            AnchorSzRet("UnityEngine.Collision", "get_contacts", 0, "UnityEngine.ContactPoint");
            AnchorSzRet("UnityEngine.TextGenerator", "GetVerticesArray", 0, "UnityEngine.UIVertex");
            AnchorSzRet("UnityEngine.TextGenerator", "GetCharactersArray", 0, "UnityEngine.UICharInfo");
            AnchorSzRet("UnityEngine.TextGenerator", "GetLinesArray", 0, "UnityEngine.UILineInfo");
            AnchorSzRet("UnityEngine.Mesh", "get_vertices", 0, "UnityEngine.Vector3");
            AnchorSzRet("UnityEngine.Mesh", "get_normals", 0, "UnityEngine.Vector3");
            AnchorSzRet("UnityEngine.Mesh", "get_uv", 0, "UnityEngine.Vector2");
            AnchorSzRet("UnityEngine.Mesh", "get_colors", 0, "UnityEngine.Color");
            AnchorSzRet("UnityEngine.Mesh", "get_colors32", 0, "UnityEngine.Color32");
            AnchorSzRet("UnityEngine.Mesh", "get_triangles", 0, "System.Int32");
            AnchorSzRet("UnityEngine.Mesh", "get_tangents", 0, "UnityEngine.Vector4");
            AnchorSzRet("UnityEngine.Mesh", "get_boneWeights", 0, "UnityEngine.BoneWeight");
            AnchorSzRet("UnityEngine.Mesh", "get_bindposes", 0, "UnityEngine.Matrix4x4");
            AnchorSzRet("UnityEngine.Texture2D", "GetPixels", 0, "UnityEngine.Color");
            AnchorSzRet("UnityEngine.Texture2D", "GetPixels32", 0, "UnityEngine.Color32");
            AnchorSzRet("UnityEngine.Physics", "RaycastAll", 1, "UnityEngine.RaycastHit");
            AnchorSzRet("UnityEngine.AnimationCurve", "get_keys", 0, "UnityEngine.Keyframe");
            AnchorSzRet("UnityEngine.Gradient", "get_colorKeys", 0, "UnityEngine.GradientColorKey");
            AnchorSzRet("UnityEngine.Gradient", "get_alphaKeys", 0, "UnityEngine.GradientAlphaKey");
            AnchorSzRet("UnityEngine.GUIContent", "Temp", 1, "UnityEngine.GUIContent");
            AnchorSzParam("UnityEngine.AudioClip", "GetData", 2, 0, "System.Single");
            AnchorSzParam("UnityEngine.Mathf", "Max", 1, 0, "System.Single");
            AnchorSzParam("UnityEngine.Mathf", "Min", 1, 0, "System.Single");

            // Match Marshal.Copy 4-arg overloads (byte[], char[], short[], int[], long[], IntPtr[])
            var marshalTd = FindTd("System.Runtime.InteropServices.Marshal");
            if (marshalTd >= 0 && tds[marshalTd].methodStart >= 0)
            {
                var copySlots = new SortedSet<int>();
                var mEnd = Math.Min(mts.Length, tds[marshalTd].methodStart + tds[marshalTd].method_count);
                for (var mi = tds[marshalTd].methodStart; mi < mEnd; mi++)
                {
                    var md = mts[mi];
                    if (meta.GetStringFromIndex(md.nameIndex) != "Copy" || md.parameterCount != 4) continue;
                    var p0 = paramDefs[md.parameterStart].typeIndex;
                    var p1 = paramDefs[md.parameterStart + 1].typeIndex;
                    if (p0 >= szarrayStart && p0 < arrayStart) copySlots.Add(p0);
                    if (p1 >= szarrayStart && p1 < arrayStart) copySlots.Add(p1);
                }
                var i16Td = FindTd("System.Int16");
                var i64Td = FindTd("System.Int64");
                var iptrTd = FindTd("System.IntPtr");
                var i32Slot = szAnchors.FirstOrDefault(kv => kv.Value == FindTd("System.Int32")).Key;
                foreach (var cs in copySlots)
                {
                    if (szAnchors.ContainsKey(cs)) continue;
                    if (i16Td >= 0 && szAnchors.Any(kv => kv.Value == FindTd("System.Char") && cs > kv.Key) &&
                        i32Slot > 0 && cs < i32Slot)
                    {
                        szAnchors.TryAdd(cs, i16Td);
                    }
                }
                var remAfterI32 = copySlots.Where(cs => !szAnchors.ContainsKey(cs) && cs > i32Slot &&
                    (!szAnchors.Any(kv => kv.Value == FindTd("System.Object") && cs >= kv.Key))).ToList();
                if (remAfterI32.Count == 2 && i64Td >= 0 && iptrTd >= 0)
                {
                    szAnchors.TryAdd(remAfterI32[0], i64Td);
                    szAnchors.TryAdd(remAfterI32[1], iptrTd);
                }
            }

            // Shared ASCII-windowed concrete TypeDef stem matcher for canonically sorted SZARRAY / BYREF zones
            var topTdsByName = new Dictionary<string, List<int>>(StringComparer.OrdinalIgnoreCase);
            for (var t = 0; t < tds.Length; t++)
            {
                if (tds[t].declaringTypeIndex >= 0 || tds[t].genericContainerIndex >= 0 || tds[t].byvalTypeIndex < 0) continue;
                var nm = tdNames[t];
                if (nm.Length < 3 || nm[0] == '<' || !char.IsAsciiLetterUpper(nm[0])) continue;
                if (!topTdsByName.TryGetValue(nm, out var list))
                    topTdsByName[nm] = list = new List<int>(1);
                list.Add(t);
            }

            void MatchSlotsInAsciiWindows(int zoneStart, int zoneEnd, Dictionary<int, int> anchors, Func<int, bool> isEligible)
            {
                // Extract monotonic chain of top-level anchors sorted by slot and short TypeDef.name
                var rawTop = anchors
                    .Where(kv => kv.Key >= zoneStart && kv.Key <= zoneEnd && tds[kv.Value].declaringTypeIndex < 0 && tds[kv.Value].genericContainerIndex < 0)
                    .OrderBy(kv => kv.Key)
                    .ToList();

                // Propagate identical adjacent anchors first
                for (var a = 0; a + 1 < rawTop.Count; a++)
                {
                    if (rawTop[a].Value == rawTop[a + 1].Value)
                    {
                        for (var s = rawTop[a].Key + 1; s < rawTop[a + 1].Key; s++)
                            if (isEligible(s)) anchors.TryAdd(s, rawTop[a].Value);
                    }
                }

                // Build clean monotonic sequence under StringComparer.Ordinal
                var mono = new List<(int slot, int td, string name)>();
                foreach (var kv in rawTop)
                {
                    var nm = tdNames[kv.Value];
                    if (mono.Count == 0 || StringComparer.Ordinal.Compare(mono[^1].name, nm) <= 0)
                        mono.Add((kv.Key, kv.Value, nm));
                }
                if (mono.Count < 2) return;

                static IEnumerable<string> StemsFromIdentifier(string raw)
                {
                    if (string.IsNullOrEmpty(raw)) yield break;
                    var s = raw;
                    if (s.StartsWith("<", StringComparison.Ordinal))
                    {
                        var end = s.IndexOf('>');
                        if (end > 1) s = s[1..end];
                    }
                    if (s.StartsWith("m_", StringComparison.Ordinal) || s.StartsWith("s_", StringComparison.Ordinal) || s.StartsWith("k_", StringComparison.Ordinal))
                        s = s[2..];
                    else if (s.StartsWith("_", StringComparison.Ordinal))
                        s = s[1..];
                    if (s.StartsWith("get_", StringComparison.Ordinal) || s.StartsWith("set_", StringComparison.Ordinal))
                        s = s[4..];
                    else if (s.StartsWith("Get", StringComparison.Ordinal) && s.Length > 3 && char.IsUpper(s[3]))
                        s = s[3..];
                    else if (s.StartsWith("Set", StringComparison.Ordinal) && s.Length > 3 && char.IsUpper(s[3]))
                        s = s[3..];
                    if (s.Length < 3) yield break;
                    yield return s;
                    if (s.EndsWith("Array", StringComparison.Ordinal) && s.Length > 8) yield return s[..^5];
                    if (s.EndsWith("List", StringComparison.Ordinal) && s.Length > 7) yield return s[..^4];
                    if (s.EndsWith("ies", StringComparison.OrdinalIgnoreCase) && s.Length > 5) yield return s[..^3] + "y";
                    if (s.EndsWith("es", StringComparison.OrdinalIgnoreCase) && s.Length > 4) yield return s[..^2];
                    if (s.EndsWith("s", StringComparison.OrdinalIgnoreCase) && s.Length > 3) yield return s[..^1];
                }

                for (var w = 0; w + 1 < mono.Count; w++)
                {
                    var (sA, tdA, nA) = mono[w];
                    var (sB, tdB, nB) = mono[w + 1];
                    if (sB - sA <= 1 || StringComparer.Ordinal.Compare(nA, nB) >= 0) continue;

                    var prevMatchedName = nA;
                    for (var s = sA + 1; s < sB; s++)
                    {
                        if (anchors.ContainsKey(s) || !isEligible(s)) continue;

                        var refTds = new HashSet<int>();
                        var stems = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
                        if (slotFieldCount[s] > 0 && slotFieldIdx[s] >= 0)
                        {
                            refTds.Add(slotFieldTd[s]);
                            foreach (var st in StemsFromIdentifier(meta.GetStringFromIndex(fields[slotFieldIdx[s]].nameIndex)))
                                stems.Add(st);
                        }
                        if (slotParamUses[s] != null)
                        {
                            foreach (var (tdi, _, pdi) in slotParamUses[s])
                            {
                                refTds.Add(tdi);
                                foreach (var st in StemsFromIdentifier(meta.GetStringFromIndex(paramDefs[pdi].nameIndex)))
                                    stems.Add(st);
                            }
                        }
                        if (slotRetUses[s] != null)
                        {
                            foreach (var (tdi, mdi) in slotRetUses[s])
                            {
                                refTds.Add(tdi);
                                foreach (var st in StemsFromIdentifier(meta.GetStringFromIndex(mts[mdi].nameIndex)))
                                    stems.Add(st);
                            }
                        }
                        if (stems.Count == 0) continue;

                        var cands = new HashSet<int>();
                        foreach (var st in stems)
                        {
                            if (!topTdsByName.TryGetValue(st, out var list)) continue;
                            foreach (var candTd in list)
                            {
                                var cn = tdNames[candTd];
                                if (StringComparer.Ordinal.Compare(prevMatchedName, cn) <= 0 &&
                                    StringComparer.Ordinal.Compare(cn, nB) <= 0)
                                {
                                    cands.Add(candTd);
                                }
                            }
                        }
                        if (cands.Count == 0) continue;

                        var chosen = -1;
                        if (cands.Count == 1)
                        {
                            chosen = cands.First();
                        }
                        else
                        {
                            // Prefer candidate sharing namespace prefix or image with referrer
                            var sameNs = cands.Where(c => refTds.Any(r => tdNamespaces[r] == tdNamespaces[c])).ToList();
                            if (sameNs.Count == 1) chosen = sameNs[0];
                        }
                        if (chosen >= 0)
                        {
                            anchors[s] = chosen;
                            prevMatchedName = tdNames[chosen];
                        }
                    }
                }

                // Final fill pass between equal top-level anchors inside zone
                var finalTop = anchors
                    .Where(kv => kv.Key >= zoneStart && kv.Key <= zoneEnd && tds[kv.Value].declaringTypeIndex < 0)
                    .OrderBy(kv => kv.Key)
                    .ToList();
                for (var a = 0; a + 1 < finalTop.Count; a++)
                {
                    if (finalTop[a].Value == finalTop[a + 1].Value)
                    {
                        for (var s = finalTop[a].Key + 1; s < finalTop[a + 1].Key; s++)
                            if (isEligible(s)) anchors.TryAdd(s, finalTop[a].Value);
                    }
                }
            }

            var minConcreteSzBound = szAnchors.Where(kv => tds[kv.Value].declaringTypeIndex < 0).Select(kv => kv.Key).DefaultIfEmpty(szarrayStart).Min();
            MatchSlotsInAsciiWindows(
                szarrayStart,
                arrayStart - 1,
                szAnchors,
                s => s > minConcreteSzBound && !slotHasGenMethod[s] && (slotTdGcs[s] == null || slotTdGcs[s].Count == 0));

            var topAnchors = szAnchors
                .Where(kv => tds[kv.Value].declaringTypeIndex < 0)
                .OrderBy(kv => kv.Key)
                .ToList();
            var firstConcreteSz = topAnchors.Count > 0 ? topAnchors[0].Key : szarrayStart;
            // Apply all concrete SZARRAY anchors + generic/fallback SZARRAY types
            for (var i = szarrayStart; i < arrayStart; i++)
            {
                if (szAnchors.TryGetValue(i, out var elemTd))
                {
                    SetSlot(i, Il2CppTypeEnum.IL2CPP_TYPE_SZARRAY, GetTypePtrForTd(elemTd));
                    continue;
                }
                if (i < firstConcreteSz)
                {
                    if (slotHasGenMethod[i] && !hasFieldDefUse[i] && slotMdGcs[i] != null && slotMdGcs[i].Count == 1)
                    {
                        var gc = gcs[slotMdGcs[i].First()];
                        var mvarPtr = AllocExtraType(Il2CppTypeEnum.IL2CPP_TYPE_MVAR, (ulong)gc.genericParameterStart);
                        SetSlot(i, Il2CppTypeEnum.IL2CPP_TYPE_SZARRAY, mvarPtr);
                        continue;
                    }
                    if (slotTdGcs[i] != null && slotTdGcs[i].Count == 1)
                    {
                        var gc = gcs[slotTdGcs[i].First()];
                        var isEntryField = hasFieldDefUse[i] && slotFieldIdx[i] >= 0 &&
                            (meta.GetStringFromIndex(fields[slotFieldIdx[i]].nameIndex) is "_entries" or "entries" or "_slots");
                        if (gc.type_argc == 1 && !isEntryField)
                        {
                            var varPtr = AllocExtraType(Il2CppTypeEnum.IL2CPP_TYPE_VAR, (ulong)gc.genericParameterStart);
                            SetSlot(i, Il2CppTypeEnum.IL2CPP_TYPE_SZARRAY, varPtr);
                            continue;
                        }
                    }
                }
                SetSlot(i, Il2CppTypeEnum.IL2CPP_TYPE_SZARRAY, objectPtr);
            }

            // -------- 4. Zone 7: ARRAY ([arrayStart .. minBv - 1]) --------
            var f32Td = FindTd("System.Single");
            var f64Td = FindTd("System.Double");
            var terrainHeightsSlot = FindMethodRetInRange("UnityEngine.TerrainData", "GetHeights", 4, arrayStart, minBv - 1);
            var terrainSetHeightsSlot = FindMethodParamInRange("UnityEngine.TerrainData", "SetHeights", 3, 2, arrayStart, minBv - 1);

            for (var i = arrayStart; i < minBv; i++)
            {
                ulong elemPtr = objectPtr;
                if ((terrainHeightsSlot.HasValue && i == terrainHeightsSlot.Value) ||
                    (terrainSetHeightsSlot.HasValue && i == terrainSetHeightsSlot.Value))
                {
                    if (f32Td >= 0) elemPtr = GetTypePtrForTd(f32Td);
                }
                else if (slotHasGenMethod[i] && !hasFieldDefUse[i] && slotMdGcs[i] != null && slotMdGcs[i].Count == 1)
                {
                    elemPtr = AllocExtraType(Il2CppTypeEnum.IL2CPP_TYPE_MVAR, (ulong)gcs[slotMdGcs[i].First()].genericParameterStart);
                }
                else if (slotTdGcs[i] != null && slotTdGcs[i].Count == 1)
                {
                    elemPtr = AllocExtraType(Il2CppTypeEnum.IL2CPP_TYPE_VAR, (ulong)gcs[slotTdGcs[i].First()].genericParameterStart);
                }
                else if (f64Td >= 0 && ((slotParamUses[i] != null && slotParamUses[i].Any(u => tdNamespaces[u.td] == "" && tdNames[u.td] is "apserv" or "ap")) ||
                                        (hasFieldDefUse[i] && tdNames[slotFieldTd[i]] == "apbuffers")))
                {
                    elemPtr = GetTypePtrForTd(f64Td);
                }

                var arrStructPtr = AllocStruct(new Il2CppArrayType
                {
                    etype = elemPtr,
                    rank = 2,
                    numsizes = 0,
                    numlobounds = 0
                });
                SetSlot(i, Il2CppTypeEnum.IL2CPP_TYPE_ARRAY, arrStructPtr);
            }

            // -------- 5. Zone 5: PTR ([ptrStart .. szarrayStart - 1]) --------
            var ptrTarget = new (Il2CppTypeEnum te, ulong dp)?[minBv];
            var u32Td = FindTd("System.UInt32");
            var bufResPtr = FindMethodParamInRange("System.Decimal+DecCalc", "ScaleResult", null, 0, ptrStart, szarrayStart - 1)
                         ?? FindMethodParamInRange("DecCalc", "ScaleResult", null, 0, ptrStart, szarrayStart - 1);
            if (bufResPtr.HasValue && u32Td >= 0)
            {
                var t = recoveredTypes[tds[u32Td].byvalTypeIndex];
                ptrTarget[bufResPtr.Value] = (t.type, t.datapoint);
            }

            // Explicit void* anchors
            void AnchorVoidPtr(int? slot) { if (slot.HasValue) ptrTarget[slot.Value] = (Il2CppTypeEnum.IL2CPP_TYPE_VOID, 0); }
            AnchorVoidPtr(FindMethodRetInRange("System.IntPtr", "ToPointer", 0, ptrStart, szarrayStart - 1));
            AnchorVoidPtr(FindMethodRetInRange("System.UIntPtr", "ToPointer", 0, ptrStart, szarrayStart - 1));
            AnchorVoidPtr(FindMethodParamInRange("System.Buffer", "MemoryCopy", 4, 0, ptrStart, szarrayStart - 1));
            AnchorVoidPtr(FindMethodParamInRange("System.Buffer", "MemoryCopy", 4, 1, ptrStart, szarrayStart - 1));
            AnchorVoidPtr(FindMethodParamInRange("System.Reflection.Pointer", "Unbox", 1, 0, ptrStart, szarrayStart - 1));
            AnchorVoidPtr(FindMethodParamInRange("System.Reflection.Pointer", "Box", 2, 0, ptrStart, szarrayStart - 1));
            AnchorVoidPtr(FindMethodRetInRange("Unity.Collections.LowLevel.Unsafe.UnsafeUtility", "Malloc", 3, ptrStart, szarrayStart - 1));
            AnchorVoidPtr(FindMethodParamInRange("Unity.Collections.LowLevel.Unsafe.UnsafeUtility", "Free", 2, 0, ptrStart, szarrayStart - 1));
            AnchorVoidPtr(FindMethodRetInRange("Unity.Collections.LowLevel.Unsafe.UnsafeUtility", "MallocTracked", 4, ptrStart, szarrayStart - 1));
            AnchorVoidPtr(FindMethodParamInRange("Unity.Collections.LowLevel.Unsafe.UnsafeUtility", "FreeTracked", 2, 0, ptrStart, szarrayStart - 1));
            AnchorVoidPtr(FindMethodParamInRange("Unity.Collections.LowLevel.Unsafe.UnsafeUtility", "MemCpy", 3, 0, ptrStart, szarrayStart - 1));
            AnchorVoidPtr(FindMethodParamInRange("Unity.Collections.LowLevel.Unsafe.UnsafeUtility", "MemClear", 2, 0, ptrStart, szarrayStart - 1));

            for (var i = ptrStart; i < szarrayStart; i++)
            {
                if (ptrTarget[i].HasValue)
                {
                    SetSlot(i, Il2CppTypeEnum.IL2CPP_TYPE_PTR, AllocExtraType(ptrTarget[i].Value.te, ptrTarget[i].Value.dp));
                    continue;
                }
                ulong targetPtr = voidPtr;
                if (slotHasGenMethod[i] && !hasFieldDefUse[i] && slotMdGcs[i] != null && slotMdGcs[i].Count == 1)
                {
                    targetPtr = AllocExtraType(Il2CppTypeEnum.IL2CPP_TYPE_MVAR, (ulong)gcs[slotMdGcs[i].First()].genericParameterStart);
                }
                else if (slotTdGcs[i] != null && slotTdGcs[i].Count == 1 && hasFieldDefUse[i] &&
                         slotFieldIdx[i] >= 0 &&
                         meta.GetStringFromIndex(fields[slotFieldIdx[i]].nameIndex) is "Ptr" or "m_Ptr" or "m_Buffer")
                {
                    targetPtr = AllocExtraType(Il2CppTypeEnum.IL2CPP_TYPE_VAR, (ulong)gcs[slotTdGcs[i].First()].genericParameterStart);
                }
                SetSlot(i, Il2CppTypeEnum.IL2CPP_TYPE_PTR, targetPtr);
            }

            // -------- 6. Zone 4: BYREF ([byrefStart .. ptrStart - 1]) --------
            var byrefElem = new (Il2CppTypeEnum te, ulong dp)?[minBv];
            var byrefTopAnchors = new Dictionary<int, int>();
            void AnchorByrefTd(int? slot, int tdIdx)
            {
                if (!slot.HasValue || tdIdx < 0 || tds[tdIdx].byvalTypeIndex < 0) return;
                var bvt = recoveredTypes[tds[tdIdx].byvalTypeIndex];
                byrefElem[slot.Value] = (bvt.type, bvt.datapoint);
                if (tds[tdIdx].declaringTypeIndex < 0 && tds[tdIdx].genericContainerIndex < 0)
                    byrefTopAnchors.TryAdd(slot.Value, tdIdx);
            }
            void AnchorByrefTryParse(string fullName)
            {
                var eTd = FindTd(fullName);
                var s = FindMethodParamInRange(fullName, "TryParse", 2, 1, byrefStart, ptrStart - 1);
                AnchorByrefTd(s, eTd);
            }

            AnchorByrefTryParse("System.Boolean");
            AnchorByrefTryParse("System.Byte");
            AnchorByrefTryParse("System.SByte");
            AnchorByrefTryParse("System.Char");
            AnchorByrefTryParse("System.DateTime");
            AnchorByrefTryParse("System.Decimal");
            AnchorByrefTryParse("System.Double");
            AnchorByrefTryParse("System.Guid");
            AnchorByrefTryParse("System.Int16");
            AnchorByrefTryParse("System.UInt16");
            AnchorByrefTryParse("System.Int32");
            AnchorByrefTryParse("System.UInt32");
            AnchorByrefTryParse("System.Int64");
            AnchorByrefTryParse("System.UInt64");
            AnchorByrefTryParse("System.Single");
            AnchorByrefTryParse("System.TimeSpan");

            // MonoIO.Write(..., out MonoIOError error)
            var monoIoErrTd = FindTd("System.IO.MonoIOError");
            AnchorByrefTd(FindMethodParamInRange("System.IO.MonoIO", "Write", 5, 4, byrefStart, ptrStart - 1), monoIoErrTd);

            // Physics.Raycast / Linecast out RaycastHit
            var rayHitTd = FindTd("UnityEngine.RaycastHit");
            AnchorByrefTd(FindMethodParamInRange("UnityEngine.Physics", "Raycast", 4, 2, byrefStart, ptrStart - 1), rayHitTd);
            AnchorByrefTd(FindMethodParamInRange("UnityEngine.Physics", "Linecast", 3, 2, byrefStart, ptrStart - 1), rayHitTd);

            // Dictionary<TKey, TValue>.TryGetValue(TKey key, out TValue value)
            var dictTd = FindTd("System.Collections.Generic.Dictionary`2");
            if (dictTd >= 0 && tds[dictTd].genericContainerIndex >= 0)
            {
                var dTryGet = FindMethodParamInRange("System.Collections.Generic.Dictionary`2", "TryGetValue", 2, 1, byrefStart, ptrStart - 1);
                if (dTryGet.HasValue)
                    byrefElem[dTryGet.Value] = (Il2CppTypeEnum.IL2CPP_TYPE_VAR, (ulong)(gcs[tds[dictTd].genericContainerIndex].genericParameterStart + 1));
            }

            // Interlocked.Exchange / CompareExchange(ref T location1, ...) -> exact same type as value!
            var interlockedTd = FindTd("System.Threading.Interlocked");
            if (interlockedTd >= 0 && tds[interlockedTd].methodStart >= 0)
            {
                var mEnd = Math.Min(mts.Length, tds[interlockedTd].methodStart + tds[interlockedTd].method_count);
                for (var mi = tds[interlockedTd].methodStart; mi < mEnd; mi++)
                {
                    var md = mts[mi];
                    var mn = meta.GetStringFromIndex(md.nameIndex);
                    if ((mn != "Exchange" && mn != "CompareExchange") || (mn == "Exchange" && md.parameterCount != 2) || (mn == "CompareExchange" && md.parameterCount != 3))
                        continue;
                    var p0 = paramDefs[md.parameterStart].typeIndex;
                    var p1 = paramDefs[md.parameterStart + 1].typeIndex;
                    if (p0 >= byrefStart && p0 < ptrStart && p1 >= minBv && p1 < recoveredTypes.Length)
                    {
                        var bvt = recoveredTypes[p1];
                        byrefElem[p0] = (bvt.type, bvt.datapoint);
                        if (bvt.type is Il2CppTypeEnum.IL2CPP_TYPE_CLASS or Il2CppTypeEnum.IL2CPP_TYPE_VALUETYPE &&
                            tds[(int)bvt.datapoint].declaringTypeIndex < 0 && tds[(int)bvt.datapoint].genericContainerIndex < 0)
                        {
                            byrefTopAnchors.TryAdd(p0, (int)bvt.datapoint);
                        }
                    }
                }
            }

            // TimeZoneInfo.TryGetLocalTzFile(out byte[] rawData, out string id)
            var tzByteArrRef = FindMethodParamInRange("System.TimeZoneInfo", "TryGetLocalTzFile", 2, 0, byrefStart, ptrStart - 1);
            var tzStrRef = FindMethodParamInRange("System.TimeZoneInfo", "TryGetLocalTzFile", 2, 1, byrefStart, ptrStart - 1);
            if (tzByteArrRef.HasValue && byteTdIdx >= 0)
                byrefElem[tzByteArrRef.Value] = (Il2CppTypeEnum.IL2CPP_TYPE_SZARRAY, GetTypePtrForTd(byteTdIdx));
            if (tzStrRef.HasValue)
            {
                byrefElem[tzStrRef.Value] = (Il2CppTypeEnum.IL2CPP_TYPE_STRING, 0);
                var strTdIdx = FindTd("System.String");
                if (strTdIdx >= 0) byrefTopAnchors.TryAdd(tzStrRef.Value, strTdIdx);
            }

            // Unity *_Injected paired managed wrappers & _unity_self
            for (var t = 0; t < tds.Length; t++)
            {
                var td = tds[t];
                if (td.methodStart < 0 || td.method_count == 0) continue;
                var mEnd = Math.Min(mts.Length, td.methodStart + td.method_count);
                for (var mi = td.methodStart; mi < mEnd; mi++)
                {
                    var md = mts[mi];
                    var mn = meta.GetStringFromIndex(md.nameIndex);
                    if (!mn.EndsWith("_Injected", StringComparison.Ordinal) || md.parameterCount <= 0) continue;

                    var baseName = mn[..^"_Injected".Length];
                    // 1) _unity_self -> declaring type
                    var p0 = paramDefs[md.parameterStart];
                    if (p0.typeIndex >= byrefStart && p0.typeIndex < ptrStart &&
                        meta.GetStringFromIndex(p0.nameIndex) == "_unity_self" &&
                        tds[t].byvalTypeIndex >= 0)
                    {
                        var bvt = recoveredTypes[tds[t].byvalTypeIndex];
                        byrefElem[p0.typeIndex] ??= (bvt.type, bvt.datapoint);
                        if (tds[t].declaringTypeIndex < 0 && tds[t].genericContainerIndex < 0)
                            byrefTopAnchors.TryAdd(p0.typeIndex, t);
                    }

                    // 2) Match sibling managed get_/set_ method with concrete >= minBv types
                    if (baseName.StartsWith("get_", StringComparison.Ordinal) && md.parameterCount >= 1)
                    {
                        var lastPi = md.parameterStart + md.parameterCount - 1;
                        var lastTi = paramDefs[lastPi].typeIndex;
                        if (lastTi >= byrefStart && lastTi < ptrStart && byrefElem[lastTi] == null)
                        {
                            for (var smi = td.methodStart; smi < mEnd; smi++)
                            {
                                if (meta.GetStringFromIndex(mts[smi].nameIndex) == baseName &&
                                    mts[smi].returnType >= minBv && mts[smi].returnType < recoveredTypes.Length)
                                {
                                    var rt = recoveredTypes[mts[smi].returnType];
                                    byrefElem[lastTi] = (rt.type, rt.datapoint);
                                    var rTd = rt.type is Il2CppTypeEnum.IL2CPP_TYPE_CLASS or Il2CppTypeEnum.IL2CPP_TYPE_VALUETYPE ? (int)rt.datapoint : -1;
                                    if (rTd >= 0 && rTd < tds.Length && tds[rTd].declaringTypeIndex < 0 && tds[rTd].genericContainerIndex < 0)
                                        byrefTopAnchors.TryAdd(lastTi, rTd);
                                    break;
                                }
                            }
                        }
                    }
                    else if (baseName.StartsWith("set_", StringComparison.Ordinal) && md.parameterCount >= 1)
                    {
                        var lastPi = md.parameterStart + md.parameterCount - 1;
                        var lastTi = paramDefs[lastPi].typeIndex;
                        if (lastTi >= byrefStart && lastTi < ptrStart && byrefElem[lastTi] == null)
                        {
                            for (var smi = td.methodStart; smi < mEnd; smi++)
                            {
                                if (meta.GetStringFromIndex(mts[smi].nameIndex) == baseName && mts[smi].parameterCount >= 1)
                                {
                                    var sLast = paramDefs[mts[smi].parameterStart + mts[smi].parameterCount - 1].typeIndex;
                                    if (sLast >= minBv && sLast < recoveredTypes.Length)
                                    {
                                        var st = recoveredTypes[sLast];
                                        byrefElem[lastTi] = (st.type, st.datapoint);
                                        var sTd = st.type is Il2CppTypeEnum.IL2CPP_TYPE_CLASS or Il2CppTypeEnum.IL2CPP_TYPE_VALUETYPE ? (int)st.datapoint : -1;
                                        if (sTd >= 0 && sTd < tds.Length && tds[sTd].declaringTypeIndex < 0 && tds[sTd].genericContainerIndex < 0)
                                            byrefTopAnchors.TryAdd(lastTi, sTd);
                                        break;
                                    }
                                }
                            }
                        }
                    }
                }
            }

            // ASCII-windowed matching for concrete top-level BYREF slots + equal-anchor propagation
            var minConcreteByref = byrefTopAnchors.Count > 0 ? byrefTopAnchors.Keys.Min() : byrefStart;
            MatchSlotsInAsciiWindows(
                byrefStart,
                ptrStart - 1,
                byrefTopAnchors,
                s => s >= minConcreteByref && !slotHasGenMethod[s] && (slotTdGcs[s] == null || slotTdGcs[s].Count == 0));
            foreach (var kv in byrefTopAnchors)
            {
                if (!byrefElem[kv.Key].HasValue && tds[kv.Value].byvalTypeIndex >= 0)
                {
                    var bvt = recoveredTypes[tds[kv.Value].byvalTypeIndex];
                    byrefElem[kv.Key] = (bvt.type, bvt.datapoint);
                }
            }

            // Fill small gaps between equal-element BYREF anchors (e.g. ref Single vs out Single)
            var byrefAnchorIdx = new List<int>();
            for (var i = byrefStart; i < ptrStart; i++)
                if (byrefElem[i].HasValue) byrefAnchorIdx.Add(i);
            for (var k = 0; k + 1 < byrefAnchorIdx.Count; k++)
            {
                var iA = byrefAnchorIdx[k];
                var iB = byrefAnchorIdx[k + 1];
                if (iB - iA <= 10 && byrefElem[iA]!.Value == byrefElem[iB]!.Value)
                {
                    for (var s = iA + 1; s < iB; s++)
                        byrefElem[s] ??= byrefElem[iA];
                }
            }

            const uint PARAM_ATTRIBUTE_OUT = 0x0002;
            for (var i = byrefStart; i < ptrStart; i++)
            {
                var inner = byrefElem[i];
                if (!inner.HasValue)
                {
                    if (slotHasGenMethod[i] && !hasFieldDefUse[i] && slotMdGcs[i] != null && slotMdGcs[i].Count == 1)
                    {
                        inner = (Il2CppTypeEnum.IL2CPP_TYPE_MVAR, (ulong)gcs[slotMdGcs[i].First()].genericParameterStart);
                    }
                    else if (slotTdGcs[i] != null && slotTdGcs[i].Count == 1)
                    {
                        inner = (Il2CppTypeEnum.IL2CPP_TYPE_VAR, (ulong)gcs[slotTdGcs[i].First()].genericParameterStart);
                    }
                    else
                    {
                        inner = (Il2CppTypeEnum.IL2CPP_TYPE_OBJECT, 0);
                    }
                }

                uint byrefAttrs = 0x0000;
                if (!hasFieldDefUse[i] && slotParamUses[i] != null && slotParamUses[i].Count > 0)
                {
                    var allOut = true;
                    foreach (var (tdi, mdi, pdi) in slotParamUses[i])
                    {
                        var mn = meta.GetStringFromIndex(mts[mdi].nameIndex);
                        var pn = meta.GetStringFromIndex(paramDefs[pdi].nameIndex);
                        var isLast = pdi == mts[mdi].parameterStart + mts[mdi].parameterCount - 1;
                        var looksOut = (mn.StartsWith("Try", StringComparison.Ordinal) && (isLast || pn is "rawData" or "id" or "value" or "val" or "result" or "data")) ||
                                       (mn.EndsWith("_Injected", StringComparison.Ordinal) && pn is "ret" or "value" && mn.StartsWith("get_", StringComparison.Ordinal)) ||
                                       (tdNames[tdi] == "MonoIO" && pn == "error") ||
                                       (pn == "hitInfo" && mn is "Raycast" or "Linecast") ||
                                       pn.StartsWith("out", StringComparison.OrdinalIgnoreCase) ||
                                       pn == "result" || pn == "ret";
                        if (!looksOut) { allOut = false; break; }
                    }
                    if (allOut) byrefAttrs = PARAM_ATTRIBUTE_OUT;
                }

                SetSlot(i, inner.Value.te, inner.Value.dp, byref: true, overrideAttrs: byrefAttrs);
            }

            // -------- 7. Zone 3: GENERICINST ([genInstStart .. byrefStart - 1]) --------
            var appliedGenInst = new bool[minBv];

            bool TryApplyGenericInst(int slot, int defTdIdx, ulong[] argPtrs)
            {
                if (slot < genInstStart || slot >= byrefStart) return false;
                if (defTdIdx < 0 || defTdIdx >= tds.Length || tds[defTdIdx].genericContainerIndex < 0) return false;
                var defGc = gcs[tds[defTdIdx].genericContainerIndex];
                if (argPtrs == null || argPtrs.Length != defGc.type_argc || argPtrs.Length == 0) return false;

                var argvPtr = AllocStruct(argPtrs);
                var instPtr = AllocStruct(new Il2CppGenericInst
                {
                    type_argc = argPtrs.Length,
                    type_argv = argvPtr
                });
                var gclassPtr = AllocStruct(new Il2CppGenericClass
                {
                    typeDefinitionIndex = defTdIdx,
                    type = GetTypePtrForTd(defTdIdx),
                    context = new Il2CppGenericContext { class_inst = instPtr, method_inst = 0 },
                    cached_class = 0
                });
                SetSlot(slot, Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST, gclassPtr);
                appliedGenInst[slot] = true;
                return true;
            }

            // Resolve Action`N / Func`N / Predicate`1 / Comparison`1 / IEnumerable`1 / List`1 / Enumerator defs
            var actionDefs = new int[17];
            var funcDefs = new int[18];
            Array.Fill(actionDefs, -1);
            Array.Fill(funcDefs, -1);
            for (var n = 1; n <= 16; n++) actionDefs[n] = FindTd($"System.Action`{n}");
            for (var n = 1; n <= 17; n++) funcDefs[n] = FindTd($"System.Func`{n}");

            // Pass A: Compiler-generated <>c.<>9 singleton fields + <>9__* cached lambda delegates
            for (var i = genInstStart; i < byrefStart; i++)
            {
                if (slotFieldCount[i] != 1 || slotFieldTd[i] < 0) continue;
                var ownerTd = slotFieldTd[i];
                var ownerName = tdNames[ownerTd];
                var fName = meta.GetStringFromIndex(fields[slotFieldIdx[i]].nameIndex);
                var isClosureClass = ownerName == "<>c" ||
                    (ownerName.StartsWith("<>c__", StringComparison.Ordinal) && !ownerName.Contains("DisplayClass", StringComparison.Ordinal));
                if (!isClosureClass) continue;

                if (fName == "<>9" && tds[ownerTd].genericContainerIndex >= 0)
                {
                    var gc = gcs[tds[ownerTd].genericContainerIndex];
                    var argPtrs = new ulong[gc.type_argc];
                    for (var k = 0; k < gc.type_argc; k++)
                        argPtrs[k] = AllocExtraType(Il2CppTypeEnum.IL2CPP_TYPE_VAR, (ulong)(gc.genericParameterStart + k));
                    TryApplyGenericInst(i, ownerTd, argPtrs);
                }
                else if (fName.StartsWith("<>9__", StringComparison.Ordinal) && tds[ownerTd].genericContainerIndex < 0 && tds[ownerTd].methodStart >= 0)
                {
                    // Find sibling <...>b__X_Y method on <>c
                    var suffix = fName["<>9__".Length..];
                    var mEnd = Math.Min(mts.Length, tds[ownerTd].methodStart + tds[ownerTd].method_count);
                    for (var mi = tds[ownerTd].methodStart; mi < mEnd; mi++)
                    {
                        var md = mts[mi];
                        var mn = meta.GetStringFromIndex(md.nameIndex);
                        if (!mn.EndsWith($"b__{suffix}", StringComparison.Ordinal)) continue;
                        if (md.returnType < minBv || md.returnType >= recoveredTypes.Length) break;
                        var isVoidRet = recoveredTypes[md.returnType].type == Il2CppTypeEnum.IL2CPP_TYPE_VOID;
                        var allParamsConcrete = true;
                        var pList = new ulong[md.parameterCount];
                        for (var p = 0; p < md.parameterCount; p++)
                        {
                            var pt = paramDefs[md.parameterStart + p].typeIndex;
                            if (pt < minBv || pt >= recoveredTypes.Length) { allParamsConcrete = false; break; }
                            pList[p] = SYNTH_TYPE_BASE + (uint)pt;
                        }
                        if (!allParamsConcrete) break;

                        if (isVoidRet)
                        {
                            if (md.parameterCount >= 1 && md.parameterCount <= 16 && actionDefs[md.parameterCount] >= 0)
                                TryApplyGenericInst(i, actionDefs[md.parameterCount], pList);
                        }
                        else if (md.parameterCount >= 0 && md.parameterCount + 1 <= 17 && funcDefs[md.parameterCount + 1] >= 0)
                        {
                            var args = new ulong[md.parameterCount + 1];
                            Array.Copy(pList, args, md.parameterCount);
                            args[md.parameterCount] = SYNTH_TYPE_BASE + (uint)md.returnType;
                            TryApplyGenericInst(i, funcDefs[md.parameterCount + 1], args);
                        }
                        break;
                    }
                }
            }

            // Pass B: Unique Generic Singleton parent classes (MonoSingleton<Self> / Singleton<Self>)
            for (var i = genInstStart; i < byrefStart; i++)
            {
                if (appliedGenInst[i] || slotParentTds[i] == null || slotParentTds[i].Count != 1) continue;
                if (hasFieldDefUse[i] || hasParamDefUse[i] || slotRetUses[i] != null || slotIfaceTds[i] != null) continue;
                var childTd = slotParentTds[i][0];
                if (tds[childTd].genericContainerIndex >= 0) continue;
                var baseTd = resolvedParentTd[childTd];
                if (baseTd >= 0 && tds[baseTd].genericContainerIndex >= 0 &&
                    gcs[tds[baseTd].genericContainerIndex].type_argc == 1 &&
                    tdNames[baseTd].Contains("Singleton", StringComparison.OrdinalIgnoreCase))
                {
                    TryApplyGenericInst(i, baseTd, new[] { GetTypePtrForTd(childTd) });
                }
            }

            // Pass C: Unique IEquatable<T> / IComparable<T> interface slots
            var iEquatableTd = FindTd("System.IEquatable`1");
            var iComparableTd = FindTd("System.IComparable`1");
            for (var i = genInstStart; i < byrefStart; i++)
            {
                if (appliedGenInst[i] || slotIfaceTds[i] == null || slotIfaceTds[i].Count != 1) continue;
                if (hasFieldDefUse[i] || hasParamDefUse[i] || slotRetUses[i] != null || slotParentTds[i] != null) continue;
                var implTdIdx = slotIfaceTds[i][0];
                var implTd = tds[implTdIdx];
                if (implTd.genericContainerIndex >= 0 || implTd.methodStart < 0) continue;
                var mEnd = Math.Min(mts.Length, implTd.methodStart + implTd.method_count);
                var hasEqSelf = false;
                var hasCmpSelf = false;
                for (var mi = implTd.methodStart; mi < mEnd; mi++)
                {
                    var md = mts[mi];
                    if (md.parameterCount != 1) continue;
                    var pti = paramDefs[md.parameterStart].typeIndex;
                    if (pti < minBv || !bvToTd.TryGetValue(pti, out var pTd) || pTd != implTdIdx) continue;
                    var mn = meta.GetStringFromIndex(md.nameIndex);
                    if (mn == "Equals") hasEqSelf = true;
                    else if (mn == "CompareTo") hasCmpSelf = true;
                }
                if (hasEqSelf && !hasCmpSelf && iEquatableTd >= 0)
                    TryApplyGenericInst(i, iEquatableTd, new[] { GetTypePtrForTd(implTdIdx) });
                else if (hasCmpSelf && !hasEqSelf && iComparableTd >= 0)
                    TryApplyGenericInst(i, iComparableTd, new[] { GetTypePtrForTd(implTdIdx) });
            }

            // Pass D: Core BCL List<T>, Dictionary<K,V>, HashSet<T> open-generic member instantiations
            var listTd = FindTd("System.Collections.Generic.List`1");
            if (listTd >= 0 && tds[listTd].genericContainerIndex >= 0 && tds[listTd].methodStart >= 0)
            {
                var listVarPtr = AllocExtraType(Il2CppTypeEnum.IL2CPP_TYPE_VAR, (ulong)gcs[tds[listTd].genericContainerIndex].genericParameterStart);
                var listEnumTd = FindTd("System.Collections.Generic.List`1+Enumerator");
                var predicateTd = FindTd("System.Predicate`1");
                var comparisonTd = FindTd("System.Comparison`1");
                var iEnumTd = FindTd("System.Collections.Generic.IEnumerable`1");
                var roColTd = FindTd("System.Collections.ObjectModel.ReadOnlyCollection`1");

                var mEnd = Math.Min(mts.Length, tds[listTd].methodStart + tds[listTd].method_count);
                for (var mi = tds[listTd].methodStart; mi < mEnd; mi++)
                {
                    var md = mts[mi];
                    var mn = meta.GetStringFromIndex(md.nameIndex);
                    if (md.returnType >= genInstStart && md.returnType < byrefStart && !appliedGenInst[md.returnType])
                    {
                        if (mn == "GetEnumerator" && listEnumTd >= 0) TryApplyGenericInst(md.returnType, listEnumTd, new[] { listVarPtr });
                        else if (mn == "FindAll" && listTd >= 0) TryApplyGenericInst(md.returnType, listTd, new[] { listVarPtr });
                        else if (mn == "AsReadOnly" && roColTd >= 0) TryApplyGenericInst(md.returnType, roColTd, new[] { listVarPtr });
                    }
                    if (md.parameterCount == 1)
                    {
                        var pt = paramDefs[md.parameterStart].typeIndex;
                        if (pt >= genInstStart && pt < byrefStart && !appliedGenInst[pt])
                        {
                            if (mn == "ForEach" && actionDefs[1] >= 0) TryApplyGenericInst(pt, actionDefs[1], new[] { listVarPtr });
                            else if ((mn == "Find" || mn == "FindLast" || mn == "FindAll" || mn == "Exists" || mn == "RemoveAll" || mn == "TrueForAll") && predicateTd >= 0)
                                TryApplyGenericInst(pt, predicateTd, new[] { listVarPtr });
                            else if (mn == "Sort" && comparisonTd >= 0) TryApplyGenericInst(pt, comparisonTd, new[] { listVarPtr });
                            else if (mn == "AddRange" && iEnumTd >= 0) TryApplyGenericInst(pt, iEnumTd, new[] { listVarPtr });
                        }
                    }
                }
            }

            if (dictTd >= 0 && tds[dictTd].genericContainerIndex >= 0)
            {
                var dGp = gcs[tds[dictTd].genericContainerIndex].genericParameterStart;
                var dKeyVarPtr = AllocExtraType(Il2CppTypeEnum.IL2CPP_TYPE_VAR, (ulong)dGp);
                var dValVarPtr = AllocExtraType(Il2CppTypeEnum.IL2CPP_TYPE_VAR, (ulong)(dGp + 1));
                var eqCompTd = FindTd("System.Collections.Generic.IEqualityComparer`1");
                var keyColTd = FindTd("System.Collections.Generic.Dictionary`2+KeyCollection");
                var valColTd = FindTd("System.Collections.Generic.Dictionary`2+ValueCollection");
                var dEnumTd = FindTd("System.Collections.Generic.Dictionary`2+Enumerator");

                var compSlot = FindFieldTypeInRange("System.Collections.Generic.Dictionary`2", "_comparer", genInstStart, byrefStart - 1);
                if (compSlot.HasValue && eqCompTd >= 0 && !appliedGenInst[compSlot.Value])
                    TryApplyGenericInst(compSlot.Value, eqCompTd, new[] { dKeyVarPtr });
                var keysSlot = FindFieldTypeInRange("System.Collections.Generic.Dictionary`2", "_keys", genInstStart, byrefStart - 1);
                if (keysSlot.HasValue && keyColTd >= 0 && !appliedGenInst[keysSlot.Value])
                    TryApplyGenericInst(keysSlot.Value, keyColTd, new[] { dKeyVarPtr, dValVarPtr });
                var valsSlot = FindFieldTypeInRange("System.Collections.Generic.Dictionary`2", "_values", genInstStart, byrefStart - 1);
                if (valsSlot.HasValue && valColTd >= 0 && !appliedGenInst[valsSlot.Value])
                    TryApplyGenericInst(valsSlot.Value, valColTd, new[] { dKeyVarPtr, dValVarPtr });
                var getCompRet = FindMethodRetInRange("System.Collections.Generic.Dictionary`2", "get_Comparer", 0, genInstStart, byrefStart - 1);
                if (getCompRet.HasValue && eqCompTd >= 0 && !appliedGenInst[getCompRet.Value])
                    TryApplyGenericInst(getCompRet.Value, eqCompTd, new[] { dKeyVarPtr });
                var getKeysRet = FindMethodRetInRange("System.Collections.Generic.Dictionary`2", "get_Keys", 0, genInstStart, byrefStart - 1);
                if (getKeysRet.HasValue && keyColTd >= 0 && !appliedGenInst[getKeysRet.Value])
                    TryApplyGenericInst(getKeysRet.Value, keyColTd, new[] { dKeyVarPtr, dValVarPtr });
                var getValsRet = FindMethodRetInRange("System.Collections.Generic.Dictionary`2", "get_Values", 0, genInstStart, byrefStart - 1);
                if (getValsRet.HasValue && valColTd >= 0 && !appliedGenInst[getValsRet.Value])
                    TryApplyGenericInst(getValsRet.Value, valColTd, new[] { dKeyVarPtr, dValVarPtr });
                var dEnumRet = FindMethodRetInRange("System.Collections.Generic.Dictionary`2", "GetEnumerator", 0, genInstStart, byrefStart - 1);
                if (dEnumRet.HasValue && dEnumTd >= 0 && !appliedGenInst[dEnumRet.Value])
                    TryApplyGenericInst(dEnumRet.Value, dEnumTd, new[] { dKeyVarPtr, dValVarPtr });
                var dEntryTd = FindTd("System.Collections.Generic.Dictionary`2+Entry");
                var entriesSlot = FindFieldTypeInRange("System.Collections.Generic.Dictionary`2", "_entries", szarrayStart, arrayStart - 1);
                if (entriesSlot.HasValue && dEntryTd >= 0)
                {
                    var eGc = AllocStruct(new Il2CppGenericInst { type_argc = 2, type_argv = AllocStruct(new[] { dKeyVarPtr, dValVarPtr }) });
                    var eGclass = AllocStruct(new Il2CppGenericClass
                    {
                        typeDefinitionIndex = dEntryTd,
                        type = GetTypePtrForTd(dEntryTd),
                        context = new Il2CppGenericContext { class_inst = eGc, method_inst = 0 },
                        cached_class = 0
                    });
                    var eTypePtr = AllocExtraType(Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST, eGclass);
                    SetSlot(entriesSlot.Value, Il2CppTypeEnum.IL2CPP_TYPE_SZARRAY, eTypePtr);
                }
            }

            // Pass E: Recover known open-generic BCL collection interfaces (< minBv) on List<T>, Dictionary<K,V>, HashSet<T>, Queue<T>, Stack<T>
            void ApplyOpenCollectionInterfaces(string fullName, string[] subMinBvIfacesInDeclOrder)
            {
                var tdIdx = FindTd(fullName);
                if (tdIdx < 0 || tds[tdIdx].genericContainerIndex < 0 || tds[tdIdx].interfaces_count == 0 || meta.interfaceIndices == null) return;
                var td = tds[tdIdx];
                var gc = gcs[td.genericContainerIndex];
                var argPtrs = new ulong[gc.type_argc];
                for (var a = 0; a < gc.type_argc; a++)
                    argPtrs[a] = AllocExtraType(Il2CppTypeEnum.IL2CPP_TYPE_VAR, (ulong)(gc.genericParameterStart + a));

                var subSlots = new List<int>();
                for (var k = 0; k < td.interfaces_count && td.interfacesStart + k < meta.interfaceIndices.Length; k++)
                {
                    var ii = meta.interfaceIndices[td.interfacesStart + k];
                    if (ii >= genInstStart && ii < byrefStart) subSlots.Add(ii);
                }
                if (subSlots.Count != subMinBvIfacesInDeclOrder.Length) return;
                for (var k = 0; k < subSlots.Count; k++)
                {
                    if (appliedGenInst[subSlots[k]]) continue;
                    var ifaceName = subMinBvIfacesInDeclOrder[k];
                    if (ifaceName.EndsWith("<KVP>", StringComparison.Ordinal))
                    {
                        var outerIfaceTd = FindTd(ifaceName[..^5]);
                        var kvpTd = FindTd("System.Collections.Generic.KeyValuePair`2");
                        if (outerIfaceTd >= 0 && kvpTd >= 0 && gc.type_argc == 2)
                        {
                            var kvpGc = AllocStruct(new Il2CppGenericInst { type_argc = 2, type_argv = AllocStruct(argPtrs) });
                            var kvpGclass = AllocStruct(new Il2CppGenericClass
                            {
                                typeDefinitionIndex = kvpTd,
                                type = GetTypePtrForTd(kvpTd),
                                context = new Il2CppGenericContext { class_inst = kvpGc, method_inst = 0 },
                                cached_class = 0
                            });
                            var kvpTypePtr = AllocExtraType(Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST, kvpGclass);
                            TryApplyGenericInst(subSlots[k], outerIfaceTd, new[] { kvpTypePtr });
                        }
                    }
                    else
                    {
                        var ifaceTd = FindTd(ifaceName);
                        if (ifaceTd >= 0) TryApplyGenericInst(subSlots[k], ifaceTd, argPtrs);
                    }
                }
            }

            ApplyOpenCollectionInterfaces("System.Collections.Generic.List`1", new[]
            {
                "System.Collections.Generic.IList`1",
                "System.Collections.Generic.ICollection`1",
                "System.Collections.Generic.IEnumerable`1",
                "System.Collections.Generic.IReadOnlyList`1",
                "System.Collections.Generic.IReadOnlyCollection`1"
            });
            ApplyOpenCollectionInterfaces("System.Collections.Generic.Dictionary`2", new[]
            {
                "System.Collections.Generic.IDictionary`2",
                "System.Collections.Generic.ICollection`1<KVP>",
                "System.Collections.Generic.IEnumerable`1<KVP>",
                "System.Collections.Generic.IReadOnlyDictionary`2",
                "System.Collections.Generic.IReadOnlyCollection`1<KVP>"
            });

            Console.WriteLine($"Sub-minBv zones (minBv={minBv}): MVAR=[0..{varStart - 1}], VAR=[{varStart}..{genInstStart - 1}], GENERICINST=[{genInstStart}..{byrefStart - 1}], BYREF=[{byrefStart}..{ptrStart - 1}], PTR=[{ptrStart}..{szarrayStart - 1}], SZARRAY=[{szarrayStart}..{arrayStart - 1}], ARRAY=[{arrayStart}..{minBv - 1}]");
        }

        private static int[] ResolveAllParentTypeDefs(
            Metadata meta,
            Il2CppTypeDefinition[] tds,
            Il2CppMethodDefinition[] mts,
            int minBv,
            Func<int, int> resolveConcreteTd)
        {
            var resolved = new int[tds.Length];
            Array.Fill(resolved, -1);

            for (var ti = 0; ti < tds.Length; ti++)
            {
                var pIdx = tds[ti].parentIndex;
                if (pIdx >= minBv)
                {
                    resolved[ti] = resolveConcreteTd(pIdx);
                }
            }

            var vt = meta.vtableMethods;
            if (vt == null || vt.Length == 0)
            {
                return resolved;
            }

            var genericTds = new List<int>();
            var byOverrideName = new Dictionary<uint, List<int>>();
            for (var t = 0; t < tds.Length; t++)
            {
                if (tds[t].genericContainerIndex >= 0 && (tds[t].flags & TYPE_ATTRIBUTE_INTERFACE) == 0 && !tds[t].IsValueType)
                {
                    genericTds.Add(t);
                    var gvt = tds[t].vtable_count;
                    if (gvt <= 0 || tds[t].vtableStart < 0) continue;
                    var seenNames = new HashSet<uint>();
                    for (var s = 0; s < gvt && tds[t].vtableStart + s < vt.Length; s++)
                    {
                        var raw = vt[tds[t].vtableStart + s];
                        if (meta.GetEncodedIndexTypeForVersion(raw) == 3)
                        {
                            var gi = (int)meta.GetDecodedMethodIndex(raw);
                            if (gi >= 0 && gi < mts.Length &&
                                mts[gi].declaringType >= 0 &&
                                tds[mts[gi].declaringType].genericContainerIndex >= 0 &&
                                seenNames.Add(mts[gi].nameIndex))
                            {
                                if (!byOverrideName.TryGetValue(mts[gi].nameIndex, out var lst))
                                {
                                    lst = new List<int>();
                                    byOverrideName[mts[gi].nameIndex] = lst;
                                }
                                lst.Add(t);
                            }
                        }
                    }
                }
            }

            var depthCache = new int[tds.Length];
            int GetConcreteDepth(int t)
            {
                if (depthCache[t] != 0) return depthCache[t];
                depthCache[t] = 1;
                var p = resolved[t];
                var d = (p >= 0 && p != t) ? 1 + GetConcreteDepth(p) : 1;
                depthCache[t] = d;
                return d;
            }

            bool NamesMatch(uint gNameIdx, uint cNameIdx)
            {
                if (gNameIdx == cNameIdx) return true;
                var gn = meta.GetStringFromIndex(gNameIdx);
                var cn = meta.GetStringFromIndex(cNameIdx);
                return cn.EndsWith("." + gn, StringComparison.Ordinal);
            }

            var overrideNames = new List<uint>();
            var concreteDecls = new HashSet<int>();
            var candSet = new HashSet<int>();

            for (var ti = 0; ti < tds.Length; ti++)
            {
                var td = tds[ti];
                if (td.IsValueType || (td.flags & TYPE_ATTRIBUTE_INTERFACE) != 0 || td.parentIndex < 0 || td.parentIndex >= minBv)
                {
                    continue;
                }

                overrideNames.Clear();
                concreteDecls.Clear();
                candSet.Clear();

                var cvt = td.vtable_count;
                var maxK6Slot = -1;
                if (cvt > 0 && td.vtableStart >= 0)
                {
                    for (var s = 0; s < cvt && td.vtableStart + s < vt.Length; s++)
                    {
                        var raw = vt[td.vtableStart + s];
                        var kind = meta.GetEncodedIndexTypeForVersion(raw);
                        if (kind == 6)
                        {
                            maxK6Slot = s;
                        }
                        else if (kind == 3)
                        {
                            var ci = (int)meta.GetDecodedMethodIndex(raw);
                            if (ci >= 0 && ci < mts.Length)
                            {
                                var decl = mts[ci].declaringType;
                                if (decl == ti) overrideNames.Add(mts[ci].nameIndex);
                                else if (decl >= 0 && tds[decl].genericContainerIndex < 0) concreteDecls.Add(decl);
                            }
                        }
                    }
                }

                foreach (var nm in overrideNames)
                {
                    if (byOverrideName.TryGetValue(nm, out var pool))
                    {
                        foreach (var g in pool) candSet.Add(g);
                    }
                }
                if (candSet.Count == 0 && maxK6Slot >= 0)
                {
                    foreach (var g in genericTds)
                    {
                        if (tds[g].vtable_count > maxK6Slot) candSet.Add(g);
                    }
                }

                var bestCand = -1;
                var bestScore = int.MinValue;
                foreach (var g in candSet)
                {
                    var gvt = tds[g].vtable_count;
                    if (g == ti || gvt > cvt || gvt <= maxK6Slot || tds[g].vtableStart < 0) continue;
                    if (tds[g].interfaces_count > td.interfaces_count) continue;

                    var ok = true;
                    var genericSlotMatches = 0;
                    for (var s = 0; s < gvt && tds[g].vtableStart + s < vt.Length && td.vtableStart + s < vt.Length; s++)
                    {
                        var graw = vt[tds[g].vtableStart + s];
                        var craw = vt[td.vtableStart + s];
                        var gk = meta.GetEncodedIndexTypeForVersion(graw);
                        var ck = meta.GetEncodedIndexTypeForVersion(craw);

                        if (ck == 6)
                        {
                            if (gk == 3)
                            {
                                var gi = (int)meta.GetDecodedMethodIndex(graw);
                                if (gi < 0 || gi >= mts.Length || mts[gi].declaringType < 0 || tds[mts[gi].declaringType].genericContainerIndex < 0)
                                {
                                    ok = false;
                                    break;
                                }
                                genericSlotMatches++;
                            }
                        }
                        else if (ck == 3)
                        {
                            var ci = (int)meta.GetDecodedMethodIndex(craw);
                            if (ci < 0 || ci >= mts.Length) { ok = false; break; }
                            var cDecl = mts[ci].declaringType;
                            if (gk == 3)
                            {
                                var gi = (int)meta.GetDecodedMethodIndex(graw);
                                if (gi < 0 || gi >= mts.Length) { ok = false; break; }
                                if (cDecl != ti && cDecl >= 0 && tds[cDecl].genericContainerIndex < 0)
                                {
                                    if (graw != craw) { ok = false; break; }
                                }
                                else
                                {
                                    if (!NamesMatch(mts[gi].nameIndex, mts[ci].nameIndex)) { ok = false; break; }
                                    genericSlotMatches++;
                                }
                            }
                            else if (gk == 6)
                            {
                                if (cDecl != ti) { ok = false; break; }
                                genericSlotMatches++;
                            }
                        }
                    }

                    if (ok && genericSlotMatches > 0)
                    {
                        var score = genericSlotMatches * 100 + gvt * 10 +
                                    (tds[g].namespaceIndex == td.namespaceIndex ? 1 : 0) +
                                    (tds[g].field_count > 0 ? 1 : 0);
                        if (score > bestScore)
                        {
                            bestScore = score;
                            bestCand = g;
                        }
                    }
                }

                if (bestCand >= 0)
                {
                    resolved[ti] = bestCand;
                }
                else
                {
                    // Deepest non-interface concrete ancestor seen in child's vtableMethods
                    var bestDepth = 0;
                    foreach (var c in concreteDecls)
                    {
                        if ((tds[c].flags & TYPE_ATTRIBUTE_INTERFACE) == 0)
                        {
                            var d = GetConcreteDepth(c);
                            if (d > bestDepth)
                            {
                                bestDepth = d;
                                bestCand = c;
                            }
                        }
                    }
                    resolved[ti] = bestCand;
                }
            }

            return resolved;
        }

        private static List<(int fromTi, int toTi)> FindValueTypeCycleEdges(int count, Dictionary<int, List<int>> edges)
        {
            var cycleEdges = new List<(int, int)>();
            if (edges.Count == 0) return cycleEdges;

            var color = new byte[count];
            var stack = new Stack<(int node, int idx)>();
            foreach (var start in edges.Keys)
            {
                if (color[start] != 0) continue;
                color[start] = 1;
                stack.Push((start, 0));
                while (stack.Count > 0)
                {
                    var (u, idx) = stack.Pop();
                    if (!edges.TryGetValue(u, out var nbrs) || idx >= nbrs.Count)
                    {
                        color[u] = 2;
                        continue;
                    }
                    stack.Push((u, idx + 1));
                    var v = nbrs[idx];
                    if (color[v] == 1)
                    {
                        cycleEdges.Add((u, v));
                    }
                    else if (color[v] == 0)
                    {
                        color[v] = 1;
                        stack.Push((v, 0));
                    }
                }
            }
            return cycleEdges;
        }

        private static int DecodePackingSize(uint bitfield)
        {
            // Bit 10 is PackingSizeIsDefault (MetadataClass.cs:337); bits 6..9 encode one of 9 packing sizes.
            if (((bitfield >> 10) & 1u) != 0) return 0;
            var code = (int)((bitfield >> 6) & 0xFu);
            return code switch
            {
                1 => 1,
                2 => 2,
                3 => 4,
                4 => 8,
                5 => 16,
                6 => 32,
                7 => 64,
                8 => 128,
                _ => 0
            };
        }

        private static bool TryMapSystemPrimitive(string name, out Il2CppTypeEnum typeEnum)
        {
            typeEnum = name switch
            {
                "Void" => Il2CppTypeEnum.IL2CPP_TYPE_VOID,
                "Boolean" => Il2CppTypeEnum.IL2CPP_TYPE_BOOLEAN,
                "Char" => Il2CppTypeEnum.IL2CPP_TYPE_CHAR,
                "SByte" => Il2CppTypeEnum.IL2CPP_TYPE_I1,
                "Byte" => Il2CppTypeEnum.IL2CPP_TYPE_U1,
                "Int16" => Il2CppTypeEnum.IL2CPP_TYPE_I2,
                "UInt16" => Il2CppTypeEnum.IL2CPP_TYPE_U2,
                "Int32" => Il2CppTypeEnum.IL2CPP_TYPE_I4,
                "UInt32" => Il2CppTypeEnum.IL2CPP_TYPE_U4,
                "Int64" => Il2CppTypeEnum.IL2CPP_TYPE_I8,
                "UInt64" => Il2CppTypeEnum.IL2CPP_TYPE_U8,
                "Single" => Il2CppTypeEnum.IL2CPP_TYPE_R4,
                "Double" => Il2CppTypeEnum.IL2CPP_TYPE_R8,
                "String" => Il2CppTypeEnum.IL2CPP_TYPE_STRING,
                "TypedReference" => Il2CppTypeEnum.IL2CPP_TYPE_TYPEDBYREF,
                "IntPtr" => Il2CppTypeEnum.IL2CPP_TYPE_I,
                "UIntPtr" => Il2CppTypeEnum.IL2CPP_TYPE_U,
                "Object" => Il2CppTypeEnum.IL2CPP_TYPE_OBJECT,
                _ => Il2CppTypeEnum.IL2CPP_TYPE_END
            };
            return typeEnum != Il2CppTypeEnum.IL2CPP_TYPE_END;
        }

        private static bool TryGetPrimitiveSizeAlign(string name, int ptrSize, out int size, out int align)
        {
            switch (name)
            {
                case "Void": size = 1; align = 1; return true;
                case "Boolean":
                case "SByte":
                case "Byte": size = 1; align = 1; return true;
                case "Char":
                case "Int16":
                case "UInt16": size = 2; align = 2; return true;
                case "Int32":
                case "UInt32":
                case "Single": size = 4; align = 4; return true;
                case "Int64":
                case "UInt64":
                case "Double": size = 8; align = 8; return true;
                case "TypedReference": size = ptrSize * 2; align = ptrSize; return true;
                case "IntPtr":
                case "UIntPtr":
                case "String":
                case "Object": size = ptrSize; align = ptrSize; return true;
                default: size = 0; align = 0; return false;
            }
        }

        private static bool IsExplicitAdjustorThunk(byte[] textBytes, int off, int sz, uint adjustorW0, ulong va, ulong prevKeptVa)
        {
            if (sz < 8 || sz > 96 || (sz & 3) != 0 || off < 0 || off + sz > textBytes.Length)
            {
                return false;
            }

            if (sz == 8 || sz == 12)
            {
                var w0 = BitConverter.ToUInt32(textBytes, off);
                var w1 = BitConverter.ToUInt32(textBytes, off + 4);
                if (w0 == adjustorW0 && (w1 & 0xFC000000u) == 0x14000000u) return true;
            }

            if (sz == 16 || sz == 20)
            {
                var lastOff = off + sz - 8;
                var wPrev = BitConverter.ToUInt32(textBytes, lastOff);
                var wLastShort = BitConverter.ToUInt32(textBytes, lastOff + 4);
                if (wPrev == adjustorW0 && (wLastShort & 0xFFFFFC1Fu) == 0xD61F0000u) return true;
            }

            var insCount = sz >> 2;
            var wLast = BitConverter.ToUInt32(textBytes, off + sz - 4);
            var isTailBranch = (wLast & 0xFC000000u) == 0x14000000u || (wLast & 0xFFFFFC1Fu) == 0xD61F0000u;

            if (sz <= 40 && isTailBranch)
            {
                var sawAdjust = false;
                var allSimple = true;
                for (var i = 0; i < insCount - 1; i++)
                {
                    var w = BitConverter.ToUInt32(textBytes, off + i * 4);
                    if (w == adjustorW0)
                    {
                        sawAdjust = true;
                        continue;
                    }
                    if ((w & 0x9F000000u) == 0x90000000u) continue; // ADRP
                    if ((w & 0x1F800000u) == 0x12800000u) continue; // MOVZ/MOVN/MOVK
                    if ((w & 0x7FE00000u) == 0x2A000000u) continue; // ORR/MOV reg
                    if (((w & 0x1F800000u) == 0x12000000u || (w & 0x1F800000u) == 0x13000000u) && (w & 0x1Fu) != 0 && ((w >> 5) & 0x1Fu) != 0) continue; // AND imm / BFM
                    if ((w & 0x7F800000u) == 0x11000000u && ((w >> 5) & 0x1Fu) != 0) continue; // ADD imm, Rn != X0
                    if ((w & 0xBFC00000u) == 0xB9400000u && ((w >> 5) & 0x1Fu) != 0) continue; // LDR W/X [Rn,#imm], Rn != X0
                    allSimple = false;
                    break;
                }
                if (allSimple && sawAdjust)
                {
                    return true;
                }
            }

            // Stack-copy / BL+RET unboxing adjustor thunks up to 96B.
            var endsWithRet = wLast == 0xD65F03C0u;
            if (!isTailBranch && !endsWithRet)
            {
                return false;
            }

            var sawAdjExtended = false;
            var directMatchTarget = false;
            var callOrTailCount = 0;
            for (var i = 0; i < insCount; i++)
            {
                var w = BitConverter.ToUInt32(textBytes, off + i * 4);
                if (w == adjustorW0)
                {
                    sawAdjExtended = true;
                    continue;
                }
                if ((w & 0xFC000000u) == 0x14000000u || (w & 0xFC000000u) == 0x94000000u) // B / BL
                {
                    if (prevKeptVa == 0) return false;
                    var isTail = (w & 0xFC000000u) == 0x14000000u;
                    if (isTail && i != insCount - 1) return false;
                    var imm26 = (int)(w & 0x03FFFFFFu);
                    if ((imm26 & 0x02000000) != 0) imm26 -= 0x04000000;
                    var target = va + (ulong)(i * 4) + (ulong)((long)imm26 << 2);
                    if (target != prevKeptVa) return false;
                    directMatchTarget = true;
                    callOrTailCount++;
                    continue;
                }
                if ((w & 0xFFFFFC1Fu) == 0xD61F0000u || (w & 0xFFFFFC1Fu) == 0xD63F0000u) // BR / BLR
                {
                    var isBr = (w & 0xFFFFFC1Fu) == 0xD61F0000u;
                    if (isBr && i != insCount - 1) return false;
                    callOrTailCount++;
                    continue;
                }
                if (endsWithRet && i == insCount - 1) continue; // final RET
                if ((w & 0x9F000000u) == 0x90000000u || (w & 0x9F000000u) == 0x10000000u) continue; // ADRP / ADR
                if ((w & 0x1F800000u) == 0x12800000u) continue; // MOVZ/MOVN/MOVK
                if ((w & 0x7FE00000u) == 0x2A000000u) continue; // ORR/MOV reg
                if (((w & 0x1F800000u) == 0x12000000u || (w & 0x1F800000u) == 0x13000000u) && (w & 0x1Fu) != 0 && ((w >> 5) & 0x1Fu) != 0) continue; // AND imm / BFM
                if ((w & 0xFFE0FC00u) == 0x1E204000u || (w & 0xFFE0FC00u) == 0x1E604000u) continue; // FMOV S/D
                if ((w & 0x3F800000u) == 0x11000000u) // 32/64 ADD/SUB imm
                {
                    var rd = (int)(w & 0x1Fu);
                    var rn = (int)((w >> 5) & 0x1Fu);
                    if (rd == 31 || rn == 31) continue; // SP/X29 frame adjustments (ADD X29, SP, #imm / SUB SP, SP, #imm)
                    return false;
                }
                if ((w & 0x3A000000u) == 0x28000000u) // STP / LDP
                {
                    var rn = (int)((w >> 5) & 0x1Fu);
                    if (rn == 31 || rn == 29) continue;
                    return false;
                }
                if ((w & 0x3B000000u) == 0x39000000u) // STR/LDR unsigned imm (GPR & FP/SIMD)
                {
                    var rn = (int)((w >> 5) & 0x1Fu);
                    var isLoad = (w & 0x00400000u) != 0;
                    if (rn == 31 || rn == 29 || (isLoad && rn != 0)) continue;
                    return false;
                }
                if ((w & 0x3F200C00u) == 0x38000000u) // LDUR/STUR unscaled
                {
                    var rn = (int)((w >> 5) & 0x1Fu);
                    if (rn == 31 || rn == 29) continue;
                    return false;
                }
                return false;
            }

            if (!sawAdjExtended || callOrTailCount != 1)
            {
                return false;
            }
            return directMatchTarget || sz <= 68;
        }

        private static bool AreInstructionsMarshalPairEquivalent(
            byte[] textBytes,
            int offA,
            ulong vaA,
            int offB,
            ulong vaB,
            int sz,
            out int extCallCount)
        {
            extCallCount = 0;
            var insCount = sz >> 2;
            var sawLdrbDiff = false;
            var sawStrbDiff = false;
            var sawTbnz = false;
            for (var i = 0; i < insCount; i++)
            {
                var wA = BitConverter.ToUInt32(textBytes, offA + i * 4);
                var wB = BitConverter.ToUInt32(textBytes, offB + i * 4);
                var pcA = vaA + (ulong)(i * 4);
                var pcB = vaB + (ulong)(i * 4);

                if (wA == wB && (wA & 0x7F000000u) == 0x37000000u) // TBNZ once-init guard
                {
                    sawTbnz = true;
                }

                if ((wA & 0xFC000000u) == 0x94000000u && (wB & 0xFC000000u) == 0x94000000u) // BL
                {
                    var immA = (int)(wA & 0x03FFFFFFu);
                    if ((immA & 0x02000000) != 0) immA -= 0x04000000;
                    var immB = (int)(wB & 0x03FFFFFFu);
                    if ((immB & 0x02000000) != 0) immB -= 0x04000000;
                    if (pcA + (ulong)((long)immA << 2) != pcB + (ulong)((long)immB << 2))
                    {
                        return false;
                    }
                    extCallCount++;
                    continue;
                }

                if ((wA & 0xFC000000u) == 0x14000000u && (wB & 0xFC000000u) == 0x14000000u) // B
                {
                    var immA = (int)(wA & 0x03FFFFFFu);
                    if ((immA & 0x02000000) != 0) immA -= 0x04000000;
                    var immB = (int)(wB & 0x03FFFFFFu);
                    if ((immB & 0x02000000) != 0) immB -= 0x04000000;
                    var tgtA = pcA + (ulong)((long)immA << 2);
                    var tgtB = pcB + (ulong)((long)immB << 2);
                    var inA = tgtA >= vaA && tgtA < vaA + (ulong)sz;
                    var inB = tgtB >= vaB && tgtB < vaB + (ulong)sz;
                    if (inA && inB)
                    {
                        if (wA != wB) return false;
                    }
                    else if (tgtA != tgtB)
                    {
                        return false;
                    }
                    else
                    {
                        extCallCount++;
                    }
                    continue;
                }

                if ((wA & 0x9F000000u) == 0x90000000u && (wB & 0x9F000000u) == 0x90000000u) // ADRP
                {
                    if ((wA & 0x1Fu) != (wB & 0x1Fu)) return false;
                    continue;
                }

                if ((wA & 0x9F000000u) == 0x10000000u && (wB & 0x9F000000u) == 0x10000000u) // ADR
                {
                    if ((wA & 0x1Fu) != (wB & 0x1Fu)) return false;
                    continue;
                }

                if (wA != wB)
                {
                    // Allow paired adjacent once-init byte flag accesses (LDRB/STRB with imm12 delta <= 16) guarded by TBNZ.
                    if ((wA & 0xFFC003FFu) == (wB & 0xFFC003FFu))
                    {
                        var op = wA & 0xFFC00000u;
                        if (op == 0x39400000u || op == 0x39000000u)
                        {
                            var immA = (int)((wA >> 10) & 0xFFFu);
                            var immB = (int)((wB >> 10) & 0xFFFu);
                            if (Math.Abs(immA - immB) <= 16)
                            {
                                if (op == 0x39400000u) sawLdrbDiff = true;
                                else sawStrbDiff = true;
                                continue;
                            }
                        }
                    }
                    return false;
                }
            }
            if ((sawLdrbDiff || sawStrbDiff) && !(sawLdrbDiff && sawStrbDiff && sawTbnz))
            {
                return false;
            }
            return true;
        }

        private static bool TryMatchSilentMarshalSixPack(
            ulong[] allFuncs,
            int k,
            ulong textVa,
            ulong textEnd,
            byte[] textBytes,
            HashSet<ulong> r0Set,
            bool hasR0Filter)
        {
            if (k + 5 >= allFuncs.Length)
            {
                return false;
            }

            Span<ulong> vas = stackalloc ulong[6];
            Span<int> szs = stackalloc int[6];
            Span<int> offs = stackalloc int[6];
            for (var i = 0; i < 6; i++)
            {
                var fva = allFuncs[k + i];
                if (hasR0Filter && !r0Set.Contains(fva))
                {
                    return false;
                }
                var fsz = ((k + i + 1 < allFuncs.Length) ? allFuncs[k + i + 1] : textEnd) - fva;
                if (fsz < 4 || fsz > 320 || (fsz & 3) != 0)
                {
                    return false;
                }
                var foff = (int)(fva - textVa);
                if (foff < 0 || foff + (int)fsz > textBytes.Length)
                {
                    return false;
                }
                vas[i] = fva;
                szs[i] = (int)fsz;
                offs[i] = foff;
            }

            if (szs[0] != szs[3] || szs[1] != szs[4] || szs[2] != szs[5])
            {
                return false;
            }
            if (szs[0] == szs[1] && szs[1] == szs[2])
            {
                return false;
            }

            var totalCalls = 0;
            for (var p = 0; p < 3; p++)
            {
                if (!AreInstructionsMarshalPairEquivalent(
                    textBytes, offs[p], vas[p], offs[p + 3], vas[p + 3], szs[p], out var extCalls))
                {
                    return false;
                }
                totalCalls += extCalls;
            }
            return totalCalls >= 1;
        }

        private static ulong[] PreFilterFunctionStarts(
            ulong[] allFuncs,
            HashSet<ulong> r0Set,
            ulong objHdrSize,
            Macho64 macho,
            byte[] textBytes,
            ulong textVa,
            ulong textSize,
            int numImgs,
            int[] imgRank,
            HashSet<ulong> marshalAllCstrs,
            Dictionary<ulong, (int imgIdx, int firstSeq)> marshalAnchors,
            Dictionary<string, List<DelegateInfo>> delegateP0Map,
            Dictionary<ulong, string> p0CstrMap,
            HashSet<ulong> p0CstrPages,
            HashSet<ulong> delThisCstrVas,
            HashSet<ulong> lStrVas,
            HashSet<ulong> lStrPages,
            out Dictionary<ulong, int>[] marshalLocalByImg,
            out Dictionary<ulong, CstrTag> funcGlobalAnchors,
            out Dictionary<ulong, List<CstrTag>> delMultiFuncMap,
            out HashSet<ulong> excludedClusterVas,
            out int[] funcSizesFiltered,
            out bool[] hasExplicitAdjFiltered)
        {
            var adjustorW0 = 0x91000000u + (uint)(objHdrSize << 10);
            var filtered = new List<ulong>(allFuncs.Length);
            var filteredSizes = new List<int>(allFuncs.Length);
            var explicitAdj = new List<bool>(allFuncs.Length);
            var n = allFuncs.Length;
            var hasR0Filter = r0Set != null && r0Set.Count > n / 10;
            var textEnd = textVa + textSize;
            marshalLocalByImg = new Dictionary<ulong, int>[numImgs];
            funcGlobalAnchors = new Dictionary<ulong, CstrTag>(1024);
            delMultiFuncMap = new Dictionary<ulong, List<CstrTag>>(256);
            excludedClusterVas = new HashSet<ulong>(2048);

            HashSet<ulong> marshalPages = null;
            if (marshalAllCstrs != null && marshalAllCstrs.Count > 0)
            {
                marshalPages = new HashSet<ulong>(marshalAllCstrs.Count);
                foreach (var mva in marshalAllCstrs)
                {
                    marshalPages.Add(mva & ~0xFFFuL);
                }
            }

            var hasPendingMarshal = false;
            var pendingValid = false;
            var pendingImgIdx = -1;
            var pendingSeq = -1;
            var mRegs = new ulong[32];
            var mRegValid = new bool[32];

            for (var k = 0; k < n; k++)
            {
                var va = allFuncs[k];
                var sz = (k + 1 < n) ? (allFuncs[k + 1] - va) : (textEnd - va);
                var off = (int)(va - textVa);

                // Exclude P/Invoke struct marshal exception helpers ("Cannot marshal field '...'") and trailing 4-byte RET stubs.
                if (marshalPages != null && sz == 28 && off >= 0 && off + 28 <= textBytes.Length)
                {
                    if (TryFindFirstPageAddTarget(
                        textBytes, off, 7, va, marshalPages, marshalAllCstrs, (Dictionary<ulong, int>)null, mRegs, mRegValid,
                        out var matchedCstr, out _))
                    {
                        hasPendingMarshal = true;
                        if (marshalAnchors != null && marshalAnchors.TryGetValue(matchedCstr, out var mInfo))
                        {
                            pendingValid = true;
                            pendingImgIdx = mInfo.imgIdx;
                            pendingSeq = mInfo.firstSeq;
                        }
                        else
                        {
                            pendingValid = false;
                        }
                        if (k + 1 < n)
                        {
                            var retVa = allFuncs[k + 1];
                            var retSz = (k + 2 < n ? allFuncs[k + 2] : textEnd) - retVa;
                            var retOff = (int)(retVa - textVa);
                            if (retSz == 4 && retOff >= 0 && retOff + 4 <= textBytes.Length &&
                                BitConverter.ToUInt32(textBytes, retOff) == 0xD65F03C0u)
                            {
                                k++;
                            }
                        }
                        continue;
                    }
                }

                // Exclude explicit ARM64 unboxing AdjustorThunks (ADD X0, X0, #objHdrSize + tail/BL call up to 96 bytes).
                var prevKeptVa = filtered.Count > 0 ? filtered[^1] : 0ul;
                if (sz <= 96 && IsExplicitAdjustorThunk(textBytes, off, (int)sz, adjustorW0, va, prevKeptVa))
                {
                    if (explicitAdj.Count > 0)
                    {
                        explicitAdj[^1] = true;
                    }
                    hasPendingMarshal = false;
                    continue;
                }

                // Exclude mirrored [A,B,C,A,B,C] struct-marshal 6-packs lacking "Cannot marshal field" strings.
                if (TryMatchSilentMarshalSixPack(allFuncs, k, textVa, textEnd, textBytes, r0Set, hasR0Filter))
                {
                    for (var s = 0; s < 6; s++) excludedClusterVas.Add(allFuncs[k + s]);
                    hasPendingMarshal = false;
                    k += 5;
                    continue;
                }

                // Exclude non-Run0 functions (12B cold stubs, outlined C++ helpers, veneer branches, split thunk tails).
                if (hasR0Filter && !r0Set.Contains(va))
                {
                    hasPendingMarshal = false;
                    continue;
                }

                // Exclude 12-byte non-Run0 ICF/alias trampolines jumping into __text when r0 filter is inactive.
                if (!hasR0Filter && sz == 12 && k > 0 && off >= 0 && off + 12 <= textBytes.Length)
                {
                    var w0 = BitConverter.ToUInt32(textBytes, off);
                    var w1 = BitConverter.ToUInt32(textBytes, off + 4);
                    var w2 = BitConverter.ToUInt32(textBytes, off + 8);
                    if ((w0 & 0x9F000000u) == 0x90000000u &&
                        (w1 & 0xFFC00000u) == 0xF9400000u &&
                        (w2 & 0xFFFFFC1Fu) == 0xD61F0000u)
                    {
                        var imm = (int)((((w0 >> 5) & 0x7FFFFu) << 2) | ((w0 >> 29) & 3u));
                        if ((imm & 0x100000) != 0) imm -= 0x200000;
                        var sva = (va & ~0xFFFuL) + (ulong)((long)imm << 12) + (((w1 >> 10) & 0xFFFuL) * 8ul);
                        if (TryReadUInt64AtVa(macho, sva, out var targetVa) && targetVa >= textVa && targetVa < textEnd)
                        {
                            hasPendingMarshal = false;
                            continue;
                        }
                    }
                }

                if (hasPendingMarshal)
                {
                    if (pendingValid && pendingImgIdx >= 0 && pendingSeq >= 0)
                    {
                        marshalLocalByImg[pendingImgIdx] ??= new Dictionary<ulong, int>();
                        marshalLocalByImg[pendingImgIdx].TryAdd(va, pendingSeq);
                    }
                    hasPendingMarshal = false;
                }

                filtered.Add(va);
                filteredSizes.Add((int)Math.Min(int.MaxValue, sz));
                explicitAdj.Add(false);
            }

            if (delThisCstrVas != null && delThisCstrVas.Count > 0 && filtered.Count > 0)
            {
                FilterDelegateHelpersAndClusters(
                    filtered, filteredSizes, explicitAdj, objHdrSize, textBytes, textVa, imgRank,
                    delegateP0Map, p0CstrMap, p0CstrPages, delThisCstrVas, lStrVas, lStrPages,
                    marshalLocalByImg, funcGlobalAnchors, delMultiFuncMap, excludedClusterVas);
            }

            funcSizesFiltered = filteredSizes.ToArray();
            hasExplicitAdjFiltered = explicitAdj.ToArray();
            return filtered.ToArray();
        }

        private readonly record struct DelCtorCandidate(
            int Idx,
            int PreStart,
            string ValidP0Key,
            bool HasForeignP0);

        /// <summary>
        /// Identifies DELCTOR functions referencing "Delegate to an instance method cannot have null 'this'.",
        /// strips pre-.ctor delegate helpers, removes closed-generic DelClusters completely, and emits
        /// resolved non-generic delegate .ctor global/local anchors.
        /// </summary>
        private static void FilterDelegateHelpersAndClusters(
            List<ulong> filtered,
            List<int> filteredSizes,
            List<bool> explicitAdj,
            ulong objHdrSize,
            byte[] textBytes,
            ulong textVa,
            int[] imgRank,
            Dictionary<string, List<DelegateInfo>> delegateP0Map,
            Dictionary<ulong, string> p0CstrMap,
            HashSet<ulong> p0CstrPages,
            HashSet<ulong> delThisCstrVas,
            HashSet<ulong> lStrVas,
            HashSet<ulong> lStrPages,
            Dictionary<ulong, int>[] marshalLocalByImg,
            Dictionary<ulong, CstrTag> funcGlobalAnchors,
            Dictionary<ulong, List<CstrTag>> delMultiFuncMap,
            HashSet<ulong> excludedClusterVas)
        {
            var count = filtered.Count;
            var delThisPages = new HashSet<ulong>(delThisCstrVas.Count);
            foreach (var dva in delThisCstrVas) delThisPages.Add(dva & ~0xFFFuL);

            var regs = new ulong[32];
            var regValid = new bool[32];
            var hasLStr = lStrVas != null && lStrVas.Count > 0;
            var hasP0 = p0CstrMap != null && p0CstrMap.Count > 0;

            bool HasLString(int idx)
            {
                if (!hasLStr) return false;
                var off = (int)(filtered[idx] - textVa);
                var ins = Math.Min(96, Math.Max(1, filteredSizes[idx] / 4));
                return off >= 0 && TryFindFirstPageAddTarget(
                    textBytes, off, ins, filtered[idx], lStrPages, lStrVas, (Dictionary<ulong, int>)null, regs, regValid,
                    out _, out _);
            }

            bool TryGetP0Key(int idx, out string key)
            {
                key = null;
                if (!hasP0) return false;
                var off = (int)(filtered[idx] - textVa);
                var ins = Math.Min(96, Math.Max(1, filteredSizes[idx] / 4));
                return off >= 0 && TryFindFirstPageAddTarget(
                    textBytes, off, ins, filtered[idx], p0CstrPages, (HashSet<ulong>)null, p0CstrMap, regs, regValid,
                    out _, out key);
            }

            var delCtorIndices = new List<int>(2048);
            for (var i = 0; i < count; i++)
            {
                var sz = filteredSizes[i];
                if (sz < 100 || sz > 420) continue;
                var off = (int)(filtered[i] - textVa);
                if (off < 0) continue;
                var ins = Math.Min(100, sz / 4);
                if (TryFindFirstPageAddTarget(
                    textBytes, off, ins, filtered[i], delThisPages, delThisCstrVas, (Dictionary<ulong, int>)null, regs, regValid,
                    out _, out _))
                {
                    delCtorIndices.Add(i);
                }
            }
            if (delCtorIndices.Count == 0) return;

            var cands = new List<DelCtorCandidate>(delCtorIndices.Count);
            var prevStop = 0;

            for (var d = 0; d < delCtorIndices.Count; d++)
            {
                var i = delCtorIndices[d];
                var minSafe = i;
                var limit = Math.Max(prevStop, i - 8);
                for (var j = i - 1; j >= limit; j--)
                {
                    if (filteredSizes[j] > 200 || HasLString(j)) break;
                    minSafe = j;
                }

                // Require initial ___0_<p> appearance near DELCTOR ([i-4..i-1]) before extending backward to i-8.
                string anchorP0 = null;
                var earliestP0Idx = -1;
                var nearLo = Math.Max(minSafe, i - 4);
                for (var j = i - 1; j >= nearLo; j--)
                {
                    if (TryGetP0Key(j, out var k0))
                    {
                        anchorP0 ??= k0;
                        if (k0 == anchorP0) earliestP0Idx = j;
                    }
                }
                if (anchorP0 != null)
                {
                    for (var j = nearLo - 1; j >= minSafe; j--)
                    {
                        if (TryGetP0Key(j, out var k0) && k0 == anchorP0)
                        {
                            earliestP0Idx = j;
                        }
                    }
                }

                int preStart;
                if (earliestP0Idx >= 0)
                {
                    preStart = earliestP0Idx;
                }
                else
                {
                    var earliestStub = -1;
                    for (var j = nearLo; j <= i - 1; j++)
                    {
                        var offJ = (int)(filtered[j] - textVa);
                        if (IsTinyObjHdrBranchStub(textBytes, offJ, filteredSizes[j], objHdrSize))
                        {
                            earliestStub = j;
                            break;
                        }
                    }
                    if (earliestStub >= 0)
                    {
                        preStart = earliestStub;
                        var prev = earliestStub - 1;
                        if (prev >= minSafe && filteredSizes[prev] >= 48 && filteredSizes[prev] <= 140)
                        {
                            preStart = prev;
                        }
                    }
                    else
                    {
                        preStart = i;
                    }
                }

                var hasValidNonGen = anchorP0 != null && delegateP0Map != null && delegateP0Map.ContainsKey(anchorP0);
                var hasForeignP0 = anchorP0 != null && !hasValidNonGen;
                cands.Add(new DelCtorCandidate(i, preStart, hasValidNonGen ? anchorP0 : null, hasForeignP0));

                prevStop = i + 1;
                if (i + 1 < count && (d + 1 >= delCtorIndices.Count || delCtorIndices[d + 1] > i + 1))
                {
                    var nextOff = (int)(filtered[i + 1] - textVa);
                    var nextSz = filteredSizes[i + 1];
                    if (nextSz <= 48 && !HasLString(i + 1) &&
                        (IsTinyObjHdrBranchStub(textBytes, nextOff, nextSz, objHdrSize) ||
                         EndsWithArm64BranchOrRet(textBytes, nextOff, nextSz, includeBr: true, includeRet: true)))
                    {
                        prevStop = i + 2;
                    }
                }
            }

            var exclude = new bool[count];
            var cIdx = 0;
            while (cIdx < cands.Count)
            {
                if (cands[cIdx].ValidP0Key != null)
                {
                    // Standalone non-generic delegate: strip [preStart .. i - 1], keep DELCTOR + Invoke, and emit exact anchor if unique.
                    var c = cands[cIdx];
                    for (var k = c.PreStart; k < c.Idx; k++)
                    {
                        exclude[k] = true;
                        excludedClusterVas.Add(filtered[k]);
                    }

                    if (delegateP0Map.TryGetValue(c.ValidP0Key, out var dList) && dList.Count > 0)
                    {
                        var ii0 = dList[0].ImgIdx;
                        var singleImg = true;
                        for (var t = 1; t < dList.Count; t++)
                        {
                            if (dList[t].ImgIdx != ii0) { singleImg = false; break; }
                        }
                        if (singleImg)
                        {
                            var delVa = filtered[c.Idx];
                            if (dList.Count == 1)
                            {
                                var di = dList[0];
                                funcGlobalAnchors[delVa] = new CstrTag(imgRank[ii0], ii0, 5, di.CtorMethodIdx, di.CtorSeq, true, di.TdIdx);
                                marshalLocalByImg[ii0] ??= new Dictionary<ulong, int>();
                                marshalLocalByImg[ii0].TryAdd(delVa, di.CtorSeq);
                            }
                            else
                            {
                                funcGlobalAnchors[delVa] = new CstrTag(imgRank[ii0], ii0, 3, -1, -1, false, dList[0].TdIdx);
                            }
                        }
                        else
                        {
                            var delVa = filtered[c.Idx];
                            var seenByImg = new Dictionary<int, (int firstT, int cnt)>(dList.Count);
                            for (var t = 0; t < dList.Count; t++)
                            {
                                var ii = dList[t].ImgIdx;
                                if (seenByImg.TryGetValue(ii, out var cur))
                                    seenByImg[ii] = (cur.firstT, cur.cnt + 1);
                                else
                                    seenByImg[ii] = (t, 1);
                            }
                            var multiList = new List<CstrTag>(seenByImg.Count);
                            foreach (var kv in seenByImg)
                            {
                                var di = dList[kv.Value.firstT];
                                if (kv.Value.cnt == 1)
                                {
                                    marshalLocalByImg[kv.Key] ??= new Dictionary<ulong, int>();
                                    marshalLocalByImg[kv.Key].TryAdd(delVa, di.CtorSeq);
                                    multiList.Add(new CstrTag(imgRank[kv.Key], kv.Key, 5, di.CtorMethodIdx, di.CtorSeq, true, di.TdIdx));
                                }
                                else
                                {
                                    multiList.Add(new CstrTag(imgRank[kv.Key], kv.Key, 3, -1, -1, false, di.TdIdx));
                                }
                            }
                            if (multiList.Count > 0)
                            {
                                delMultiFuncMap[delVa] = multiList;
                            }
                        }
                    }
                    cIdx++;
                    continue;
                }

                // Group consecutive non-non-generic DELCTORs spaced <= 16 functions apart.
                var runEnd = cIdx;
                var anyForeign = cands[cIdx].HasForeignP0;
                while (runEnd + 1 < cands.Count &&
                       cands[runEnd + 1].ValidP0Key == null &&
                       cands[runEnd + 1].Idx - cands[runEnd].Idx <= 16)
                {
                    runEnd++;
                    if (cands[runEnd].HasForeignP0) anyForeign = true;
                }

                var runLen = runEnd - cIdx + 1;
                if (anyForeign || runLen >= 6)
                {
                    var lastI = cands[runEnd].Idx;
                    var postEnd = lastI;
                    if (lastI + 4 < count &&
                        filteredSizes[lastI + 1] <= 64 &&
                        EndsWithArm64BranchOrRet(textBytes, (int)(filtered[lastI + 1] - textVa), filteredSizes[lastI + 1], includeBr: true, includeRet: false) &&
                        filteredSizes[lastI + 2] <= 200 && !HasLString(lastI + 2) &&
                        TryGetP0Key(lastI + 3, out var postP0) && (delegateP0Map == null || !delegateP0Map.ContainsKey(postP0)) &&
                        filteredSizes[lastI + 4] <= 80 &&
                        EndsWithArm64BranchOrRet(textBytes, (int)(filtered[lastI + 4] - textVa), filteredSizes[lastI + 4], includeBr: true, includeRet: false))
                    {
                        postEnd = lastI + 4;
                    }
                    else if (lastI + 1 < count &&
                             IsTinyObjHdrBranchStub(textBytes, (int)(filtered[lastI + 1] - textVa), filteredSizes[lastI + 1], objHdrSize))
                    {
                        postEnd = lastI + 1;
                    }

                    for (var k = cands[cIdx].PreStart; k <= postEnd; k++)
                    {
                        exclude[k] = true;
                        excludedClusterVas.Add(filtered[k]);
                    }
                }
                else
                {
                    for (var r = cIdx; r <= runEnd; r++)
                    {
                        for (var k = cands[r].PreStart; k < cands[r].Idx; k++)
                        {
                            exclude[k] = true;
                            excludedClusterVas.Add(filtered[k]);
                        }
                    }
                }
                cIdx = runEnd + 1;
            }

            var writeIdx = 0;
            for (var i = 0; i < count; i++)
            {
                if (exclude[i]) continue;
                filtered[writeIdx] = filtered[i];
                filteredSizes[writeIdx] = filteredSizes[i];
                explicitAdj[writeIdx] = explicitAdj[i];
                writeIdx++;
            }
            if (writeIdx < count)
            {
                filtered.RemoveRange(writeIdx, count - writeIdx);
                filteredSizes.RemoveRange(writeIdx, count - writeIdx);
                explicitAdj.RemoveRange(writeIdx, count - writeIdx);
            }
        }

        private static bool IsTinyObjHdrBranchStub(byte[] textBytes, int off, int sz, ulong objHdrSize)
        {
            if (sz < 8 || sz > 32 || (sz & 3) != 0 || off < 0 || off + sz > textBytes.Length)
            {
                return false;
            }
            var w0 = BitConverter.ToUInt32(textBytes, off);
            var wL = BitConverter.ToUInt32(textBytes, off + sz - 4);
            if ((w0 & 0xFFC003E0u) != 0xF9400000u || (wL & 0xFFFFFC1Fu) != 0xD61F0000u)
            {
                return false;
            }
            var imm = ((w0 >> 10) & 0xFFFuL) * 8ul;
            return imm >= objHdrSize && imm <= objHdrSize + 48ul;
        }

        private static bool EndsWithArm64BranchOrRet(byte[] textBytes, int off, int sz, bool includeBr, bool includeRet)
        {
            if (sz < 4 || (sz & 3) != 0 || off < 0 || off + sz > textBytes.Length)
            {
                return false;
            }
            var wL = BitConverter.ToUInt32(textBytes, off + sz - 4);
            if (includeBr && (wL & 0xFFFFFC1Fu) == 0xD61F0000u) return true;
            if (includeRet && wL == 0xD65F03C0u) return true;
            return false;
        }

        /// <summary>
        /// Scans an instruction window for the first ARM64 ADRP + ADD immediate sequence referencing a target VA set or map.
        /// </summary>
        private static bool TryFindFirstPageAddTarget<TVal>(
            byte[] textBytes,
            int textOff,
            int insCount,
            ulong startVa,
            HashSet<ulong> targetPages,
            HashSet<ulong> targetSet,
            Dictionary<ulong, TVal> targetMap,
            ulong[] regs,
            bool[] regValid,
            out ulong matchedVa,
            out TVal matchedValue)
        {
            Array.Clear(regValid, 0, 32);
            var cur = startVa;
            for (var wIdx = 0; wIdx < insCount && textOff + (wIdx + 1) * 4 <= textBytes.Length; wIdx++)
            {
                var w = BitConverter.ToUInt32(textBytes, textOff + wIdx * 4);
                if ((w & 0x9F000000u) == 0x90000000u) // ADRP
                {
                    var rd = (int)(w & 0x1Fu);
                    var imm = (int)((((w >> 5) & 0x7FFFFu) << 2) | ((w >> 29) & 3u));
                    if ((imm & 0x100000) != 0) imm -= 0x200000;
                    var pg = (cur & ~0xFFFuL) + (ulong)((long)imm << 12);
                    if (rd != 31 && targetPages.Contains(pg))
                    {
                        regs[rd] = pg;
                        regValid[rd] = true;
                    }
                    else if (rd != 31)
                    {
                        regValid[rd] = false;
                    }
                }
                else if ((w & 0xFF800000u) == 0x91000000u) // ADD imm
                {
                    var rd = (int)(w & 0x1Fu);
                    var rn = (int)((w >> 5) & 0x1Fu);
                    if (rn != 31 && regValid[rn])
                    {
                        var addImm = ((w >> 10) & 0xFFFuL) << (((w >> 22) & 1u) != 0 ? 12 : 0);
                        var target = regs[rn] + addImm;
                        if (targetSet != null && targetSet.Contains(target))
                        {
                            matchedVa = target;
                            matchedValue = default;
                            return true;
                        }
                        if (targetMap != null && targetMap.TryGetValue(target, out matchedValue))
                        {
                            matchedVa = target;
                            return true;
                        }
                    }
                    if (rd != 31)
                    {
                        regValid[rd] = false;
                    }
                }
                else if ((w & 0x9F000000u) == 0x10000000u || // ADR
                         (w & 0x3B000000u) == 0x18000000u || // LDR literal
                         (w & 0x3B400000u) == 0x39400000u || // LDR/LDRB/LDRH unsigned imm
                         (w & 0x1F800000u) == 0x12800000u || // MOVN/MOVZ/MOVK
                         (w & 0x7FE00000u) == 0x2A000000u || // ORR/MOV reg
                         (w & 0x7F800000u) == 0x51000000u || // SUB imm
                         (w & 0xFF800000u) == 0x11000000u)   // 32-bit ADD imm
                {
                    var rd = (int)(w & 0x1Fu);
                    if (rd != 31)
                    {
                        regValid[rd] = false;
                    }
                }
                cur += 4;
            }
            matchedVa = 0;
            matchedValue = default;
            return false;
        }

        private static bool TryReadUInt64AtVa(Macho64 macho, ulong va, out ulong value)
        {
            value = 0;
            if (!macho.TryMapVATR(va, out var fileOff) || fileOff + 8 > macho.Length)
            {
                return false;
            }
            macho.Position = fileOff;
            value = macho.ReadUInt64();
            return true;
        }

        private static List<(int funcRelIdx, int seq)> StrictLongestIncreasingChain(List<(int funcRelIdx, int seq)> hits)
        {
            if (hits.Count == 0) return hits;
            // Deduplicate per funcRelIdx keeping distinct seq hits ordered by (funcRelIdx, seq), enforcing strict increase in BOTH axes.
            hits.Sort((a, b) =>
            {
                var c = a.funcRelIdx.CompareTo(b.funcRelIdx);
                return c != 0 ? c : a.seq.CompareTo(b.seq);
            });

            // Standard strict LIS over seq while filtering multiple hits on same funcRelIdx cleanly by iterating descending seq per funcRelIdx.
            var dpVals = new List<int>(hits.Count);
            var dpHitIdx = new List<int>(hits.Count);
            var parent = new int[hits.Count];
            Array.Fill(parent, -1);

            var i = 0;
            while (i < hits.Count)
            {
                var j = i;
                while (j < hits.Count && hits[j].funcRelIdx == hits[i].funcRelIdx) j++;

                // Process strictly unique funcRelIdx group in reverse seq so two hits in the same function cannot chain together.
                for (var idx = j - 1; idx >= i; idx--)
                {
                    var seq = hits[idx].seq;
                    var pos = LowerBoundList(dpVals, seq);
                    parent[idx] = pos > 0 ? dpHitIdx[pos - 1] : -1;
                    if (pos == dpVals.Count)
                    {
                        dpVals.Add(seq);
                        dpHitIdx.Add(idx);
                    }
                    else
                    {
                        dpVals[pos] = seq;
                        dpHitIdx[pos] = idx;
                    }
                }
                i = j;
            }

            var result = new List<(int, int)>(dpHitIdx.Count);
            if (dpHitIdx.Count > 0)
            {
                var cur = dpHitIdx[^1];
                while (cur != -1)
                {
                    result.Add(hits[cur]);
                    cur = parent[cur];
                }
                result.Reverse();
            }
            return result;
        }

        private static List<List<(int funcRelIdx, int seq)>> ExtractMonotoneChunks(List<(int funcRelIdx, int seq)> hits)
        {
            var chunks = new List<List<(int funcRelIdx, int seq)>>();
            if (hits == null || hits.Count == 0)
            {
                return chunks;
            }

            var sortedHits = new List<(int funcRelIdx, int seq)>(hits);
            sortedHits.Sort((a, b) =>
            {
                var c = a.funcRelIdx.CompareTo(b.funcRelIdx);
                return c != 0 ? c : a.seq.CompareTo(b.seq);
            });

            var primary = StrictLongestIncreasingChain(new List<(int funcRelIdx, int seq)>(sortedHits));
            if (primary.Count == 0)
            {
                return chunks;
            }
            chunks.Add(primary);

            var secondarySeqSpans = new List<(int sMin, int sMax)>();

            bool IsInsideSecondarySpan(int s)
            {
                foreach (var (eMin, eMax) in secondarySeqSpans)
                {
                    if (s >= eMin && s <= eMax) return true;
                }
                return false;
            }

            bool IsAcceptableCandidate(List<(int funcRelIdx, int seq)> cand)
            {
                if (cand == null || cand.Count < 2) return false;
                var dS = cand[^1].seq - cand[0].seq;
                if (cand.Count >= 3)
                {
                    return dS >= 8 || cand.Count >= 4;
                }
                var dF = cand[1].funcRelIdx - cand[0].funcRelIdx;
                return dS >= 15 && dS <= 2000 && dF >= 10 && Math.Max(dF, dS) <= 3 * Math.Min(dF, dS);
            }

            bool TryEvictPrimaryOutlier(int minCandHits)
            {
                if (chunks[0].Count < 16) return false;
                var secSeqs = new List<int>(128);
                var secSeqSet = new HashSet<int>(128);
                for (var c = 1; c < chunks.Count; c++)
                {
                    foreach (var (_, sq) in chunks[c])
                    {
                        if (secSeqSet.Add(sq)) secSeqs.Add(sq);
                    }
                }
                secSeqs.Sort();

                var primarySeqs = new List<int>(chunks[0].Count);
                var primarySeqSet = new HashSet<int>(chunks[0].Count);
                foreach (var (_, sq) in chunks[0])
                {
                    primarySeqs.Add(sq);
                    primarySeqSet.Add(sq);
                }

                var allPinnedF = new List<int>(256);
                foreach (var ch in chunks)
                {
                    foreach (var (fr, _) in ch) allPinnedF.Add(fr);
                }
                allPinnedF.Sort();

                List<(int funcRelIdx, int seq)> bestEvictCand = null;
                List<int> bestEvictPrimaryIdx = null;
                var hIdx = 0;
                var secBuckets = new Dictionary<int, List<(int funcRelIdx, int seq)>>();
                var pBuckets = new Dictionary<int, List<(int funcRelIdx, int seq)>>();

                void ConsiderCandidate(List<(int funcRelIdx, int seq)> cand)
                {
                    if (cand.Count < minCandHits || !IsAcceptableCandidate(cand)) return;
                    var cS0 = cand[0].seq;
                    var cS1 = cand[^1].seq;
                    var conflicts = new List<int>(4);
                    for (var pi = 0; pi < chunks[0].Count; pi++)
                    {
                        var ps = chunks[0][pi].seq;
                        if (ps >= cS0 && ps <= cS1)
                        {
                            conflicts.Add(pi);
                            if (conflicts.Count > 2) break;
                        }
                    }
                    if (conflicts.Count == 0 || conflicts.Count > 2) return;
                    if (cand.Count < Math.Max(minCandHits, conflicts.Count * 8)) return;
                    if (chunks[0].Count - conflicts.Count < 8) return;
                    if (bestEvictCand == null || cand.Count > bestEvictCand.Count)
                    {
                        bestEvictCand = cand;
                        bestEvictPrimaryIdx = conflicts;
                    }
                }

                for (var pfIdx = 0; pfIdx <= allPinnedF.Count; pfIdx++)
                {
                    var fHi = pfIdx < allPinnedF.Count ? allPinnedF[pfIdx] : int.MaxValue;
                    var fLo = pfIdx > 0 ? allPinnedF[pfIdx - 1] : int.MinValue;
                    while (hIdx < sortedHits.Count && sortedHits[hIdx].funcRelIdx <= fLo) hIdx++;
                    var spanStart = hIdx;
                    while (hIdx < sortedHits.Count && sortedHits[hIdx].funcRelIdx < fHi) hIdx++;
                    if (hIdx - spanStart < minCandHits) continue;

                    secBuckets.Clear();
                    for (var hi = spanStart; hi < hIdx; hi++)
                    {
                        var h = sortedHits[hi];
                        if (secSeqSet.Contains(h.seq) || primarySeqSet.Contains(h.seq) || IsInsideSecondarySpan(h.seq)) continue;
                        var mb = LowerBoundList(secSeqs, h.seq);
                        if (!secBuckets.TryGetValue(mb, out var bucket))
                        {
                            bucket = new List<(int funcRelIdx, int seq)>(16);
                            secBuckets[mb] = bucket;
                        }
                        bucket.Add(h);
                    }

                    foreach (var bucket in secBuckets.Values)
                    {
                        if (bucket.Count < minCandHits) continue;

                        // First try the whole secondary bucket directly.
                        ConsiderCandidate(StrictLongestIncreasingChain(bucket));

                        // Partition by primary chunks[0] M-gaps and merge adjacent M-buckets spanning 1..2 primary outliers,
                        // preventing an unrelated earlier/later hit in the same F-gap from inflating conflict counts.
                        pBuckets.Clear();
                        foreach (var h in bucket)
                        {
                            var pmb = LowerBoundList(primarySeqs, h.seq);
                            if (!pBuckets.TryGetValue(pmb, out var pb))
                            {
                                pb = new List<(int funcRelIdx, int seq)>(8);
                                pBuckets[pmb] = pb;
                            }
                            pb.Add(h);
                        }
                        if (pBuckets.Count < 2) continue;

                        var pKeys = new List<int>(pBuckets.Keys);
                        pKeys.Sort();
                        for (var a = 0; a < pKeys.Count; a++)
                        {
                            for (var b = a + 1; b < pKeys.Count && pKeys[b] - pKeys[a] <= 2; b++)
                            {
                                var total = 0;
                                for (var k = a; k <= b; k++) total += pBuckets[pKeys[k]].Count;
                                if (total < minCandHits) continue;

                                var merged = new List<(int funcRelIdx, int seq)>(total);
                                for (var k = a; k <= b; k++) merged.AddRange(pBuckets[pKeys[k]]);
                                merged.Sort((x, y) =>
                                {
                                    var c = x.funcRelIdx.CompareTo(y.funcRelIdx);
                                    return c != 0 ? c : x.seq.CompareTo(y.seq);
                                });
                                ConsiderCandidate(StrictLongestIncreasingChain(merged));
                            }
                        }
                    }
                }

                if (bestEvictCand == null) return false;
                for (var ei = bestEvictPrimaryIdx.Count - 1; ei >= 0; ei--)
                {
                    chunks[0].RemoveAt(bestEvictPrimaryIdx[ei]);
                }
                chunks.Add(bestEvictCand);
                secondarySeqSpans.Add((bestEvictCand[0].seq, bestEvictCand[^1].seq));
                return true;
            }

            // First evict rare 1..2 primary outlier hits blocking a major (>=16-hit) unsplit interior monotone chunk.
            for (var pre = 0; pre < 4; pre++)
            {
                if (!TryEvictPrimaryOutlier(16)) break;
            }

            // Outer pass allows fallback eviction (>=8-hit) after conflict-free extraction finishes.
            for (var evictPass = 0; evictPass < 4; evictPass++)
            {
                // Inner loop extracts conflict-free secondary chunks sitting in open F-intervals between ANY pinned anchors.
                for (var iter = 0; iter < 128; iter++)
                {
                    var pinnedF = new List<int>(256);
                    var takenSeqsSet = new HashSet<int>(512);
                    var takenSeqs = new List<int>(512);
                    foreach (var ch in chunks)
                    {
                        foreach (var (fr, sq) in ch)
                        {
                            pinnedF.Add(fr);
                            if (takenSeqsSet.Add(sq)) takenSeqs.Add(sq);
                        }
                    }
                    pinnedF.Sort();
                    takenSeqs.Sort();

                    List<(int funcRelIdx, int seq)> bestCand = null;
                    var hitIdx = 0;
                    var hitCount = sortedHits.Count;
                    var mBuckets = new Dictionary<int, List<(int funcRelIdx, int seq)>>();

                    for (var pfIdx = 0; pfIdx <= pinnedF.Count; pfIdx++)
                    {
                        var fHi = pfIdx < pinnedF.Count ? pinnedF[pfIdx] : int.MaxValue;
                        var fLo = pfIdx > 0 ? pinnedF[pfIdx - 1] : int.MinValue;
                        if (pfIdx > 0 && fHi <= fLo + 1)
                        {
                            while (hitIdx < hitCount && sortedHits[hitIdx].funcRelIdx <= fHi) hitIdx++;
                            continue;
                        }
                        while (hitIdx < hitCount && sortedHits[hitIdx].funcRelIdx <= fLo) hitIdx++;
                        var spanStart = hitIdx;
                        while (hitIdx < hitCount && sortedHits[hitIdx].funcRelIdx < fHi) hitIdx++;
                        if (hitIdx - spanStart < 2) continue;

                        mBuckets.Clear();
                        for (var hi = spanStart; hi < hitIdx; hi++)
                        {
                            var h = sortedHits[hi];
                            if (takenSeqsSet.Contains(h.seq) || IsInsideSecondarySpan(h.seq)) continue;
                            var mb = LowerBoundList(takenSeqs, h.seq);
                            if (!mBuckets.TryGetValue(mb, out var bucket))
                            {
                                bucket = new List<(int funcRelIdx, int seq)>(8);
                                mBuckets[mb] = bucket;
                            }
                            bucket.Add(h);
                        }

                        foreach (var bucket in mBuckets.Values)
                        {
                            if (bucket.Count < 2) continue;
                            var cand = StrictLongestIncreasingChain(bucket);
                            if (!IsAcceptableCandidate(cand)) continue;
                            if (bestCand == null || cand.Count > bestCand.Count ||
                                (cand.Count == bestCand.Count && (cand[^1].seq - cand[0].seq) > (bestCand[^1].seq - bestCand[0].seq)))
                            {
                                bestCand = cand;
                            }
                        }
                    }

                    if (bestCand == null)
                    {
                        break;
                    }
                    chunks.Add(bestCand);
                    secondarySeqSpans.Add((bestCand[0].seq, bestCand[^1].seq));
                }

                if (!TryEvictPrimaryOutlier(8)) break;
            }

            return chunks;
        }

        private static bool IsInlinedAdjustorClone(
            byte[] textBytes,
            ulong textVa,
            ulong va1,
            int sz1,
            ulong va2,
            int sz2,
            ulong objHdrSize)
        {
            if (sz1 != sz2 || sz1 < 8 || sz1 > 256 || (sz1 & 3) != 0)
            {
                return false;
            }
            var off1 = (long)(va1 - textVa);
            var off2 = (long)(va2 - textVa);
            if (off1 < 0 || off2 < 0 || off1 + sz1 > textBytes.Length || off2 + sz2 > textBytes.Length)
            {
                return false;
            }

            var insCount = sz1 >> 2;
            var offDiff = 0;
            var hdrInt = (int)objHdrSize;
            var hdrUint = (uint)objHdrSize;

            for (var k = 0; k < insCount; k++)
            {
                var a = BitConverter.ToUInt32(textBytes, (int)off1 + k * 4);
                var b = BitConverter.ToUInt32(textBytes, (int)off2 + k * 4);
                if (a == b) continue;

                // B / BL branching to the exact same absolute VA
                if ((a & 0xFC000000u) == (b & 0xFC000000u) && ((a & 0xFC000000u) == 0x14000000u || (a & 0xFC000000u) == 0x94000000u))
                {
                    var ia = (int)(a & 0x03FFFFFFu);
                    if ((ia & 0x02000000) != 0) ia -= 0x04000000;
                    var ib = (int)(b & 0x03FFFFFFu);
                    if ((ib & 0x02000000) != 0) ib -= 0x04000000;
                    if ((long)va1 + k * 4 + (long)ia * 4 == (long)va2 + k * 4 + (long)ib * 4) continue;
                }

                // Scaled unsigned-imm12 LDR/STR (including scalar/vector SIMD V=1)
                if ((a & 0xFFC003FFu) == (b & 0xFFC003FFu) && (a & 0x3B000000u) == 0x39000000u)
                {
                    var sizeLog = (a >> 30) & 3u;
                    var isV = ((a >> 26) & 1u) != 0;
                    var opcHi = ((a >> 23) & 1u) != 0;
                    var scale = isV && opcHi && sizeLog == 0 ? 4 : (int)sizeLog;
                    var step = hdrUint >> scale;
                    if (step > 0)
                    {
                        var ia = (a >> 10) & 0xFFFu;
                        var ib = (b >> 10) & 0xFFFu;
                        if (ib == ia + step) { offDiff++; continue; }
                    }
                }

                // LDP / STP signed 7-bit offset pair
                if ((a & 0xFFE07FFFu) == (b & 0xFFE07FFFu) && (a & 0x3A000000u) == 0x28000000u)
                {
                    var opc = (int)((a >> 30) & 3u);
                    var isV = ((a >> 26) & 1u) != 0;
                    var scale = isV ? (2 + opc) : (opc >= 2 ? 3 : 2);
                    var step = hdrInt >> scale;
                    if (step > 0)
                    {
                        var ia = (int)((a >> 15) & 0x7Fu);
                        if ((ia & 0x40) != 0) ia -= 0x80;
                        var ib = (int)((b >> 15) & 0x7Fu);
                        if ((ib & 0x40) != 0) ib -= 0x80;
                        if (ib == ia + step) { offDiff++; continue; }
                    }
                }

                // LDUR / STUR unscaled 9-bit offset
                if ((a & 0xFFE00FFFu) == (b & 0xFFE00FFFu) && (a & 0x3B200C00u) == 0x38000000u)
                {
                    var ia = (int)((a >> 12) & 0x1FFu);
                    if ((ia & 0x100) != 0) ia -= 0x200;
                    var ib = (int)((b >> 12) & 0x1FFu);
                    if ((ib & 0x100) != 0) ib -= 0x200;
                    if (ib == ia + hdrInt) { offDiff++; continue; }
                }

                // ADD Xd, Xn, #imm12
                if ((a & 0xFFC003FFu) == (b & 0xFFC003FFu) && (a & 0xFFC00000u) == 0x91000000u)
                {
                    var ia = (a >> 10) & 0xFFFu;
                    var ib = (b >> 10) & 0xFFFu;
                    if (ib == ia + hdrUint) { offDiff++; continue; }
                }

                return false;
            }

            return offDiff >= 1;
        }

        /// <summary>
        /// Checks if a tiny ARM64 function starts with a pure tailcall stub (ending at the first BR/B without calls/RET)
        /// that zeroes an unread argument GPR X0..X7 (e.g. MOV Xr, #0 for MethodInfo* = NULL), returning the highest
        /// such zeroed register index or -1.
        /// </summary>
        private static int TryGetTailcallZeroedGprReg(byte[] textBytes, int textOff, int size)
        {
            if (size < 8 || size > 64 || (size & 3) != 0 || textOff < 0 || textOff + size > textBytes.Length)
            {
                return -1;
            }
            var insLimit = size / 4;
            uint readMask = 0;
            uint writtenMask = 0;
            var maxZeroGpr = -1;
            for (var i = 0; i < insLimit; i++)
            {
                var w = BitConverter.ToUInt32(textBytes, textOff + i * 4);
                // First unconditional tail branch stops scan cleanly (even if dead fused stubs follow).
                if ((w & 0xFFFFFC1Fu) == 0xD61F0000u)
                {
                    var rn = (int)((w >> 5) & 0x1Fu);
                    if (rn < 31 && (writtenMask & (1u << rn)) == 0) readMask |= 1u << rn;
                    return maxZeroGpr;
                }
                if ((w & 0xFC000000u) == 0x14000000u)
                {
                    return maxZeroGpr;
                }
                // Disallow RET, BL, BLR, or conditional/compare branches inside pure tailcall stubs.
                if (w == 0xD65F03C0u ||
                    (w & 0xFC000000u) == 0x94000000u ||
                    (w & 0xFFFFFC1Fu) == 0xD63F0000u ||
                    (w & 0xFE000000u) == 0x54000000u ||
                    (w & 0x7E000000u) == 0x34000000u ||
                    (w & 0x7E000000u) == 0x36000000u)
                {
                    return -1;
                }
                // ADRP Xd, imm
                if ((w & 0x9F000000u) == 0x90000000u)
                {
                    var rd = (int)(w & 0x1Fu);
                    if (rd < 31) writtenMask |= 1u << rd;
                    continue;
                }
                // ADD Xd/Wd, Xn/Wn, #imm
                if ((w & 0x7F800000u) == 0x11000000u)
                {
                    var rd = (int)(w & 0x1Fu);
                    var rn = (int)((w >> 5) & 0x1Fu);
                    if (rn < 31 && (writtenMask & (1u << rn)) == 0) readMask |= 1u << rn;
                    if (rd < 31) writtenMask |= 1u << rd;
                    continue;
                }
                // LDR Xt/Wt, [Xn, #imm] (unsigned offset)
                if ((w & 0xBFC00000u) == 0xB9400000u)
                {
                    var rt = (int)(w & 0x1Fu);
                    var rn = (int)((w >> 5) & 0x1Fu);
                    if (rn < 31 && (writtenMask & (1u << rn)) == 0) readMask |= 1u << rn;
                    if (rt < 31) writtenMask |= 1u << rt;
                    continue;
                }
                // MOVZ Xd/Wd, #0
                if ((w & 0x7FFFFFE0u) == 0x52800000u)
                {
                    var rd = (int)(w & 0x1Fu);
                    if (rd <= 7 && (readMask & (1u << rd)) == 0)
                    {
                        maxZeroGpr = Math.Max(maxZeroGpr, rd);
                    }
                    if (rd < 31) writtenMask |= 1u << rd;
                    continue;
                }
                // MOV Xd, Xm / ORR Xd, Xn, Xm
                if ((w & 0x7FE00000u) == 0x2A000000u)
                {
                    var rd = (int)(w & 0x1Fu);
                    var rn = (int)((w >> 5) & 0x1Fu);
                    var rm = (int)((w >> 16) & 0x1Fu);
                    if (rn < 31 && (writtenMask & (1u << rn)) == 0) readMask |= 1u << rn;
                    if (rm < 31 && (writtenMask & (1u << rm)) == 0) readMask |= 1u << rm;
                    if (rn == 31 && rm == 31 && rd <= 7 && (readMask & (1u << rd)) == 0)
                    {
                        maxZeroGpr = Math.Max(maxZeroGpr, rd);
                    }
                    if (rd < 31) writtenMask |= 1u << rd;
                    continue;
                }
                // Unknown instruction inside stub -> bail conservatively.
                return -1;
            }
            return -1;
        }

        private static void FillMethodsFromChunks(
            ulong[] allFuncsFiltered,
            int[] funcSizesFiltered,
            bool[] hasExplicitAdjFiltered,
            int fIdx0,
            int fCount,
            List<(int tdIdx, int methodIdx)> methodsSeq,
            List<List<(int funcRelIdx, int seq)>> chunks,
            Il2CppMethodDefinition[] mts,
            bool[] vtInstArr,
            ulong[] modPtrs,
            byte[] textBytes,
            ulong textVa,
            ulong objHdrSize)
        {
            var mCount = methodsSeq.Count;
            if (fCount <= 0 || mCount <= 0)
            {
                return;
            }

            void AssignMethodVa(int seq, int relFuncIdx)
            {
                var va = allFuncsFiltered[fIdx0 + relFuncIdx];
                var mi = methodsSeq[seq].methodIdx;
                var rid = mts[mi].token & 0x00FFFFFFu;
                if (rid >= 1 && rid <= modPtrs.Length)
                {
                    modPtrs[rid - 1] = va;
                }
            }

            void FillSubproblem(
                List<int> subFIndices,
                List<int> subMSeqs,
                List<(int posF, int posM)> subAnchors)
            {
                if (subFIndices.Count == 0 || subMSeqs.Count == 0)
                {
                    return;
                }

                var segStartsF = -1;
                var segStartsM = -1;
                var candFs = new List<int>(64);

                for (var cIdx = 0; cIdx <= subAnchors.Count; cIdx++)
                {
                    int nextF, nextM;
                    if (cIdx < subAnchors.Count)
                    {
                        nextF = subAnchors[cIdx].posF;
                        nextM = subAnchors[cIdx].posM;
                        AssignMethodVa(subMSeqs[nextM], subFIndices[nextF]);
                    }
                    else
                    {
                        nextF = subFIndices.Count;
                        nextM = subMSeqs.Count;
                    }

                    var dm = nextM - segStartsM - 1;
                    var df = nextF - segStartsF - 1;
                    if (dm > 0)
                    {
                        if (df <= 0)
                        {
                            var fallbackF = segStartsF >= 0
                                ? subFIndices[segStartsF]
                                : (nextF < subFIndices.Count ? subFIndices[nextF] : subFIndices[0]);
                            for (var j = 0; j < dm; j++)
                            {
                                AssignMethodVa(subMSeqs[segStartsM + 1 + j], fallbackF);
                            }
                        }
                        else
                        {
                            candFs.Clear();
                            for (var p = segStartsF + 1; p < nextF; p++)
                            {
                                candFs.Add(subFIndices[p]);
                            }

                            // Only fold inlined ValueType adjustor clones when segment actually has excess slots and vtInst methods.
                            if (candFs.Count > dm)
                            {
                                var vtUnpaired = 0;
                                for (var j = 0; j < dm; j++)
                                {
                                    var mi = methodsSeq[subMSeqs[segStartsM + 1 + j]].methodIdx;
                                    if (vtInstArr[mi]) vtUnpaired++;
                                }

                                if (vtUnpaired > 0)
                                {
                                    var maxDrop = Math.Min(candFs.Count - dm, vtUnpaired);
                                    var dropped = new List<int>(candFs.Count);
                                    var drops = 0;
                                    for (var i = 0; i < candFs.Count; i++)
                                    {
                                        var fA = candFs[i];
                                        dropped.Add(fA);
                                        if (drops < maxDrop && i + 1 < candFs.Count && !hasExplicitAdjFiltered[fIdx0 + fA])
                                        {
                                            var fB = candFs[i + 1];
                                            if (IsInlinedAdjustorClone(
                                                textBytes, textVa,
                                                allFuncsFiltered[fIdx0 + fA], funcSizesFiltered[fIdx0 + fA],
                                                allFuncsFiltered[fIdx0 + fB], funcSizesFiltered[fIdx0 + fB],
                                                objHdrSize))
                                            {
                                                drops++;
                                                i++; // skip inlined +objHdrSize clone
                                            }
                                        }
                                    }
                                    candFs = dropped;
                                }
                            }

                            // When the unanchored head before subAnchors[0] overruns a preceding image's tail by 1..6 functions,
                            // trim leading functions if ARM64 tailcall zeroing (MOV Xr, #0; BR) proves 0-param arg mismatches at t=0.
                            if (segStartsM < 0 && nextM < subMSeqs.Count && candFs.Count >= 4 && dm > 0 && candFs.Count >= dm - 2)
                            {
                                var maxTrim = Math.Min(6, candFs.Count - 1);
                                var checkLen = Math.Min(12, Math.Min(dm, candFs.Count));
                                var bestTrim = 0;
                                var bestViol = 0;
                                var bestExact = 0;
                                for (var t = 0; t <= maxTrim; t++)
                                {
                                    var spanCheck = Math.Min(checkLen, candFs.Count - t);
                                    var viol = 0;
                                    var exact = 0;
                                    for (var j = 0; j < spanCheck; j++)
                                    {
                                        var relF = candFs[t + j];
                                        var vaF = allFuncsFiltered[fIdx0 + relF];
                                        var offF = (int)(vaF - textVa);
                                        var szF = funcSizesFiltered[fIdx0 + relF];
                                        var zeroGpr = TryGetTailcallZeroedGprReg(textBytes, offF, szF);
                                        if (zeroGpr < 0) continue;

                                        var mi = methodsSeq[subMSeqs[j]].methodIdx;
                                        var isSt = (mts[mi].flags & 0x0010) != 0;
                                        var pc = mts[mi].parameterCount;
                                        if (pc == 0)
                                        {
                                            var maxGpr = isSt ? 0 : 1;
                                            if (zeroGpr > maxGpr) viol++;
                                        }
                                        else if (pc <= 2)
                                        {
                                            var maxGpr = (isSt ? 0 : 1) + pc;
                                            if (zeroGpr == maxGpr) exact++;
                                        }
                                    }
                                    if (t == 0)
                                    {
                                        bestViol = viol;
                                        bestExact = exact;
                                        if (viol == 0) break;
                                    }
                                    else if (viol < bestViol || (viol == bestViol && exact > bestExact))
                                    {
                                        bestTrim = t;
                                        bestViol = viol;
                                        bestExact = exact;
                                        if (viol == 0 && t > 0) break;
                                    }
                                }
                                if (bestTrim > 0 && bestViol < int.MaxValue)
                                {
                                    candFs.RemoveRange(0, bestTrim);
                                }
                            }

                            var effDf = candFs.Count;
                            if (effDf >= dm)
                            {
                                for (var j = 0; j < dm; j++)
                                {
                                    var pick = effDf == dm
                                        ? j
                                        : (int)((long)j * effDf / dm);
                                    if (pick >= effDf) pick = effDf - 1;
                                    AssignMethodVa(subMSeqs[segStartsM + 1 + j], candFs[pick]);
                                }
                            }
                            else
                            {
                                // Route ICF over-capacity (dm - effDf) onto tiny (<= 12B) stubs first so larger frames & tailcalls stay 1-to-1.
                                var tinyCount = 0;
                                for (var i = 0; i < effDf; i++)
                                {
                                    if (funcSizesFiltered[fIdx0 + candFs[i]] <= 12) tinyCount++;
                                }
                                var rem = dm - effDf;
                                if (tinyCount >= 2 && rem <= tinyCount * 3)
                                {
                                    var tinySeen = 0;
                                    var methodPos = 0;
                                    for (var i = 0; i < effDf && methodPos < dm; i++)
                                    {
                                        var extra = 0;
                                        if (funcSizesFiltered[fIdx0 + candFs[i]] <= 12)
                                        {
                                            var c0 = tinySeen * rem / tinyCount;
                                            tinySeen++;
                                            var c1 = tinySeen * rem / tinyCount;
                                            extra = c1 - c0;
                                        }
                                        var take = 1 + extra;
                                        for (var u = 0; u < take && methodPos < dm; u++)
                                        {
                                            AssignMethodVa(subMSeqs[segStartsM + 1 + methodPos], candFs[i]);
                                            methodPos++;
                                        }
                                    }
                                    while (methodPos < dm)
                                    {
                                        AssignMethodVa(subMSeqs[segStartsM + 1 + methodPos], candFs[effDf - 1]);
                                        methodPos++;
                                    }
                                }
                                else
                                {
                                    for (var j = 0; j < dm; j++)
                                    {
                                        var pick = (int)((long)j * effDf / dm);
                                        if (pick >= effDf) pick = effDf - 1;
                                        AssignMethodVa(subMSeqs[segStartsM + 1 + j], candFs[pick]);
                                    }
                                }
                            }
                        }
                    }

                    segStartsF = nextF;
                    segStartsM = nextM;
                }
            }

            if (chunks.Count <= 1)
            {
                var allF = new List<int>(fCount);
                for (var f = 0; f < fCount; f++) allF.Add(f);
                var allM = new List<int>(mCount);
                for (var m = 0; m < mCount; m++) allM.Add(m);
                var anc = chunks.Count == 1 ? chunks[0] : new List<(int, int)>();
                FillSubproblem(allF, allM, anc);
                return;
            }

            // Order secondary chunks inner-to-outer (deepest nesting first), breaking ties by anchor count and seq span.
            var nChunks = chunks.Count;
            var depth = new int[nChunks];
            for (var c = 1; c < nChunks; c++)
            {
                var f0 = chunks[c][0].funcRelIdx;
                var f1 = chunks[c][^1].funcRelIdx;
                var d = 0;
                for (var p = 0; p < nChunks; p++)
                {
                    if (p == c) continue;
                    if (chunks[p][0].funcRelIdx < f0 && f1 < chunks[p][^1].funcRelIdx) d++;
                }
                depth[c] = d;
            }
            var secOrder = new int[nChunks - 1];
            for (var i = 0; i < secOrder.Length; i++) secOrder[i] = i + 1;
            Array.Sort(secOrder, (a, b) =>
            {
                var d = depth[b].CompareTo(depth[a]);
                if (d != 0) return d;
                var cntCmp = chunks[b].Count.CompareTo(chunks[a].Count);
                if (cntCmp != 0) return cntCmp;
                return (chunks[b][^1].seq - chunks[b][0].seq).CompareTo(chunks[a][^1].seq - chunks[a][0].seq);
            });

            var allAnchorSeqs = new List<int>(64);
            var pinned = new List<(int f, int s, int c)>(64);
            for (var c = 0; c < nChunks; c++)
            {
                foreach (var (fr, sq) in chunks[c])
                {
                    allAnchorSeqs.Add(sq);
                    pinned.Add((fr, sq, c));
                }
            }
            allAnchorSeqs.Sort();
            pinned.Sort((a, b) => a.f.CompareTo(b.f));

            // Map every secondary chunk's boundary seqs so competing secondary chunks sharing an M-gap can coordinate budgets.
            var secStartToChunk = new Dictionary<int, int>(nChunks);
            var secEndToChunk = new Dictionary<int, int>(nChunks);
            for (var c = 1; c < nChunks; c++)
            {
                secStartToChunk[chunks[c][0].seq] = c;
                secEndToChunk[chunks[c][^1].seq] = c;
            }

            int PrevAnchorBelow(int s)
            {
                var lo = 0;
                var hi = allAnchorSeqs.Count;
                while (lo < hi)
                {
                    var mid = lo + ((hi - lo) >> 1);
                    if (allAnchorSeqs[mid] < s) lo = mid + 1;
                    else hi = mid;
                }
                return lo > 0 ? allAnchorSeqs[lo - 1] : -1;
            }

            int NextAnchorAbove(int s)
            {
                var lo = 0;
                var hi = allAnchorSeqs.Count;
                while (lo < hi)
                {
                    var mid = lo + ((hi - lo) >> 1);
                    if (allAnchorSeqs[mid] <= s) lo = mid + 1;
                    else hi = mid;
                }
                return lo < allAnchorSeqs.Count ? allAnchorSeqs[lo] : mCount;
            }

            // Compute F-gap limits for each secondary chunk (interior brackets reserve parent's unclaimed methods first).
            var ratioArr = new double[nChunks];
            var allowLeftF = new int[nChunks];
            var allowRightF = new int[nChunks];
            var wantHeadM = new int[nChunks];
            var wantTailM = new int[nChunks];

            // Precompute how much free F-space remains in each parent bracket (p_i.f .. p_{i+1}.f) of chunk 0.
            var pri = chunks[0];
            var priPinPos = new Dictionary<(int f, int s), int>(pri.Count);
            for (var i = 0; i < pri.Count; i++) priPinPos[(pri[i].funcRelIdx, pri[i].seq)] = i;

            var secCorePrefix = new int[fCount + 1];
            var isSecCoreF = new bool[fCount];
            var isSecM = new bool[mCount];
            for (var c = 1; c < nChunks; c++)
            {
                for (var f = chunks[c][0].funcRelIdx; f <= chunks[c][^1].funcRelIdx; f++)
                {
                    if (f >= 0 && f < fCount) isSecCoreF[f] = true;
                }
                for (var m = chunks[c][0].seq; m <= chunks[c][^1].seq; m++)
                {
                    if (m >= 0 && m < mCount) isSecM[m] = true;
                }
            }
            for (var f = 0; f < fCount; f++) secCorePrefix[f + 1] = secCorePrefix[f] + (isSecCoreF[f] ? 1 : 0);

            var secMPrefix = new int[mCount + 1];
            for (var m = 0; m < mCount; m++) secMPrefix[m + 1] = secMPrefix[m] + (isSecM[m] ? 1 : 0);

            var bracketRatioFree = new double[Math.Max(1, pri.Count - 1)];
            for (var bi = 0; bi + 1 < pri.Count; bi++)
            {
                var fA = pri[bi].funcRelIdx;
                var fB = pri[bi + 1].funcRelIdx;
                var sA = pri[bi].seq;
                var sB = pri[bi + 1].seq;
                var totOpenF = Math.Max(0, (fB - fA - 1) - (secCorePrefix[fB] - secCorePrefix[fA + 1]));
                var priUnclaimedM = Math.Max(0, (sB - sA - 1) - (secMPrefix[sB] - secMPrefix[sA + 1]));
                var priWantF = (int)Math.Round(priUnclaimedM * 1.08);
                var freeF = Math.Max(0, totOpenF - priWantF);
                bracketRatioFree[bi] = totOpenF > 0 ? (double)freeF / totOpenF : 0.0;
            }

            int BracketIndexOfF(int f)
            {
                if (pri.Count < 2 || f <= pri[0].funcRelIdx || f >= pri[^1].funcRelIdx) return -1;
                var lo = 0;
                var hi = pri.Count - 2;
                while (lo <= hi)
                {
                    var mid = lo + ((hi - lo) >> 1);
                    if (f < pri[mid].funcRelIdx) hi = mid - 1;
                    else if (f > pri[mid + 1].funcRelIdx) lo = mid + 1;
                    else return mid;
                }
                return -1;
            }

            for (var c = 1; c < nChunks; c++)
            {
                var ch = chunks[c];
                var f0 = ch[0].funcRelIdx;
                var f1 = ch[^1].funcRelIdx;
                var s0 = ch[0].seq;
                var s1 = ch[^1].seq;
                var r = Math.Clamp((double)Math.Max(1, f1 - f0) / Math.Max(1, s1 - s0), 0.85, 1.35);
                ratioArr[c] = r;

                // Find immediate pinned anchors surrounding [f0 .. f1].
                var idxL = LowerBoundPinned(pinned, f0) - 1;
                var idxR = UpperBoundPinned(pinned, f1);
                var rawLeftF = idxL >= 0 ? Math.Max(0, f0 - pinned[idxL].f - 1) : f0;
                var rawRightF = idxR < pinned.Count ? Math.Max(0, pinned[idxR].f - 1 - f1) : Math.Max(0, fCount - 1 - f1);

                var cTailAvail = Math.Max(0, NextAnchorAbove(s1) - 1 - s1);
                var cHeadAvail = Math.Max(0, s0 - 1 - PrevAnchorBelow(s0));

                // Left side gap share
                int limL;
                if (idxL < 0)
                {
                    limL = rawLeftF;
                }
                else
                {
                    var lC = pinned[idxL].c;
                    var lS = pinned[idxL].s;
                    if (lC == 0)
                    {
                        var bi = BracketIndexOfF(f0);
                        if (bi >= 0 && bi == BracketIndexOfF(pinned[idxL].f + 1))
                        {
                            limL = (int)Math.Floor(rawLeftF * bracketRatioFree[bi]);
                        }
                        else
                        {
                            var tailL = Math.Max(0, NextAnchorAbove(lS) - 1 - lS);
                            var resL = Math.Min(rawLeftF, (int)Math.Round(tailL * 1.05));
                            limL = Math.Max(0, rawLeftF - resL);
                        }
                    }
                    else
                    {
                        var tailL = Math.Max(0, NextAnchorAbove(lS) - 1 - lS);
                        var tot = Math.Max(1, tailL + cHeadAvail);
                        var bi = BracketIndexOfF(f0);
                        var usable = bi >= 0 ? (int)Math.Floor(rawLeftF * bracketRatioFree[bi]) : rawLeftF;
                        limL = Math.Clamp((int)Math.Round((double)usable * cHeadAvail / tot), 0, usable);
                    }
                }

                // Right side gap share
                int limR;
                if (idxR >= pinned.Count)
                {
                    limR = rawRightF;
                }
                else
                {
                    var rC = pinned[idxR].c;
                    var rS = pinned[idxR].s;
                    if (rC == 0)
                    {
                        var bi = BracketIndexOfF(f1);
                        if (bi >= 0 && bi == BracketIndexOfF(pinned[idxR].f - 1))
                        {
                            limR = (int)Math.Floor(rawRightF * bracketRatioFree[bi]);
                        }
                        else
                        {
                            var headR = Math.Max(0, rS - 1 - PrevAnchorBelow(rS));
                            var resR = Math.Min(rawRightF, (int)Math.Round(headR * 1.05));
                            limR = Math.Max(0, rawRightF - resR);
                        }
                    }
                    else
                    {
                        var headR = Math.Max(0, rS - 1 - PrevAnchorBelow(rS));
                        var tot = Math.Max(1, cTailAvail + headR);
                        var bi = BracketIndexOfF(f1);
                        var usable = bi >= 0 ? (int)Math.Floor(rawRightF * bracketRatioFree[bi]) : rawRightF;
                        limR = Math.Clamp((int)Math.Round((double)usable * cTailAvail / tot), 0, usable);
                    }
                }

                allowLeftF[c] = limL;
                allowRightF[c] = limR;
                wantHeadM[c] = (int)Math.Round(limL / r);
                wantTailM[c] = (int)Math.Round(limR / r);
            }

            static int LowerBoundPinned(List<(int f, int s, int c)> list, int targetF)
            {
                int lo = 0, hi = list.Count;
                while (lo < hi)
                {
                    var mid = lo + ((hi - lo) >> 1);
                    if (list[mid].f < targetF) lo = mid + 1;
                    else hi = mid;
                }
                return lo;
            }

            static int UpperBoundPinned(List<(int f, int s, int c)> list, int targetF)
            {
                int lo = 0, hi = list.Count;
                while (lo < hi)
                {
                    var mid = lo + ((hi - lo) >> 1);
                    if (list[mid].f <= targetF) lo = mid + 1;
                    else hi = mid;
                }
                return lo;
            }

            var claimedF = new bool[fCount];
            var claimedM = new bool[mCount];
            var chunkPlaced = new bool[nChunks];

            foreach (var c in secOrder)
            {
                var ch = chunks[c];
                var f0 = ch[0].funcRelIdx;
                var f1 = ch[^1].funcRelIdx;
                var s0 = ch[0].seq;
                var s1 = ch[^1].seq;

                // Check core isn't already partially claimed (defensive guard).
                var coreFree = true;
                for (var f = f0; f <= f1 && coreFree; f++)
                {
                    if (claimedF[f]) coreFree = false;
                }
                for (var m = s0; m <= s1 && coreFree; m++)
                {
                    if (claimedM[m]) coreFree = false;
                }
                if (!coreFree) continue;

                var ratio = ratioArr[c];

                // Measure immediately contiguous unclaimed functions leftward/rightward up to allowLeftF/allowRightF.
                var availHeadF = 0;
                for (var f = f0 - 1; f >= 0 && availHeadF < allowLeftF[c] && !claimedF[f]; f--) availHeadF++;
                var availTailF = 0;
                for (var f = f1 + 1; f < fCount && availTailF < allowRightF[c] && !claimedF[f]; f++) availTailF++;

                var lowBoundS = PrevAnchorBelow(s0) + 1;
                var highBoundS = NextAnchorAbove(s1) - 1;

                // Count unclaimed methods in M-gap and reserve opposing share if an unplaced secondary chunk shares the M-gap.
                var maxHeadM = 0;
                for (var m = s0 - 1; m >= lowBoundS && !claimedM[m]; m--) maxHeadM++;
                if (lowBoundS > 0 && secEndToChunk.TryGetValue(lowBoundS - 1, out var cPrev) && !chunkPlaced[cPrev] && maxHeadM > 0)
                {
                    var comb = wantTailM[cPrev] + wantHeadM[c];
                    if (comb > maxHeadM)
                    {
                        var keepPrev = Math.Clamp((int)Math.Round((double)maxHeadM * wantTailM[cPrev] / comb), 0, maxHeadM);
                        maxHeadM -= keepPrev;
                    }
                }

                var maxTailM = 0;
                for (var m = s1 + 1; m <= highBoundS && !claimedM[m]; m++) maxTailM++;
                if (highBoundS + 1 < mCount && secStartToChunk.TryGetValue(highBoundS + 1, out var cNext) && !chunkPlaced[cNext] && maxTailM > 0)
                {
                    var comb = wantTailM[c] + wantHeadM[cNext];
                    if (comb > maxTailM)
                    {
                        var keepNext = Math.Clamp((int)Math.Round((double)maxTailM * wantHeadM[cNext] / comb), 0, maxTailM);
                        maxTailM -= keepNext;
                    }
                }

                var headM = Math.Clamp((int)Math.Round(availHeadF / ratio), 0, maxHeadM);
                var tailM = Math.Clamp((int)Math.Round(availTailF / ratio), 0, maxTailM);

                var useF0 = headM == 0
                    ? f0
                    : Math.Max(f0 - availHeadF, f0 - (int)Math.Round(headM * ratio));
                var useF1 = tailM == 0
                    ? f1
                    : Math.Min(f1 + availTailF, f1 + (int)Math.Round(tailM * ratio));
                var useS0 = s0 - headM;
                var useS1 = s1 + tailM;

                chunkPlaced[c] = true;

                var secF = new List<int>(useF1 - useF0 + 1);
                var fMap = new Dictionary<int, int>(useF1 - useF0 + 1);
                for (var f = useF0; f <= useF1; f++)
                {
                    claimedF[f] = true;
                    fMap[f] = secF.Count;
                    secF.Add(f);
                }

                var secM = new List<int>(useS1 - useS0 + 1);
                var mMap = new Dictionary<int, int>(useS1 - useS0 + 1);
                for (var m = useS0; m <= useS1; m++)
                {
                    claimedM[m] = true;
                    mMap[m] = secM.Count;
                    secM.Add(m);
                }

                var secAnchors = new List<(int, int)>(ch.Count);
                foreach (var (fr, sq) in ch)
                {
                    secAnchors.Add((fMap[fr], mMap[sq]));
                }
                FillSubproblem(secF, secM, secAnchors);
            }

            // Primary chunk operates over remaining unclaimed functions and methods.
            var priF = new List<int>(fCount);
            var priFMap = new Dictionary<int, int>(fCount);
            for (var f = 0; f < fCount; f++)
            {
                if (!claimedF[f])
                {
                    priFMap[f] = priF.Count;
                    priF.Add(f);
                }
            }

            var priM = new List<int>(mCount);
            var priMMap = new Dictionary<int, int>(mCount);
            for (var m = 0; m < mCount; m++)
            {
                if (!claimedM[m])
                {
                    priMMap[m] = priM.Count;
                    priM.Add(m);
                }
            }

            var priAnchors = new List<(int, int)>(chunks[0].Count);
            foreach (var (fr, sq) in chunks[0])
            {
                if (priFMap.TryGetValue(fr, out var pF) && priMMap.TryGetValue(sq, out var pM))
                {
                    priAnchors.Add((pF, pM));
                }
            }
            FillSubproblem(priF, priM, priAnchors);
        }

        private static (ulong vaStart, ulong vaEnd)[] ComputeImageWindows(
            ulong[] dense,
            int lastCodeSlot,
            int cgSlot,
            int invokerEndSlot,
            ulong r2First,
            int[] orderedImgs,
            List<(int tdIdx, int methodIdx)>[] imgMethods,
            List<GlobalAnchor>[] anchorsByImg,
            HashSet<ulong> excludedClusterVas)
        {
            var m = orderedImgs.Length;
            var windows = new (ulong vaStart, ulong vaEnd)[m];

            // Build active-slot prefix sums so excluded closed-generic DelClusters carry zero weight during partitioning.
            var hasExcl = excludedClusterVas != null && excludedClusterVas.Count > 0;
            var activePref = new int[lastCodeSlot + 3];
            for (var s = 0; s <= lastCodeSlot; s++)
            {
                var ex = hasExcl && dense[s] != 0 && excludedClusterVas.Contains(dense[s]);
                activePref[s + 1] = activePref[s] + (ex ? 0 : 1);
            }
            activePref[lastCodeSlot + 2] = activePref[lastCodeSlot + 1] + 1;

            int ActiveCount(int lo, int hi)
            {
                lo = Math.Clamp(lo, 0, activePref.Length - 1);
                hi = Math.Clamp(hi, lo, activePref.Length - 1);
                return activePref[hi] - activePref[lo];
            }

            int[] PartitionActive(int slotStart, int slotEnd, long[] weights)
            {
                var nW = weights.Length;
                var endS = Math.Max(slotStart, slotEnd);
                var p0 = activePref[Math.Clamp(slotStart, 0, activePref.Length - 1)];
                var p1 = activePref[Math.Clamp(endS, 0, activePref.Length - 1)];
                var spanActive = p1 - p0;
                if (spanActive <= 0)
                {
                    return PartitionSlots(slotStart, endS, weights);
                }

                var bounds = new int[nW + 1];
                bounds[0] = slotStart;
                bounds[nW] = endS;
                long total = 0;
                for (var i = 0; i < nW; i++) total += weights[i];
                if (total <= 0) total = nW;
                long acc = 0;
                var maxHi = Math.Min(endS, activePref.Length - 1);
                for (var i = 0; i < nW - 1; i++)
                {
                    acc += weights[i];
                    var targetP = p0 + (int)((double)acc * spanActive / total);
                    var lo = Math.Clamp(bounds[i], 0, maxHi);
                    var hi = maxHi;
                    while (lo < hi)
                    {
                        var mid = lo + ((hi - lo) >> 1);
                        if (activePref[mid] < targetP) lo = mid + 1;
                        else hi = mid;
                    }
                    bounds[i + 1] = Math.Clamp(lo, bounds[i], endS);
                }
                return bounds;
            }

            int SlotBackActive(int sEnd, int activeBack, int minSlot)
            {
                var hiEnd = Math.Clamp(sEnd, 0, activePref.Length - 1);
                var targetP = activePref[hiEnd] - activeBack;
                var lo = Math.Clamp(minSlot, 0, hiEnd);
                var hi = hiEnd;
                while (lo < hi)
                {
                    var mid = lo + ((hi - lo) >> 1);
                    if (activePref[mid] < targetP) lo = mid + 1;
                    else hi = mid;
                }
                return lo;
            }

            // Build next non-zero VA helper
            ulong SlotToVa(int slot)
            {
                if (slot < 0) slot = 0;
                if (slot > lastCodeSlot) return r2First;
                for (var s = slot; s <= lastCodeSlot; s++)
                {
                    if (dense[s] != 0) return dense[s];
                }
                return r2First;
            }

            // Collect anchored ranks in ascending rank order.
            var anchoredRanks = new List<int>(m);
            for (var r = 0; r < m; r++)
            {
                if (anchorsByImg[orderedImgs[r]].Count > 0)
                {
                    anchoredRanks.Add(r);
                }
            }

            if (anchoredRanks.Count == 0)
            {
                // Fallback purely by compiled method counts across [0..cgSlot) and [invokerEndSlot..lastCodeSlot+1).
                var slotStart = invokerEndSlot > 0 ? invokerEndSlot : 0;
                DistributeGapByWeights(0, m, slotStart, lastCodeSlot + 1, orderedImgs, imgMethods, windows, SlotToVa, r2First, PartitionActive);
                return windows;
            }

            var splitLoSlot = new int[m];
            var splitHiSlot = new int[m];
            Array.Fill(splitLoSlot, -1);
            Array.Fill(splitHiSlot, -1);

            // Find cg/invoker crossing point among anchoredRanks
            var lastPreAnchoredRank = -1;
            var firstPostAnchoredRank = m;
            if (cgSlot >= 0)
            {
                foreach (var r in anchoredRanks)
                {
                    var lst = anchorsByImg[orderedImgs[r]];
                    if (lst[^1].Slot < cgSlot) lastPreAnchoredRank = r;
                    else if (firstPostAnchoredRank == m && lst[0].Slot > cgSlot) firstPostAnchoredRank = r;
                }
            }

            int SumOutOfOrderSpan(List<GlobalAnchor> lst, int idxFrom, int idxToExclusive, int minSeqExcl, int maxSeqExcl, bool extendRightTail)
            {
                List<int> spineIndices = null;
                if (extendRightTail)
                {
                    var baseItems = new List<int>();
                    for (var i = 0; i < lst.Count; i++)
                    {
                        var sq = lst[i].MethodSeq;
                        if (sq >= 0 && sq <= minSeqExcl) baseItems.Add(i);
                    }
                    if (baseItems.Count >= 2)
                    {
                        var parent = new int[baseItems.Count];
                        var dpVals = new List<int>(baseItems.Count);
                        var dpPos = new List<int>(baseItems.Count);
                        for (var bi = 0; bi < baseItems.Count; bi++)
                        {
                            var sq = lst[baseItems[bi]].MethodSeq;
                            int lo = 0, hi = dpVals.Count;
                            while (lo < hi)
                            {
                                var mid = (lo + hi) >> 1;
                                if (dpVals[mid] <= sq) lo = mid + 1;
                                else hi = mid;
                            }
                            parent[bi] = lo > 0 ? dpPos[lo - 1] : -1;
                            if (lo == dpVals.Count) { dpVals.Add(sq); dpPos.Add(bi); }
                            else { dpVals[lo] = sq; dpPos[lo] = bi; }
                        }
                        spineIndices = new List<int>(dpPos.Count);
                        var cur = dpPos[^1];
                        while (cur != -1) { spineIndices.Add(baseItems[cur]); cur = parent[cur]; }
                        spineIndices.Reverse();
                    }
                }

                var spans = new List<(int sLo, int sHi)>();
                int rLo = -1, rHi = -1, uniqCnt = 0, runFirstIdx = -1, runLastIdx = -1;

                void FlushRun()
                {
                    if (uniqCnt >= 2 && rHi - rLo >= 20)
                    {
                        var extHi = rHi;
                        if (extendRightTail && maxSeqExcl - 1 > rHi && runFirstIdx >= 0 && runLastIdx >= runFirstIdx)
                        {
                            int prevIdx = -1, nextIdx = -1;
                            if (spineIndices != null)
                            {
                                var pos = spineIndices.BinarySearch(runFirstIdx);
                                var ins = pos < 0 ? ~pos : pos;
                                if (ins > 0) prevIdx = spineIndices[ins - 1];
                                var posR = spineIndices.BinarySearch(runLastIdx);
                                var insR = posR < 0 ? ~posR : posR + 1;
                                if (insR < spineIndices.Count) nextIdx = spineIndices[insR];
                            }
                            else
                            {
                                for (var p = runFirstIdx - 1; p >= 0; p--)
                                {
                                    var ps = lst[p].MethodSeq;
                                    if (ps >= 0 && ps <= minSeqExcl) { prevIdx = p; break; }
                                }
                                for (var n = runLastIdx + 1; n < lst.Count; n++)
                                {
                                    var ns = lst[n].MethodSeq;
                                    if (ns >= 0 && ns <= minSeqExcl) { nextIdx = n; break; }
                                }
                            }
                            if (prevIdx >= 0 && nextIdx >= 0)
                            {
                                var pSeqSpan = lst[nextIdx].MethodSeq - lst[prevIdx].MethodSeq;
                                if (pSeqSpan > 0 && pSeqSpan < 500)
                                {
                                    var gapAfter = ActiveCount(lst[runLastIdx].Slot + 1, lst[nextIdx].Slot);
                                    var spare = gapAfter - (int)Math.Round(pSeqSpan * 1.15);
                                    if (spare > 20)
                                    {
                                        extHi = Math.Min(maxSeqExcl - 1, rHi + (int)(spare / 1.05));
                                    }
                                }
                            }
                        }
                        spans.Add((rLo, extHi));
                    }
                    rLo = rHi = uniqCnt = runFirstIdx = runLastIdx = -1;
                    uniqCnt = 0;
                }

                for (var j = idxFrom; j < idxToExclusive; j++)
                {
                    var sq = lst[j].MethodSeq;
                    if (sq < 0 || sq <= minSeqExcl || sq >= maxSeqExcl) continue;
                    if (uniqCnt == 0)
                    {
                        rLo = rHi = sq;
                        uniqCnt = 1;
                        runFirstIdx = runLastIdx = j;
                    }
                    else if (sq >= rHi)
                    {
                        if (sq > rHi) uniqCnt++;
                        rHi = sq;
                        runLastIdx = j;
                    }
                    else
                    {
                        FlushRun();
                        rLo = rHi = sq;
                        uniqCnt = 1;
                        runFirstIdx = runLastIdx = j;
                    }
                }
                FlushRun();
                if (spans.Count == 0) return 0;
                spans.Sort((a, b) => a.sLo.CompareTo(b.sLo));
                var covered = 0;
                int curLo = spans[0].sLo, curHi = spans[0].sHi;
                for (var i = 1; i < spans.Count; i++)
                {
                    if (spans[i].sLo <= curHi + 1) curHi = Math.Max(curHi, spans[i].sHi);
                    else { covered += curHi - curLo + 1; curLo = spans[i].sLo; curHi = spans[i].sHi; }
                }
                covered += curHi - curLo + 1;
                return covered;
            }

            // Estimate head/tail compiled methods of an anchored image at its boundary anchors
            (int est, int needPre, bool isExact) EvalHead(int r)
            {
                var lst = anchorsByImg[orderedImgs[r]];
                var cnt = imgMethods[orderedImgs[r]].Count;
                var kHead = -1;
                for (var i = 0; i < lst.Count; i++)
                {
                    if (lst[i].MethodSeq >= 0) { kHead = i; break; }
                }
                int raw;
                int needPre = 0;
                bool isExact = false;
                if (kHead == 0)
                {
                    raw = lst[0].MethodSeq;
                    needPre = raw;
                    isExact = true;
                }
                else if (kHead > 0)
                {
                    var gap = ActiveCount(lst[0].Slot, lst[kHead].Slot);
                    if (gap <= 256 && lst[kHead].MethodSeq >= gap)
                    {
                        raw = lst[kHead].MethodSeq - gap;
                        isExact = gap <= 32;
                        if (isExact && raw > 8) needPre = raw - 8;
                    }
                    else if (lst[0].ApproxSeq >= 0)
                    {
                        raw = lst[0].ApproxSeq;
                    }
                    else if (lst[kHead].MethodSeq >= gap)
                    {
                        raw = Math.Min(lst[kHead].MethodSeq - gap, Math.Max(0, cnt / 2));
                    }
                    else
                    {
                        raw = Math.Max(0, cnt / 4);
                    }
                }
                else
                {
                    raw = lst[0].ApproxSeq >= 0 ? lst[0].ApproxSeq : Math.Max(0, cnt / 4);
                }

                if (kHead >= 0 && raw > 20)
                {
                    var sub = SumOutOfOrderSpan(lst, kHead + 1, lst.Count, -1, lst[kHead].MethodSeq, false);
                    if (sub > 0)
                    {
                        raw = Math.Max(0, raw - sub);
                        needPre = Math.Min(needPre, raw);
                    }
                }
                return (raw, needPre, isExact);
            }

            (int est, bool isExact) EvalTail(int r)
            {
                var lst = anchorsByImg[orderedImgs[r]];
                var cnt = imgMethods[orderedImgs[r]].Count;
                var kTail = -1;
                for (var i = lst.Count - 1; i >= 0; i--)
                {
                    if (lst[i].MethodSeq >= 0) { kTail = i; break; }
                }
                int raw;
                int sRef;
                bool isExact = false;
                if (kTail == lst.Count - 1 && kTail >= 0)
                {
                    sRef = lst[^1].MethodSeq;
                    raw = Math.Max(0, cnt - 1 - sRef);
                    isExact = true;
                }
                else if (kTail >= 0)
                {
                    var gap = ActiveCount(lst[kTail].Slot, lst[^1].Slot);
                    if (gap <= 256 && cnt - 1 - lst[kTail].MethodSeq >= gap)
                    {
                        raw = Math.Max(0, cnt - 1 - lst[kTail].MethodSeq - gap);
                        sRef = Math.Min(cnt - 1, lst[kTail].MethodSeq + gap);
                        isExact = gap <= 32;
                    }
                    else if (lst[^1].ApproxSeq >= 0)
                    {
                        sRef = lst[^1].ApproxSeq;
                        raw = Math.Max(0, cnt - 1 - sRef);
                    }
                    else
                    {
                        raw = Math.Max(0, cnt - 1 - lst[kTail].MethodSeq - gap);
                        sRef = Math.Min(cnt - 1, lst[kTail].MethodSeq + gap);
                    }
                }
                else
                {
                    sRef = lst[^1].ApproxSeq;
                    raw = sRef >= 0 ? Math.Max(0, cnt - 1 - sRef) : Math.Max(0, cnt / 4);
                }

                if (sRef >= 0 && raw > 20)
                {
                    var limitIdx = kTail >= 0 ? kTail : lst.Count - 1;
                    var sub = SumOutOfOrderSpan(lst, 0, limitIdx, sRef, cnt, true);
                    if (sub > 0) raw = Math.Max(0, raw - sub);
                }
                return (raw, isExact);
            }

            // Handle leading images [0 .. firstAnchorRank]
            var firstAncR = anchoredRanks[0];
            var firstAnc = anchorsByImg[orderedImgs[firstAncR]][0];
            var firstAncSlot = firstAnc.Slot;
            var (firstHeadEst, firstNeedPre, _) = EvalHead(firstAncR);
            if (cgSlot >= 0 && firstAncR > lastPreAnchoredRank && invokerEndSlot <= firstAncSlot)
            {
                // Everything before firstPostAnchoredRank sits either pre-cg or between invokerEnd and firstPostAnchor
                DistributeCrossingBoundary(0, firstAncR, 0, cgSlot, invokerEndSlot, firstAncSlot,
                    0, firstHeadEst, orderedImgs, imgMethods, splitLoSlot, splitHiSlot,
                    ActiveCount, PartitionActive);
                var activePost = ActiveCount(invokerEndSlot, firstAncSlot);
                if (firstNeedPre > 0 && activePost > 0)
                {
                    var minPost = SlotBackActive(firstAncSlot, Math.Min(activePost, firstNeedPre), invokerEndSlot);
                    if (splitLoSlot[firstAncR] > minPost)
                    {
                        splitLoSlot[firstAncR] = minPost;
                        for (var r = firstAncR - 1; r >= 0 && splitHiSlot[r] > minPost; r--)
                        {
                            splitHiSlot[r] = minPost;
                            if (splitLoSlot[r] > minPost) splitLoSlot[r] = minPost;
                        }
                    }
                }
            }
            else
            {
                // Pre-region ends cleanly before firstAncSlot
                var preOnlyCount = 0L;
                for (var r = 0; r < firstAncR; r++) preOnlyCount += Math.Max(1, imgMethods[orderedImgs[r]].Count);
                var headBCount = (long)Math.Max(1, firstHeadEst);
                var weights = new long[firstAncR + 1];
                for (var r = 0; r < firstAncR; r++) weights[r] = Math.Max(1, imgMethods[orderedImgs[r]].Count);
                weights[firstAncR] = headBCount;
                var upperPre = firstNeedPre > 0 ? firstAncSlot : firstAncSlot + 1;
                var bounds = PartitionActive(0, Math.Max(0, upperPre), weights);
                var preSplitIdx = firstAncR;
                var preLoEnd = bounds[preSplitIdx];

                // Guard against pre-CodeGen inflated GenericMethods block (<firstAncR> must not absorb 10k+ generics into its head).
                var expectedPre = preOnlyCount + headBCount;
                var activeUpperPre = ActiveCount(0, Math.Max(0, upperPre));
                if (firstAncR > 0 && activeUpperPre > Math.Max(2000, expectedPre * 3))
                {
                    var headCap = Math.Max(headBCount + 128, headBCount * 3 / 2);
                    if (firstAnc.MethodSeq <= 0 && firstAnc.ApproxSeq < 0) headCap = Math.Max(headCap, imgMethods[orderedImgs[firstAncR]].Count / 3);
                    var minFirstAncStart = SlotBackActive(upperPre, (int)Math.Min(activeUpperPre, headCap), 0);
                    if (bounds[preSplitIdx] < minFirstAncStart)
                    {
                        bounds[preSplitIdx] = minFirstAncStart;
                    }
                    var maxPreCap = Math.Max((int)preOnlyCount, (int)preOnlyCount * 3 / 2 + 128);
                    var activeToSplit = ActiveCount(0, bounds[preSplitIdx]);
                    var maxPreEnd = activeToSplit > maxPreCap
                        ? SlotBackActive(bounds[preSplitIdx], activeToSplit - maxPreCap, 0)
                        : bounds[preSplitIdx];
                    var preWeights = new long[firstAncR];
                    for (var r = 0; r < firstAncR; r++) preWeights[r] = weights[r];
                    var preB = PartitionActive(0, maxPreEnd, preWeights);
                    for (var r = 0; r < firstAncR; r++) bounds[r] = preB[r];
                    preLoEnd = preB[firstAncR];
                }
                else if (firstNeedPre > 0 && firstAncSlot > 0)
                {
                    var availPre = ActiveCount(0, firstAncSlot);
                    var reserve = firstAncR == 1
                        ? Math.Min(availPre, firstNeedPre)
                        : Math.Min(availPre, Math.Max(1, firstNeedPre / Math.Max(1, firstAncR)));
                    var maxBoundary = SlotBackActive(firstAncSlot, reserve, 0);
                    if (bounds[preSplitIdx] > maxBoundary)
                    {
                        bounds[preSplitIdx] = maxBoundary;
                        for (var i = preSplitIdx - 1; i >= 0; i--)
                        {
                            if (bounds[i] > maxBoundary) bounds[i] = maxBoundary;
                        }
                        preLoEnd = maxBoundary;
                    }
                }
                for (var r = 0; r <= firstAncR; r++) splitLoSlot[r] = bounds[r];
                for (var r = 0; r < firstAncR - 1; r++) splitHiSlot[r] = bounds[r + 1];
                if (firstAncR > 0) splitHiSlot[firstAncR - 1] = preLoEnd;
            }

            // Handle gaps between consecutive anchored ranks
            for (var a = 0; a + 1 < anchoredRanks.Count; a++)
            {
                var rA = anchoredRanks[a];
                var rB = anchoredRanks[a + 1];
                var sA = anchorsByImg[orderedImgs[rA]][^1].Slot;
                var ancB0 = anchorsByImg[orderedImgs[rB]][0];
                var sB = ancB0.Slot;
                var (tailEstA, exactTailA) = EvalTail(rA);
                var (headEstB, needPreB, exactHeadB) = EvalHead(rB);

                if (cgSlot >= 0 && rA <= lastPreAnchoredRank && rB >= firstPostAnchoredRank && invokerEndSlot >= cgSlot)
                {
                    var hiBoundA = cgSlot;
                    var loBoundB = Math.Min(sB, Math.Max(cgSlot + 1, invokerEndSlot));
                    DistributeCrossingBoundary(rA, rB, sA + 1, hiBoundA, loBoundB, sB,
                        tailEstA, headEstB, orderedImgs, imgMethods, splitLoSlot, splitHiSlot,
                        ActiveCount, PartitionActive);
                    var activeGapB = ActiveCount(loBoundB, sB);
                    if (needPreB > 0 && activeGapB > 0)
                    {
                        var minB = SlotBackActive(sB, Math.Min(activeGapB, CountAwareReserve(needPreB, rB - rA, activeGapB)), loBoundB);
                        if (splitLoSlot[rB] > minB)
                        {
                            splitLoSlot[rB] = minB;
                            for (var r = rB - 1; r > rA && splitHiSlot[r] > minB; r--)
                            {
                                splitHiSlot[r] = minB;
                                if (splitLoSlot[r] > minB) splitLoSlot[r] = minB;
                            }
                            if (rB == rA + 1 && splitHiSlot[rA] > minB) splitHiSlot[rA] = minB;
                        }
                    }
                }
                else
                {
                    var count = rB - rA + 1;
                    var weights = new long[count];
                    weights[0] = Math.Max(1, tailEstA);
                    long sumMid = 0;
                    for (var idx = 1; idx < count - 1; idx++)
                    {
                        var w = Math.Max(1, imgMethods[orderedImgs[rA + idx]].Count);
                        weights[idx] = w;
                        sumMid += w;
                    }
                    weights[count - 1] = Math.Max(1, headEstB);

                    var upperB = needPreB > 0 ? sB : sB + 1;
                    if (sumMid > 0 && (!exactTailA || !exactHeadB))
                    {
                        var gapAvail = ActiveCount(sA + 1, Math.Max(sA + 1, upperB));
                        if (gapAvail > 0 && weights[0] + sumMid + weights[^1] > gapAvail)
                        {
                            var fixedW = (exactTailA ? weights[0] : 0) + (exactHeadB ? weights[^1] : 0);
                            var flexAvail = gapAvail - fixedW - sumMid;
                            if (flexAvail > 0)
                            {
                                var flexTotal = (exactTailA ? 0 : weights[0]) + (exactHeadB ? 0 : weights[^1]);
                                if (flexTotal > 0)
                                {
                                    if (!exactTailA) weights[0] = Math.Max(1, (long)Math.Round((double)flexAvail * weights[0] / flexTotal));
                                    if (!exactHeadB) weights[^1] = Math.Max(1, (long)Math.Round((double)flexAvail * weights[^1] / flexTotal));
                                }
                            }
                        }
                    }

                    var bounds = PartitionActive(sA + 1, Math.Max(sA + 1, upperB), weights);
                    if (needPreB > 0 && sB > sA + 1)
                    {
                        var avail = ActiveCount(sA + 1, sB);
                        int reserve;
                        if (count == 2)
                        {
                            var tailWeight = weights[0];
                            var propKeepA = tailWeight > 1
                                ? Math.Max(0, avail - (int)((long)avail * weights[^1] / Math.Max(1L, tailWeight + weights[^1])))
                                : 0;
                            var halfTail = (int)Math.Min(avail / 2L, tailWeight / 2L);
                            var minKeepA = tailWeight > 1 && needPreB > avail - halfTail
                                ? propKeepA
                                : 0;
                            reserve = Math.Min(needPreB, Math.Max(1, avail - minKeepA));
                        }
                        else
                        {
                            reserve = Math.Min(avail, CountAwareReserve(needPreB, count - 1, avail));
                        }
                        var maxBoundary = SlotBackActive(sB, reserve, sA + 1);
                        if (bounds[^1] > maxBoundary)
                        {
                            bounds[^1] = maxBoundary;
                            for (var i = count - 1; i >= 1; i--)
                            {
                                if (bounds[i] > maxBoundary) bounds[i] = maxBoundary;
                            }
                        }
                    }
                    splitHiSlot[rA] = bounds[1];
                    for (var idx = 1; idx < count - 1; idx++)
                    {
                        splitLoSlot[rA + idx] = bounds[idx];
                        splitHiSlot[rA + idx] = bounds[idx + 1];
                    }
                    splitLoSlot[rB] = bounds[count - 1];
                }
            }

            static int CountAwareReserve(int needPre, int gapSlots, int avail)
            {
                if (avail <= 0) return 0;
                return Math.Max(1, Math.Min(needPre, avail / Math.Max(1, gapSlots)));
            }

            // Handle trailing images [lastAncR .. m - 1]
            var lastAncR = anchoredRanks[^1];
            var lastAncSlot = anchorsByImg[orderedImgs[lastAncR]][^1].Slot;
            {
                var count = m - lastAncR;
                var weights = new long[count];
                var (estTail, _) = EvalTail(lastAncR);
                estTail = Math.Max(1, estTail);
                long tailUnanchored = 0;
                for (var idx = 1; idx < count; idx++)
                {
                    var w = Math.Max(1, imgMethods[orderedImgs[lastAncR + idx]].Count);
                    weights[idx] = w;
                    tailUnanchored += w;
                }
                if (count >= 2)
                {
                    var avail = ActiveCount(lastAncSlot + 1, lastCodeSlot + 1);
                    if (estTail + tailUnanchored > avail && avail > 0)
                    {
                        var capped = avail > tailUnanchored ? (int)(avail - tailUnanchored) : Math.Max(1, avail / 4);
                        estTail = Math.Max(1, Math.Min(estTail, capped));
                    }
                }
                weights[0] = estTail;
                var bounds = PartitionActive(lastAncSlot + 1, lastCodeSlot + 2, weights);
                splitHiSlot[lastAncR] = bounds[1];
                for (var idx = 1; idx < count; idx++)
                {
                    splitLoSlot[lastAncR + idx] = bounds[idx];
                    splitHiSlot[lastAncR + idx] = bounds[idx + 1];
                }
            }

            // Finalize monotonic VA bounds (clamp anchored images to always cover their own anchors)
            for (var r = 0; r < m; r++)
            {
                var loS = splitLoSlot[r];
                var hiS = splitHiSlot[r];
                if (loS < 0) loS = 0;
                if (hiS <= loS) hiS = Math.Min(lastCodeSlot + 1, loS);

                var vaStart = SlotToVa(loS);
                var vaEnd = hiS > lastCodeSlot ? r2First : SlotToVa(hiS);

                var lst = anchorsByImg[orderedImgs[r]];
                if (lst.Count > 0)
                {
                    var a0 = dense[lst[0].Slot];
                    var a1 = dense[lst[^1].Slot];
                    if (a0 != 0 && a0 < vaStart) vaStart = a0;
                    if (a1 != 0 && a1 >= vaEnd) vaEnd = a1 + 4;
                }
                windows[r] = (vaStart, Math.Max(vaStart, vaEnd));
            }

            return windows;
        }

        private static void DistributeCrossingBoundary(
            int rA,
            int rB,
            int preStart,
            int preEnd,
            int postStart,
            int postEnd,
            int tailA,
            int headB,
            int[] orderedImgs,
            List<(int tdIdx, int methodIdx)>[] imgMethods,
            int[] splitLoSlot,
            int[] splitHiSlot,
            Func<int, int, int> activeCount,
            Func<int, int, long[], int[]> partitionActive)
        {
            var preLen = Math.Max(0, activeCount(preStart, preEnd));
            var postLen = Math.Max(0, activeCount(postStart, postEnd));

            // Pick splitRank k in [rA .. rB-1] dividing pre vs post proportionally to compiled method counts.
            var midCount = Math.Max(0, rB - rA - 1);
            var cumPre = new long[midCount + 1];
            cumPre[0] = rA == 0 ? 0 : Math.Max(0, tailA);
            for (var i = 0; i < midCount; i++)
            {
                cumPre[i + 1] = cumPre[i] + imgMethods[orderedImgs[rA + 1 + i]].Count;
            }
            var totalAll = cumPre[midCount] + Math.Max(0, headB);

            var bestK = 0;
            if (totalAll > 0 && preLen + postLen > 0)
            {
                var targetPreRatio = (double)preLen / (preLen + postLen);
                var bestDiff = double.MaxValue;
                for (var k = 0; k <= midCount; k++)
                {
                    var ratio = (double)cumPre[k] / totalAll;
                    var diff = Math.Abs(ratio - targetPreRatio);
                    if (diff < bestDiff)
                    {
                        bestDiff = diff;
                        bestK = k;
                    }
                }
            }

            // First [rA .. rA + bestK] fit into [preStart .. preEnd]
            var preCount = bestK + 1;
            var preWeights = new long[preCount];
            preWeights[0] = Math.Max(1, rA == 0 ? imgMethods[orderedImgs[0]].Count : tailA);
            for (var i = 1; i < preCount; i++) preWeights[i] = Math.Max(1, imgMethods[orderedImgs[rA + i]].Count);
            var preBounds = partitionActive(preStart, preEnd, preWeights);
            if (rA == 0) splitLoSlot[0] = preBounds[0];
            splitHiSlot[rA] = preBounds[1];
            for (var i = 1; i < preCount; i++)
            {
                splitLoSlot[rA + i] = preBounds[i];
                splitHiSlot[rA + i] = preBounds[i + 1];
            }

            // Remaining [rA + bestK + 1 .. rB] fit into [postStart .. postEnd + 1]
            var postFirstR = rA + bestK + 1;
            var postCount = rB - postFirstR + 1;
            var postWeights = new long[postCount];
            for (var i = 0; i < postCount - 1; i++)
            {
                postWeights[i] = Math.Max(1, imgMethods[orderedImgs[postFirstR + i]].Count);
            }
            postWeights[postCount - 1] = Math.Max(1, headB);
            var postBounds = partitionActive(postStart, postEnd + 1, postWeights);
            for (var i = 0; i < postCount - 1; i++)
            {
                splitLoSlot[postFirstR + i] = postBounds[i];
                splitHiSlot[postFirstR + i] = postBounds[i + 1];
            }
            splitLoSlot[rB] = postBounds[postCount - 1];
        }

        private static void DistributeGapByWeights(
            int rStart,
            int rEnd,
            int slotStart,
            int slotEnd,
            int[] orderedImgs,
            List<(int tdIdx, int methodIdx)>[] imgMethods,
            (ulong vaStart, ulong vaEnd)[] windows,
            Func<int, ulong> slotToVa,
            ulong r2First,
            Func<int, int, long[], int[]> partitionActive)
        {
            var n = rEnd - rStart;
            var weights = new long[n];
            for (var i = 0; i < n; i++) weights[i] = Math.Max(1, imgMethods[orderedImgs[rStart + i]].Count);
            var b = partitionActive(slotStart, slotEnd, weights);
            for (var i = 0; i < n; i++)
            {
                var vaS = slotToVa(b[i]);
                var vaE = b[i + 1] >= slotEnd ? r2First : slotToVa(b[i + 1]);
                windows[rStart + i] = (vaS, vaE);
            }
        }

        private static int[] PartitionSlots(int slotStart, int slotEnd, long[] weights)
        {
            var n = weights.Length;
            var bounds = new int[n + 1];
            bounds[0] = slotStart;
            bounds[n] = Math.Max(slotStart, slotEnd);
            var span = bounds[n] - slotStart;
            long total = 0;
            for (var i = 0; i < n; i++) total += weights[i];
            if (total <= 0) total = n;
            long acc = 0;
            for (var i = 0; i < n - 1; i++)
            {
                acc += weights[i];
                bounds[i + 1] = slotStart + (int)((double)acc * span / total);
            }
            return bounds;
        }

        private static bool FunctionReferencesCStringRange(
            byte[] textBytes,
            int textOff,
            int insLimit,
            ulong startVa,
            ulong cstrVa,
            ulong cstrEnd,
            ulong[] regs,
            bool[] regValid)
        {
            if (textOff < 0 || cstrVa >= cstrEnd) return false;
            Array.Clear(regValid, 0, 32);
            var cur = startVa;
            for (var wIdx = 0; wIdx < insLimit && textOff + (wIdx + 1) * 4 <= textBytes.Length; wIdx++)
            {
                var w = BitConverter.ToUInt32(textBytes, textOff + wIdx * 4);
                if ((w & 0x9F000000u) == 0x90000000u) // ADRP
                {
                    var rd = (int)(w & 0x1Fu);
                    var imm = (int)((((w >> 5) & 0x7FFFFu) << 2) | ((w >> 29) & 3u));
                    if ((imm & 0x100000) != 0) imm -= 0x200000;
                    if (rd != 31)
                    {
                        regs[rd] = (cur & ~0xFFFuL) + (ulong)((long)imm << 12);
                        regValid[rd] = true;
                    }
                }
                else if ((w & 0xFF800000u) == 0x91000000u) // ADD imm
                {
                    var rd = (int)(w & 0x1Fu);
                    var rn = (int)((w >> 5) & 0x1Fu);
                    if (rn != 31 && regValid[rn])
                    {
                        var addImm = ((w >> 10) & 0xFFFuL) << (((w >> 22) & 1u) != 0 ? 12 : 0);
                        var target = regs[rn] + addImm;
                        if (target >= cstrVa && target < cstrEnd) return true;
                    }
                    if (rd != 31) regValid[rd] = false;
                }
                else if ((w & 0x3B000000u) == 0x39000000u ||
                         (w & 0x7F000000u) == 0x58000000u ||
                         (w & 0x1F800000u) == 0x12800000u ||
                         (w & 0x7FE00000u) == 0x2A000000u)
                {
                    var rd = (int)(w & 0x1Fu);
                    if (rd != 31) regValid[rd] = false;
                }
                cur += 4;
            }
            return false;
        }

        private static bool HasIndirectBranchOrCall(byte[] textBytes, int textOff, int insLimit)
        {
            if (textOff < 0) return false;
            for (var wIdx = 0; wIdx < insLimit && textOff + (wIdx + 1) * 4 <= textBytes.Length; wIdx++)
            {
                var w = BitConverter.ToUInt32(textBytes, textOff + wIdx * 4);
                if ((w & 0xFFFFFC1Fu) == 0xD61F0000u || (w & 0xFFFFFC1Fu) == 0xD63F0000u)
                {
                    return true;
                }
            }
            return false;
        }

        private static int FindInvokerEndSlot(
            ulong[] dense,
            int cgSlot,
            int lastCodeSlot,
            List<GlobalAnchor>[] anchorsByImg,
            int[] orderedImgs,
            byte[] textBytes,
            ulong textVa,
            ulong cstrVa,
            ulong cstrSize)
        {
            if (cgSlot < 0) return 0;

            var firstPostAnchorSlot = lastCodeSlot;
            foreach (var ii in orderedImgs)
            {
                var lst = anchorsByImg[ii];
                if (lst.Count > 0 && lst[0].Slot > cgSlot && lst[0].Slot < firstPostAnchorSlot)
                {
                    firstPostAnchorSlot = lst[0].Slot;
                }
            }

            // Stack-protector guards (___stack_chk_guard) cause RuntimeInvoker thunks to emit ADRP+LDR,
            // so locate the last large zero-__cstring desert (>= 128 non-zero slots) between cgSlot and firstPostAnchorSlot.
            var cstrEnd = cstrVa + cstrSize;
            var nzCountAfterCg = 0;
            for (var k = cgSlot + 1; k < firstPostAnchorSlot; k++)
            {
                if (dense[k] != 0) nzCountAfterCg++;
            }

            if (cstrSize > 0 && nzCountAfterCg >= 256)
            {
                var regs = new ulong[32];
                var regValid = new bool[32];
                var zeroRun = 0;
                var zeroBlr = 0;
                var lastDesertEnd = -1;

                for (var k = cgSlot + 1; k < firstPostAnchorSlot; k++)
                {
                    var va = dense[k];
                    if (va == 0) continue;
                    ulong nva = 0;
                    for (var j = k + 1; j <= firstPostAnchorSlot; j++)
                    {
                        if (dense[j] != 0) { nva = dense[j]; break; }
                    }
                    if (nva <= va) nva = va + 128;
                    var insLimit = (int)Math.Min(120, Math.Max(1, (long)(nva - va) / 4));
                    var textOff = (int)(va - textVa);

                    if (FunctionReferencesCStringRange(textBytes, textOff, insLimit, va, cstrVa, cstrEnd, regs, regValid))
                    {
                        if (zeroRun >= 128 && zeroBlr * 4 >= zeroRun)
                        {
                            lastDesertEnd = k;
                        }
                        zeroRun = 0;
                        zeroBlr = 0;
                    }
                    else
                    {
                        zeroRun++;
                        if (HasIndirectBranchOrCall(textBytes, textOff, insLimit))
                        {
                            zeroBlr++;
                        }
                    }
                }

                if (lastDesertEnd > cgSlot && lastDesertEnd < firstPostAnchorSlot)
                {
                    // Walk back at most 32 short non-indirect-branch leaf functions if assembly begins with simple getters.
                    var backSteps = 0;
                    var cur = lastDesertEnd;
                    while (cur > cgSlot + 1 && backSteps < 32)
                    {
                        var prev = cur - 1;
                        while (prev > cgSlot && dense[prev] == 0) prev--;
                        if (prev <= cgSlot) break;
                        var prevVa = dense[prev];
                        var nextVa = dense[cur];
                        var sz = (long)(nextVa - prevVa);
                        if (sz <= 0 || sz > 32) break;
                        var prevIns = (int)(sz / 4);
                        var prevOff = (int)(prevVa - textVa);
                        if (HasIndirectBranchOrCall(textBytes, prevOff, prevIns)) break;
                        cur = prev;
                        backSteps++;
                    }
                    return cur;
                }
            }

            // Small-binary fallback: RuntimeInvoker thunks do not reference ADRP pages.
            for (var k = cgSlot + 1; k < firstPostAnchorSlot; k++)
            {
                var va = dense[k];
                if (va == 0) continue;
                ulong nva = 0;
                for (var j = k + 1; j <= firstPostAnchorSlot; j++)
                {
                    if (dense[j] != 0) { nva = dense[j]; break; }
                }
                if (nva <= va) nva = va + 64;
                var insLimit = (int)Math.Min(100, Math.Max(1, (long)(nva - va) / 4));
                var textOff = (int)(va - textVa);
                for (var wIdx = 0; wIdx < insLimit && textOff + (wIdx + 1) * 4 <= textBytes.Length; wIdx++)
                {
                    var w = BitConverter.ToUInt32(textBytes, textOff + wIdx * 4);
                    if ((w & 0x9F000000u) == 0x90000000u)
                    {
                        return k;
                    }
                }
            }

            return firstPostAnchorSlot;
        }

        private static List<GlobalAnchor> RunWeightedLis(List<GlobalAnchor> hits, int numImgs)
        {
            hits.Sort((a, b) =>
            {
                var c = a.Slot.CompareTo(b.Slot);
                return c != 0 ? c : a.ImgRank.CompareTo(b.ImgRank);
            });

            var bitWeight = new int[numImgs + 2];
            var bitIdx = new int[numImgs + 2];
            Array.Fill(bitIdx, -1);

            void BitUpdate(int rank, int wt, int hitIdx)
            {
                for (var x = rank + 1; x <= numImgs + 1; x += x & -x)
                {
                    if (wt > bitWeight[x])
                    {
                        bitWeight[x] = wt;
                        bitIdx[x] = hitIdx;
                    }
                }
            }

            (int bestWt, int bestHit) BitQuery(int rank)
            {
                var bestW = 0;
                var bestH = -1;
                for (var x = rank + 1; x > 0; x -= x & -x)
                {
                    if (bitWeight[x] > bestW)
                    {
                        bestW = bitWeight[x];
                        bestH = bitIdx[x];
                    }
                }
                return (bestW, bestH);
            }

            var parent = new int[hits.Count];
            Array.Fill(parent, -1);
            var overallBestW = 0;
            var overallBestIdx = -1;

            for (var i = 0; i < hits.Count; i++)
            {
                var h = hits[i];
                var (prevW, prevIdx) = BitQuery(h.ImgRank);
                var curW = prevW + h.Weight;
                parent[i] = prevIdx;
                BitUpdate(h.ImgRank, curW, i);
                if (curW > overallBestW)
                {
                    overallBestW = curW;
                    overallBestIdx = i;
                }
            }

            var kept = new List<GlobalAnchor>();
            for (var c = overallBestIdx; c != -1; c = parent[c])
            {
                kept.Add(hits[c]);
            }
            kept.Reverse();
            return kept;
        }

        private static List<GlobalAnchor>[] FindWindowAnchorsWithFenwickLis(
            ulong[] dense,
            int lastCodeSlot,
            int cgSlot,
            bool[] altMask,
            ulong r2First,
            byte[] textBytes,
            ulong textVa,
            int numImgs,
            Dictionary<ulong, CstrTag> cstrGlobalMap,
            HashSet<ulong> cstrGlobalPages,
            Dictionary<ulong, List<CstrTag>> cstrMultiMap,
            HashSet<ulong> cstrMultiPages,
            Dictionary<ulong, CstrTag> funcGlobalAnchors,
            Dictionary<ulong, List<CstrTag>> delMultiFuncMap)
        {
            var rawHits = new List<GlobalAnchor>(4096);
            var rawMultiHits = new List<(int slot, List<CstrTag> cands)>(512);
            var hasMultiCstr = cstrMultiMap != null && cstrMultiMap.Count > 0 && cstrMultiPages != null && cstrMultiPages.Count > 0;
            var hasMultiDel = delMultiFuncMap != null && delMultiFuncMap.Count > 0;
            var r0NextIdx = BuildNextNonZeroSlotTable(dense, lastCodeSlot);
            var regs = new ulong[32];
            var regValid = new bool[32];

            for (var k = 0; k <= lastCodeSlot; k++)
            {
                if (altMask[k] || k == cgSlot || dense[k] == 0) continue;
                var va = dense[k];
                if (funcGlobalAnchors != null && funcGlobalAnchors.TryGetValue(va, out var funcTag))
                {
                    rawHits.Add(new GlobalAnchor(k, funcTag.Rank, funcTag.Weight, funcTag.ImgIdx, funcTag.MethodSeq));
                    continue;
                }
                if (hasMultiDel && delMultiFuncMap.TryGetValue(va, out var dMulti))
                {
                    rawMultiHits.Add((k, dMulti));
                }
                var nIdx = r0NextIdx[k];
                var nva = nIdx <= lastCodeSlot ? dense[nIdx] : r2First;
                if (nva <= va) nva = va + 128;
                var insCount = (int)Math.Min(128, Math.Max(1, (long)(nva - va) / 4));

                Array.Clear(regValid, 0, 32);
                var cur = va;
                var textOff = (int)(va - textVa);

                for (var wIdx = 0; wIdx < insCount && textOff + (wIdx + 1) * 4 <= textBytes.Length; wIdx++)
                {
                    var w = BitConverter.ToUInt32(textBytes, textOff + wIdx * 4);
                    if ((w & 0x9F000000u) == 0x90000000u)
                    {
                        var rd = (int)(w & 0x1Fu);
                        var imm = (int)((((w >> 5) & 0x7FFFFu) << 2) | ((w >> 29) & 3u));
                        if ((imm & 0x100000) != 0) imm -= 0x200000;
                        var pg = (cur & ~0xFFFuL) + (ulong)((long)imm << 12);
                        if (rd != 31 && (cstrGlobalPages.Contains(pg) || (hasMultiCstr && cstrMultiPages.Contains(pg))))
                        {
                            regs[rd] = pg;
                            regValid[rd] = true;
                        }
                        else if (rd != 31)
                        {
                            regValid[rd] = false;
                        }
                    }
                    else if ((w & 0xFF800000u) == 0x91000000u)
                    {
                        var rd = (int)(w & 0x1Fu);
                        var rn = (int)((w >> 5) & 0x1Fu);
                        if (rn != 31 && regValid[rn])
                        {
                            var addImm = ((w >> 10) & 0xFFFuL) << (((w >> 22) & 1u) != 0 ? 12 : 0);
                            var t = regs[rn] + addImm;
                            if (cstrGlobalMap.TryGetValue(t, out var tag))
                            {
                                rawHits.Add(new GlobalAnchor(k, tag.Rank, tag.Weight, tag.ImgIdx, tag.MethodSeq, tag.ApproxSeq));
                            }
                            else if (hasMultiCstr && cstrMultiMap.TryGetValue(t, out var mTags))
                            {
                                rawMultiHits.Add((k, mTags));
                            }
                        }
                        if (rd != 31)
                        {
                            regValid[rd] = false;
                        }
                    }
                    else if ((w & 0x3B000000u) == 0x39000000u ||
                             (w & 0x7F000000u) == 0x58000000u ||
                             (w & 0x1F800000u) == 0x12800000u ||
                             (w & 0x7FE00000u) == 0x2A000000u)
                    {
                        var rd = (int)(w & 0x1Fu);
                        if (rd != 31)
                        {
                            regValid[rd] = false;
                        }
                    }
                    cur += 4;
                }
            }

            var kept = RunWeightedLis(rawHits, numImgs);
            var byImg = new List<GlobalAnchor>[numImgs];
            for (var ii = 0; ii < numImgs; ii++) byImg[ii] = new List<GlobalAnchor>();
            foreach (var h in kept) byImg[h.ImgIdx].Add(h);
            for (var ii = 0; ii < numImgs; ii++)
            {
                var lst = byImg[ii];
                if (lst.Count > 1 && lst.Any(x => x.Weight >= 2))
                {
                    lst.RemoveAll(x => x.Weight == 1);
                }
            }

            // Pass 2: disambiguate multi-image strong hits unique inside Pass-1 monotonic [rA..rB] brackets.
            if (rawMultiHits.Count > 0)
            {
                var surviving = new List<GlobalAnchor>(kept.Count);
                for (var ii = 0; ii < numImgs; ii++) surviving.AddRange(byImg[ii]);
                surviving.Sort((a, b) =>
                {
                    var c = a.Slot.CompareTo(b.Slot);
                    return c != 0 ? c : a.ImgRank.CompareTo(b.ImgRank);
                });

                if (surviving.Count > 0)
                {
                    var bracketCands = new List<GlobalAnchor>[surviving.Count + 1];
                    foreach (var (slot, cands) in rawMultiHits)
                    {
                        // Binary search rightmost surviving anchor with Slot <= slot
                        int lo = 0, hi = surviving.Count - 1, bIdx = -1;
                        while (lo <= hi)
                        {
                            var mid = lo + ((hi - lo) >> 1);
                            if (surviving[mid].Slot <= slot) { bIdx = mid; lo = mid + 1; }
                            else hi = mid - 1;
                        }
                        if (bIdx >= 0 && surviving[bIdx].Slot == slot) continue;

                        var rA = bIdx >= 0 ? surviving[bIdx].ImgRank : 0;
                        var rB = bIdx + 1 < surviving.Count ? surviving[bIdx + 1].ImgRank : numImgs - 1;
                        var uniqueImg = -1;
                        CstrTag chosen = default;
                        var valid = false;
                        foreach (var cand in cands)
                        {
                            if (cand.Rank < rA || cand.Rank > rB) continue;
                            if (!valid)
                            {
                                uniqueImg = cand.ImgIdx;
                                chosen = cand;
                                valid = true;
                            }
                            else if (cand.ImgIdx != uniqueImg)
                            {
                                valid = false;
                                break;
                            }
                            else if (cand.Weight > chosen.Weight)
                            {
                                chosen = cand;
                            }
                        }
                        if (!valid || chosen.Weight < 3) continue;

                        var g = bIdx + 1;
                        bracketCands[g] ??= new List<GlobalAnchor>(8);
                        bracketCands[g].Add(new GlobalAnchor(slot, chosen.Rank, chosen.Weight, chosen.ImgIdx, chosen.MethodSeq, chosen.ApproxSeq));
                    }

                    for (var g = 0; g < bracketCands.Length; g++)
                    {
                        var gc = bracketCands[g];
                        if (gc == null || gc.Count == 0) continue;
                        var gKept = gc.Count == 1 ? gc : RunWeightedLis(gc, numImgs);
                        foreach (var h in gKept)
                        {
                            var lst = byImg[h.ImgIdx];
                            lst.Add(h);
                            if (lst.Count > 1 && lst.Any(x => x.Weight >= 2))
                            {
                                lst.RemoveAll(x => x.Weight == 1);
                            }
                        }
                    }

                    for (var ii = 0; ii < numImgs; ii++)
                    {
                        if (byImg[ii].Count > 1)
                        {
                            byImg[ii].Sort((a, b) => a.Slot.CompareTo(b.Slot));
                        }
                    }
                }
            }
            return byImg;
        }

        private static void ScanCStringAnchors(
            byte[] cstrBytes,
            ulong cstrVa,
            int[] imgRank,
            Il2CppTypeDefinition[] tds,
            int[] methodIdxToSeq,
            int[] tdFirstSeq,
            int[] tdApproxSeq,
            Dictionary<string, List<(int imgIdx, int methodIdx)>> icallGlobal,
            Dictionary<string, List<(int imgIdx, int methodIdx)>> pinvGlobal,
            Dictionary<string, List<(int imgIdx, int methodIdx)>> pchkGlobal,
            Dictionary<string, List<(int imgIdx, int tdIdx)>> marshalGlobal,
            Dictionary<string, (int imgIdx, int tdIdx)> tprivMap,
            HashSet<int> delegateMethodSet,
            out Dictionary<ulong, CstrTag> cstrGlobalMap,
            out HashSet<ulong> cstrGlobalPages,
            out Dictionary<ulong, List<CstrTag>> cstrMultiMap,
            out HashSet<ulong> cstrMultiPages,
            out Dictionary<ulong, int>[] cstrLocalByImg,
            out HashSet<ulong>[] cstrLocalPagesByImg,
            out HashSet<ulong> marshalAllCstrs,
            out Dictionary<ulong, (int imgIdx, int firstSeq)> marshalAnchors,
            out Dictionary<ulong, string> p0CstrMap,
            out HashSet<ulong> p0CstrPages,
            out HashSet<ulong> delThisCstrVas,
            out HashSet<ulong> lStrVas,
            out HashSet<ulong> lStrPages)
        {
            var numImgs = imgRank.Length;
            var globalMap = new Dictionary<ulong, CstrTag>(4096);
            var globalPages = new HashSet<ulong>(2048);
            var multiMap = new Dictionary<ulong, List<CstrTag>>(2048);
            var multiPages = new HashSet<ulong>(1024);
            var localByImg = new Dictionary<ulong, int>[numImgs];
            var localPagesByImg = new HashSet<ulong>[numImgs];
            marshalAllCstrs = new HashSet<ulong>(1024);
            marshalAnchors = new Dictionary<ulong, (int imgIdx, int firstSeq)>(1024);
            p0CstrMap = new Dictionary<ulong, string>(4096);
            p0CstrPages = new HashSet<ulong>(1024);
            delThisCstrVas = new HashSet<ulong>(4);
            lStrVas = new HashSet<ulong>(2048);
            lStrPages = new HashSet<ulong>(1024);

            // Build per-image unique lookup helpers where needed while keeping O(N) cstring pass
            static bool HasSingleImage<T>(List<(int imgIdx, T item)> list, out int singleImg, out bool isUniqueMethod, out T singleItem)
            {
                singleImg = list[0].imgIdx;
                singleItem = list[0].item;
                isUniqueMethod = list.Count == 1;
                for (var i = 1; i < list.Count; i++)
                {
                    if (list[i].imgIdx != singleImg)
                    {
                        isUniqueMethod = false;
                        return false;
                    }
                }
                return true;
            }

            void AddGlobal(ulong va, int ii, int weight, int methodIdx, bool isExact, int tdIdx = -1, int seqOverride = -1)
            {
                var seq = seqOverride >= 0 ? seqOverride : (methodIdx >= 0 && methodIdx < methodIdxToSeq.Length ? methodIdxToSeq[methodIdx] : -1);
                var approx = seq >= 0 ? seq : (tdIdx >= 0 && tdIdx < tdApproxSeq.Length ? tdApproxSeq[tdIdx] : -1);
                if (globalMap.TryGetValue(va, out var prev) && prev.Weight >= weight) return;
                globalMap[va] = new CstrTag(imgRank[ii], ii, weight, methodIdx, seq, isExact, tdIdx, approx);
                globalPages.Add(va & ~0xFFFuL);
            }

            void AddLocal(ulong va, int ii, int methodIdx)
            {
                if (methodIdx < 0 || methodIdx >= methodIdxToSeq.Length) return;
                var seq = methodIdxToSeq[methodIdx];
                if (seq < 0) return;
                localByImg[ii] ??= new Dictionary<ulong, int>();
                localByImg[ii][va] = seq;
                localPagesByImg[ii] ??= new HashSet<ulong>();
                localPagesByImg[ii].Add(va & ~0xFFFuL);
            }

            void RecordMethodHit(ulong va, int ii, int methodIdx, bool imgSingle, bool uniqueGlobal, int imgWeight, Dictionary<string, List<(int imgIdx, int methodIdx)>> map, string key)
            {
                if (imgSingle)
                {
                    var wt = uniqueGlobal ? 5 : imgWeight;
                    AddGlobal(va, ii, wt, methodIdx, uniqueGlobal);
                    if (uniqueGlobal) AddLocal(va, ii, methodIdx);
                    return;
                }

                // Not globally unique to one image -> record local unique entries and per-image candidate tags for bracket disambiguation.
                var list = map[key];
                var seenByImg = new Dictionary<int, (int firstMi, int cnt)>();
                foreach (var (im, mi) in list)
                {
                    if (seenByImg.TryGetValue(im, out var cur))
                        seenByImg[im] = (cur.firstMi, cur.cnt + 1);
                    else
                        seenByImg[im] = (mi, 1);
                }
                var multiList = new List<CstrTag>(seenByImg.Count);
                foreach (var kv in seenByImg)
                {
                    if (kv.Value.cnt == 1)
                    {
                        var mi = kv.Value.firstMi;
                        AddLocal(va, kv.Key, mi);
                        var seq = mi >= 0 && mi < methodIdxToSeq.Length ? methodIdxToSeq[mi] : -1;
                        multiList.Add(new CstrTag(imgRank[kv.Key], kv.Key, 5, mi, seq, true, -1));
                    }
                    else
                    {
                        multiList.Add(new CstrTag(imgRank[kv.Key], kv.Key, imgWeight, -1, -1, false, -1));
                    }
                }
                if (multiList.Count > 0 && (!multiMap.TryGetValue(va, out var prevMulti) || multiList.Count < prevMulti.Count))
                {
                    multiMap[va] = multiList;
                    multiPages.Add(va & ~0xFFFuL);
                }
            }

            var len = cstrBytes.Length;
            var pos = 0;
            while (pos < len)
            {
                var nul = Array.IndexOf(cstrBytes, (byte)0, pos);
                if (nul < 0) nul = len;
                var slen = nul - pos;
                if (slen >= 3 && slen <= 10 && cstrBytes[pos] == (byte)'L' && cstrBytes[pos + 1] == (byte)'_')
                {
                    var allDigits = true;
                    for (var dp = pos + 2; dp < nul; dp++)
                    {
                        if (cstrBytes[dp] < (byte)'0' || cstrBytes[dp] > (byte)'9')
                        {
                            allDigits = false;
                            break;
                        }
                    }
                    if (allDigits)
                    {
                        var lva = cstrVa + (ulong)pos;
                        lStrVas.Add(lva);
                        lStrPages.Add(lva & ~0xFFFuL);
                    }
                }
                if (slen >= 4 && slen <= 512)
                {
                    var s = Encoding.ASCII.GetString(cstrBytes, pos, slen);
                    var va = cstrVa + (ulong)pos;

                    if (s == "Delegate to an instance method cannot have null 'this'.")
                    {
                        delThisCstrVas.Add(va);
                    }

                    // 1. PCHK: ___<digits>_<name>
                    if (s[0] == '_' && s.Length >= 6 && s[1] == '_' && s[2] == '_' && char.IsDigit(s[3]))
                    {
                        if (s[3] == '0' && s[4] == '_')
                        {
                            p0CstrMap[va] = s;
                            p0CstrPages.Add(va & ~0xFFFuL);
                        }
                        if (pchkGlobal.TryGetValue(s, out var pl))
                        {
                            var allDelegateMethods = delegateMethodSet != null && delegateMethodSet.Count > 0 && pl.All(x => delegateMethodSet.Contains(x.methodIdx));
                            if (!allDelegateMethods)
                            {
                                var imgSingle = HasSingleImage(pl, out var ii, out var uniq, out var mi);
                                RecordMethodHit(va, ii, mi, imgSingle, uniq, 3, pchkGlobal, s);
                            }
                        }
                    }

                    // 2. ICALL: "<Type>::<Method>(" inside full C string
                    var colIdx = s.IndexOf("::", StringComparison.Ordinal);
                    if (colIdx > 0)
                    {
                        var parenIdx = s.IndexOf('(', colIdx + 2);
                        if (parenIdx > colIdx + 2)
                        {
                            var st = colIdx - 1;
                            while (st >= 0 && IsIdentChar(s[st])) st--;
                            st++;
                            if (st < colIdx)
                            {
                                var key = s.Substring(st, parenIdx - st + 1);
                                if (icallGlobal.TryGetValue(key, out var il))
                                {
                                    var imgSingle = HasSingleImage(il, out var ii, out var uniq, out var mi);
                                    RecordMethodHit(va, ii, mi, imgSingle, uniq, 5, icallGlobal, key);
                                }
                            }
                        }
                    }

                    // 3. MARSHAL: "Cannot marshal field '<f>' of type '<t>'"
                    var marshPos = s.IndexOf("Cannot marshal field '", StringComparison.Ordinal);
                    if (marshPos >= 0)
                    {
                        marshalAllCstrs.Add(va);
                        var endQuote2 = s.LastIndexOf('\'');
                        if (endQuote2 > marshPos + 22)
                        {
                            var key = s.Substring(marshPos, endQuote2 - marshPos + 1);
                            if (marshalGlobal.TryGetValue(key, out var ml) &&
                                HasSingleImage(ml, out var ii, out _, out _))
                            {
                                var hasMethods = ml.Any(x => tds[x.tdIdx].method_count > 0);
                                var tdIdx0 = ml[0].tdIdx;
                                var allSameTd = true;
                                for (var mi = 1; mi < ml.Count; mi++)
                                {
                                    if (ml[mi].tdIdx != tdIdx0)
                                    {
                                        allSameTd = false;
                                        break;
                                    }
                                }
                                var firstSeq = hasMethods && allSameTd ? tdFirstSeq[tdIdx0] : -1;
                                AddGlobal(va, ii, hasMethods ? 2 : 1, -1, false, tdIdx0, firstSeq);
                                if (firstSeq >= 0)
                                {
                                    marshalAnchors[va] = (ii, firstSeq);
                                }
                            }
                        }
                    }

                    // 4. PINV: exact C identifier >= 6 chars
                    if (s.Length >= 6 && IsPlainIdentifier(s) && pinvGlobal.TryGetValue(s, out var pinvL))
                    {
                        var imgSingle = HasSingleImage(pinvL, out var ii, out var uniq, out var mi);
                        RecordMethodHit(va, ii, mi, imgSingle, uniq, 3, pinvGlobal, s);
                    }

                    // 5. TPRIV: "<TypeName>_t<40_UPPER_HEX>"
                    var tIdx = s.IndexOf("_t", StringComparison.Ordinal);
                    while (tIdx > 0 && tIdx + 42 <= s.Length)
                    {
                        if (IsUpperHex40(s, tIdx + 2))
                        {
                            var hex = s.Substring(tIdx + 2, 40);
                            if (tprivMap.TryGetValue(hex, out var hit))
                            {
                                var isSelfThis = tIdx + 50 <= s.Length && s.AsSpan(tIdx + 42, 8).SequenceEqual("*)__this");
                                AddGlobal(va, hit.imgIdx, isSelfThis ? 2 : 1, -1, false, hit.tdIdx);
                                break;
                            }
                        }
                        tIdx = s.IndexOf("_t", tIdx + 2, StringComparison.Ordinal);
                    }
                }
                pos = nul + 1;
            }
            cstrGlobalMap = globalMap;
            cstrGlobalPages = globalPages;
            cstrMultiMap = multiMap;
            cstrMultiPages = multiPages;
            cstrLocalByImg = localByImg;
            cstrLocalPagesByImg = localPagesByImg;
        }

        private static bool IsIdentChar(char c) =>
            (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') ||
            c == '_' || c == '.' || c == '`' || c == '+' || c == '/' || c == '<' || c == '>';

        private static bool IsPlainIdentifier(string s)
        {
            foreach (var c in s)
            {
                if (!((c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c == '_'))
                    return false;
            }
            return true;
        }

        private static bool IsUpperHex40(string s, int start)
        {
            for (var i = 0; i < 40; i++)
            {
                var c = s[start + i];
                if (!((c >= '0' && c <= '9') || (c >= 'A' && c <= 'F')))
                    return false;
            }
            return true;
        }

        private static string Sha1Utf16LeHex(string input)
        {
            var bytes = Encoding.Unicode.GetBytes(input);
            var hash = SHA1.HashData(bytes);
            return Convert.ToHexString(hash);
        }

        private static bool TryResolveRegistrationAddresses(
            ulong[] dense,
            int cgSlot,
            byte[] textBytes,
            ulong textVa,
            out ulong codeRegistration,
            out ulong metadataRegistration)
        {
            codeRegistration = 0;
            metadataRegistration = 0;
            if (cgSlot < 0 || cgSlot >= dense.Length || dense[cgSlot] == 0)
            {
                return false;
            }
            var va = dense[cgSlot];
            var off = (int)(va - textVa);
            if (off < 0 || off + 16 > textBytes.Length)
            {
                return false;
            }

            var w0 = BitConverter.ToUInt32(textBytes, off);
            if ((w0 & 0x9F000000u) != 0x90000000u)
            {
                return false;
            }

            var regs = new ulong[32];
            var rd0 = (int)(w0 & 0x1Fu);
            var imm0 = (int)((((w0 >> 5) & 0x7FFFFu) << 2) | ((w0 >> 29) & 3u));
            if ((imm0 & 0x100000) != 0) imm0 -= 0x200000;
            regs[rd0] = (va & ~0xFFFuL) + (ulong)((long)imm0 << 12);

            for (var i = 1; i <= 3; i++)
            {
                var w = BitConverter.ToUInt32(textBytes, off + i * 4);
                if ((w & 0xFF800000u) != 0x91000000u) return false;
                var rd = (int)(w & 0x1Fu);
                var rn = (int)((w >> 5) & 0x1Fu);
                var addImm = ((w >> 10) & 0xFFFuL) << (((w >> 22) & 1u) != 0 ? 12 : 0);
                regs[rd] = regs[rn] + addImm;
            }

            codeRegistration = regs[0];
            metadataRegistration = regs[1];
            return codeRegistration != 0 && metadataRegistration != 0;
        }

        private static int FindCodegenRegistrationSlot(ulong[] dense, int lastCodeSlot, bool[] altMask, byte[] textBytes, ulong textVa)
        {
            for (var k = 0; k <= lastCodeSlot; k++)
            {
                if (altMask[k] || dense[k] == 0) continue;
                var off = (int)(dense[k] - textVa);
                if (off < 0 || off + 20 > textBytes.Length) continue;

                var w0 = BitConverter.ToUInt32(textBytes, off);
                var w1 = BitConverter.ToUInt32(textBytes, off + 4);
                var w2 = BitConverter.ToUInt32(textBytes, off + 8);
                var w3 = BitConverter.ToUInt32(textBytes, off + 12);
                var w4 = BitConverter.ToUInt32(textBytes, off + 16);

                if ((w0 & 0x9F000000u) == 0x90000000u &&
                    (w1 & 0xFF800000u) == 0x91000000u &&
                    (w2 & 0xFF800000u) == 0x91000000u &&
                    (w3 & 0xFF800000u) == 0x91000000u &&
                    (w4 & 0xFC000000u) == 0x14000000u)
                {
                    var imm2 = (w2 >> 10) & 0xFFFu;
                    var imm3 = (w3 >> 10) & 0xFFFu;
                    if (imm2 == 0x88 && imm3 == 0x108)
                    {
                        return k;
                    }
                }
            }
            return -1;
        }

        private static bool[] BuildAltZeroMask(ulong[] dense, int monoEnd)
        {
            var mask = new bool[monoEnd];
            var i = 0;
            while (i < monoEnd)
            {
                if (dense[i] == 0)
                {
                    var s = i;
                    while (i < monoEnd && (dense[i] == 0 || (i + 1 < monoEnd && dense[i + 1] == 0) || (i > 0 && dense[i - 1] == 0)))
                    {
                        i++;
                    }
                    if (i - s >= 6)
                    {
                        for (var k = Math.Max(0, s - 1); k < i; k++)
                        {
                            mask[k] = true;
                        }
                    }
                }
                else
                {
                    i++;
                }
            }
            return mask;
        }

        private static int FindMonoEnd(ulong[] dense, ulong r2First)
        {
            ulong prev = 0;
            var seenMidCode = false;
            for (var idx = 0; idx < dense.Length; idx++)
            {
                var v = dense[idx];
                if (v != 0)
                {
                    if (prev > 0x400000)
                    {
                        if (v < prev - 0x400000)
                        {
                            return idx;
                        }
                        if (seenMidCode && ((r2First > 0 && v >= r2First) || v > prev + 0x400000))
                        {
                            return idx;
                        }
                        seenMidCode = true;
                    }
                    prev = v;
                }
            }
            return dense.Length;
        }

        private static int[] BuildNextNonZeroSlotTable(ulong[] dense, int lastCodeSlot)
        {
            var next = new int[lastCodeSlot + 1];
            var curNext = lastCodeSlot + 1;
            for (var k = lastCodeSlot; k >= 0; k--)
            {
                next[k] = curNext;
                if (dense[k] != 0) curNext = k;
            }
            return next;
        }

        private static bool TryFindPointerRuns(
            Macho64 macho,
            IReadOnlyList<MachoSectionInfo> sectionInfos,
            ulong textVa,
            ulong textEnd,
            out PointerRun run0,
            out PointerRun run2,
            out ulong[] dense)
        {
            run0 = default;
            run2 = default;
            dense = Array.Empty<ulong>();

            bool IsTextPtr(ulong v) => v >= textVa && v < textEnd && (v & 3) == 0;

            var runs = new List<PointerRun>();
            foreach (var info in sectionInfos)
            {
                var sec = info.Section;
                // Skip executable sections, zerofill (S_ZEROFILL = 0x1), and tiny sections.
                if (sec.size < 200 * 8 || (sec.flags & 0x80000400u) == 0x80000400u || (sec.flags & 0xFFu) == 1)
                {
                    continue;
                }
                if (info.SegName == "__TEXT" || info.SegName == "__RODATA") continue;

                var bytes = ReadStreamSlice(macho, sec.offset, checked((int)sec.size));
                var numSlots = bytes.Length / 8;
                ulong Slot(int i) => BitConverter.ToUInt64(bytes, i * 8);

                var i = 0;
                while (i < numSlots)
                {
                    if (IsTextPtr(Slot(i)))
                    {
                        var s = i;
                        var j = i;
                        var nzCount = 0;
                        ulong firstVa = 0, lastVa = 0;
                        while (j < numSlots)
                        {
                            var v = Slot(j);
                            if (IsTextPtr(v))
                            {
                                if (firstVa == 0) firstVa = v;
                                lastVa = v;
                                nzCount++;
                                j++;
                            }
                            else if (v == 0 && j + 1 < numSlots && IsTextPtr(Slot(j + 1)) && (j == s || IsTextPtr(Slot(j - 1))))
                            {
                                j++;
                            }
                            else
                            {
                                break;
                            }
                        }
                        if (nzCount >= 200)
                        {
                            runs.Add(new PointerRun(s, j, nzCount, firstVa, lastVa, sec));
                        }
                        i = j;
                    }
                    else
                    {
                        i++;
                    }
                }
            }

            if (runs.Count < 3)
            {
                return false;
            }

            var byCount = runs.OrderByDescending(r => r.NonZeroCount).ToArray();
            run0 = byCount[0];
            run2 = byCount[1];
            foreach (var r in byCount.Skip(1))
            {
                if (r.NonZeroCount >= run0.NonZeroCount / 20 && r.FirstVa > run0.FirstVa)
                {
                    run2 = r;
                    break;
                }
            }

            var run0Len = run0.EndSlot - run0.StartSlot;
            dense = new ulong[run0Len];
            var run0Bytes = ReadStreamSlice(macho, run0.Section.offset + (ulong)run0.StartSlot * 8, run0Len * 8);
            Buffer.BlockCopy(run0Bytes, 0, dense, 0, run0Bytes.Length);
            return true;
        }

        private static ulong ReadSectionU64(Macho64 macho, MachoSection64Bit sec, int slotIndex)
        {
            macho.Position = sec.offset + (ulong)slotIndex * 8;
            return macho.ReadUInt64();
        }

        private static ulong DetectObjectHeaderSize(
            Macho64 macho,
            byte[] textBytes,
            ulong textVa,
            ulong textSize,
            ulong[] allFuncs,
            uint exportTrieOffset,
            uint exportTrieSize,
            ulong textSegmentVmaddr)
        {
            if (exportTrieOffset > 0 && exportTrieSize > 0 && exportTrieOffset + exportTrieSize <= macho.Length)
            {
                var trie = ReadStreamSlice(macho, exportTrieOffset, (int)exportTrieSize);
                if (TryFindExportedSymbol(trie, "_il2cpp_object_header_size", out var symOffset))
                {
                    var symVa = textSegmentVmaddr + symOffset;
                    if (symVa >= textVa && symVa + 4 <= textVa + textSize)
                    {
                        var insn = BitConverter.ToUInt32(textBytes, (int)(symVa - textVa));
                        if ((insn & 0xFFE0001Fu) == 0x52800000u) // MOV W0, #imm
                        {
                            var val = (insn >> 5) & 0xFFFFu;
                            if (val == 8 || val == 16) return val;
                        }
                    }
                }
            }

            // Fallback: count 8/12-byte AdjustorThunks matching ADD X0, X0, #8; B vs #16; B
            var count8 = 0;
            var count16 = 0;
            for (var k = 0; k + 1 < allFuncs.Length; k++)
            {
                var sz = allFuncs[k + 1] - allFuncs[k];
                if (sz != 8 && sz != 12) continue;
                var off = (int)(allFuncs[k] - textVa);
                if (off < 0 || off + 8 > textBytes.Length) continue;
                var w0 = BitConverter.ToUInt32(textBytes, off);
                var w1 = BitConverter.ToUInt32(textBytes, off + 4);
                if ((w1 & 0xFC000000u) != 0x14000000u) continue;
                if (w0 == 0x91002000u) count8++;
                else if (w0 == 0x91004000u) count16++;
            }
            return count8 > count16 ? 8ul : 16ul;
        }

        private static bool TryFindExportedSymbol(byte[] trie, string targetName, out ulong symbolOffset)
        {
            symbolOffset = 0;
            var stack = new Stack<(int nodeOffset, string prefix)>();
            stack.Push((0, string.Empty));

            while (stack.Count > 0)
            {
                var (off, prefix) = stack.Pop();
                if (off < 0 || off >= trie.Length) continue;
                var p = off;
                var termSize = ReadUleb128(trie, ref p);
                if (termSize > 0)
                {
                    if (prefix == targetName)
                    {
                        var flags = ReadUleb128(trie, ref p);
                        if ((flags & 0x08u) == 0) // not re-export
                        {
                            symbolOffset = ReadUleb128(trie, ref p);
                            return true;
                        }
                    }
                    p = off + (int)ReadUleb128At(trie, off, out var termHdrLen) + termHdrLen;
                }
                if (p >= trie.Length) continue;
                var childCount = trie[p++];
                for (var c = 0; c < childCount && p < trie.Length; c++)
                {
                    var nul = Array.IndexOf(trie, (byte)0, p);
                    if (nul < 0) break;
                    var edge = Encoding.UTF8.GetString(trie, p, nul - p);
                    p = nul + 1;
                    var childOff = (int)ReadUleb128(trie, ref p);
                    var nextPrefix = prefix + edge;
                    if (targetName.StartsWith(nextPrefix, StringComparison.Ordinal))
                    {
                        stack.Push((childOff, nextPrefix));
                    }
                }
            }
            return false;
        }

        private static ulong ReadUleb128(byte[] data, ref int pos)
        {
            ulong val = 0;
            var shift = 0;
            while (pos < data.Length)
            {
                var b = data[pos++];
                val |= (ulong)(b & 0x7F) << shift;
                if ((b & 0x80) == 0) break;
                shift += 7;
            }
            return val;
        }

        private static ulong ReadUleb128At(byte[] data, int pos, out int bytesRead)
        {
            var start = pos;
            var val = ReadUleb128(data, ref pos);
            bytesRead = pos - start;
            return val;
        }

        private static ulong[] ParseFunctionStarts(
            Macho64 macho,
            uint foff,
            uint fsz,
            ulong textSegmentVmaddr,
            ulong textVa,
            ulong textEnd)
        {
            var blob = ReadStreamSlice(macho, foff, (int)fsz);
            var list = new List<ulong>(blob.Length / 2);
            var cur = textSegmentVmaddr;
            var p = 0;
            while (p < blob.Length)
            {
                var delta = ReadUleb128(blob, ref p);
                if (delta == 0) break;
                cur += delta;
                if (cur >= textVa && cur < textEnd)
                {
                    list.Add(cur);
                }
            }
            return list.ToArray();
        }

        private static bool TryGetSection(IReadOnlyList<MachoSectionInfo> sectionInfos, string seg, string sect, out MachoSection64Bit result)
        {
            foreach (var info in sectionInfos)
            {
                if (info.SegName == seg && info.Section.sectname == sect)
                {
                    result = info.Section;
                    return true;
                }
            }
            result = null;
            return false;
        }

        private static MachoSection64Bit FindCStringSection(IReadOnlyList<MachoSectionInfo> sectionInfos)
        {
            if (TryGetSection(sectionInfos, "__TEXT", "__cstring", out var s)) return s;
            if (TryGetSection(sectionInfos, "__RODATA", "__cstring", out s)) return s;
            foreach (var info in sectionInfos)
            {
                if (info.Section.sectname == "__cstring") return info.Section;
            }
            return null;
        }

        private static byte[] ReadStreamSlice(Macho64 macho, ulong offset, int count)
        {
            macho.Position = offset;
            return macho.ReadBytes(count);
        }

        private static int LowerBound(ulong[] arr, ulong target)
        {
            var lo = 0;
            var hi = arr.Length;
            while (lo < hi)
            {
                var mid = lo + ((hi - lo) >> 1);
                if (arr[mid] < target) lo = mid + 1;
                else hi = mid;
            }
            return lo;
        }

        private static int LowerBoundList(List<int> list, int target)
        {
            var lo = 0;
            var hi = list.Count;
            while (lo < hi)
            {
                var mid = lo + ((hi - lo) >> 1);
                if (list[mid] < target) lo = mid + 1;
                else hi = mid;
            }
            return lo;
        }

        private static int UpperBound(int[] arr, int target)
        {
            var lo = 0;
            var hi = arr.Length;
            while (lo < hi)
            {
                var mid = lo + ((hi - lo) >> 1);
                if (arr[mid] <= target) lo = mid + 1;
                else hi = mid;
            }
            return lo;
        }
    }
}
