using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;

namespace Il2CppDumper
{
    /// <summary>
    /// Recover per-image methodPointers when CodeRegistration BSS is empty.
    /// Sliding-window search: exact method-count windows of (0|exec) pointers.
    /// </summary>
    public static class MethodPointerScanner
    {
        private sealed class SecScan
        {
            public ulong FilePos;
            public ulong Va;
            public byte[] Valid;   // 1 = 0 or exec
            public byte[] NonZero; // 1 = exec
            public int[] PrefInvalid;
            public int[] PrefNonZero;
            public List<(int start, int length)> ValidBlocks;
        }

        public static int TryAttach(Il2Cpp il2Cpp, Metadata metadata)
        {
            if (il2Cpp is not Macho64 || metadata?.imageDefs == null)
                return 0;

            SectionHelper helper;
            try
            {
                helper = il2Cpp.GetSectionHelper(
                    metadata.methodDefs.Count(x => x.methodIndex >= 0),
                    metadata.typeDefs.Length,
                    metadata.imageDefs.Length);
            }
            catch { return 0; }

            if (helper.Data == null || helper.Exec == null || helper.Data.Count == 0)
                return 0;

            var scans = BuildScans(il2Cpp, helper);
            if (scans.Count == 0)
                return 0;

            var images = new List<(string name, int count)>();
            foreach (var imageDef in metadata.imageDefs)
            {
                var name = metadata.GetStringFromIndex(imageDef.nameIndex);
                var count = 0;
                var typeEnd = imageDef.typeStart + imageDef.typeCount;
                for (var t = imageDef.typeStart; t < typeEnd && t < metadata.typeDefs.Length; t++)
                    count += metadata.typeDefs[t].method_count;
                if (count > 0)
                    images.Add((name, count));
            }

            // Track used VA ranges to avoid double-claim
            var used = new List<(ulong start, ulong end)>();
            var attached = 0;

            // Larger images first — more unique counts
            foreach (var (name, count) in images.OrderByDescending(x => x.count))
            {
                if (count < 1)
                    continue;

                var bestScore = -1;
                SecScan bestScan = null;
                var bestIndex = -1;
                var lockObj = new object();

                // Flatten scans and subtract used intervals to avoid inner overlaps checks
                var searchItems = new List<(SecScan scan, int start, int length)>();
                var scansCount = scans.Count;
                for (var sIdx = 0; sIdx < scansCount; sIdx++)
                {
                    var scan = scans[sIdx];
                    var blocks = scan.ValidBlocks;
                    var blocksCount = blocks.Count;
                    for (var bIdx = 0; bIdx < blocksCount; bIdx++)
                    {
                        var block = blocks[bIdx];
                        if (count <= block.length)
                        {
                            var subs = GetNonOverlappingSubBlocks(scan, block.start, block.length, used);
                            var subsCount = subs.Count;
                            for (var k = 0; k < subsCount; k++)
                            {
                                var sub = subs[k];
                                if (count <= sub.length)
                                {
                                    searchItems.Add((scan, sub.start, sub.length));
                                }
                            }
                        }
                    }
                }

                Parallel.ForEach(searchItems, item =>
                {
                    var scan = item.scan;
                    var start = item.start;
                    var length = item.length;
                    var maxI = start + length - count;
                    var minNz = Math.Max(1, count / 50);

                    for (var i = start; i <= maxI; i++)
                    {
                        var nz = scan.PrefNonZero[i + count] - scan.PrefNonZero[i];
                        if (nz < minNz)
                            continue;

                        var score = nz;
                        if (score > bestScore)
                        {
                            lock (lockObj)
                            {
                                if (score > bestScore)
                                {
                                    bestScore = score;
                                    bestScan = scan;
                                    bestIndex = i;
                                }
                            }
                        }
                    }
                });

                if (bestScan == null || bestIndex < 0)
                    continue;

                try
                {
                    var ptrs = new ulong[count];
                    il2Cpp.Position = bestScan.FilePos + (ulong)bestIndex * 8;
                    var nz = 0;
                    for (var k = 0; k < count; k++)
                    {
                        ptrs[k] = il2Cpp.ReadUInt64();
                        if (ptrs[k] != 0) nz++;
                    }
                    il2Cpp.SetModuleMethodPointers(name, ptrs);
                    var va = bestScan.Va + (ulong)bestIndex * 8;
                    used.Add((va, va + (ulong)count * 8));
                    attached++;
                }
                catch (Exception ex)
                {
                    MainForm.Log($"MethodPointerScanner {name}: {ex.Message}", System.Windows.Media.Brushes.Orange);
                }
            }

            return attached;
        }

        private static List<(int start, int length)> GetNonOverlappingSubBlocks(SecScan scan, int start, int length, List<(ulong start, ulong end)> used)
        {
            var result = new List<(int start, int length)>();
            var usedIntervals = new List<(int start, int end)>();
            var usedCount = used.Count;
            var scanStartVa = scan.Va;
            var scanEndVa = scan.Va + (ulong)scan.Valid.Length * 8;

            for (var i = 0; i < usedCount; i++)
            {
                var u = used[i];
                if (u.start < scanEndVa && u.end > scanStartVa)
                {
                    var uStart = u.start >= scanStartVa ? (int)((u.start - scanStartVa) / 8) : 0;
                    var uEnd = u.end <= scanEndVa ? (int)((u.end - scanStartVa) / 8) : scan.Valid.Length;
                    usedIntervals.Add((uStart, uEnd));
                }
            }

            usedIntervals.Sort((x, y) => x.start.CompareTo(y.start));

            var currentStart = start;
            var blockEnd = start + length;
            var intervalsCount = usedIntervals.Count;

            for (var i = 0; i < intervalsCount; i++)
            {
                var interval = usedIntervals[i];
                if (interval.start >= blockEnd)
                    break;
                if (interval.end <= currentStart)
                    continue;

                if (interval.start > currentStart)
                {
                    result.Add((currentStart, interval.start - currentStart));
                }
                currentStart = Math.Max(currentStart, interval.end);
            }
            if (currentStart < blockEnd)
            {
                result.Add((currentStart, blockEnd - currentStart));
            }

            return result;
        }

        private static List<SecScan> BuildScans(Il2Cpp il2Cpp, SectionHelper helper)
        {
            var list = new List<SecScan>();
            var execMin = helper.Exec.Count > 0 ? helper.Exec.Min(s => s.address) : 0;
            var execMax = helper.Exec.Count > 0 ? helper.Exec.Max(s => s.addressEnd) : 0;

            foreach (var sec in helper.Data)
            {
                if (sec.offsetEnd <= sec.offset + 64)
                    continue;
                var size = sec.offsetEnd - sec.offset;
                var n = (int)(size / 8);
                if (n < 16)
                    continue;

                var valid = new byte[n];
                var nonZero = new byte[n];
                try
                {
                    il2Cpp.Position = sec.offset;
                    var buf = il2Cpp.ReadBytes((int)size);
                    
                    Parallel.For(0, n, i =>
                    {
                        var p = BitConverter.ToUInt64(buf, i * 8);
                        if (p == 0)
                        {
                            valid[i] = 1;
                        }
                        else if (p >= execMin && p < execMax && InExec(helper, p, execMin, execMax))
                        {
                            valid[i] = 1;
                            nonZero[i] = 1;
                        }
                    });
                }
                catch { continue; }

                var prefInv = new int[n + 1];
                var prefNz = new int[n + 1];
                for (var i = 0; i < n; i++)
                {
                    prefInv[i + 1] = prefInv[i] + (valid[i] == 0 ? 1 : 0);
                    prefNz[i + 1] = prefNz[i] + nonZero[i];
                }

                // Find contiguous valid blocks
                var validBlocks = new List<(int start, int length)>();
                var runStart = -1;
                for (var i = 0; i < n; i++)
                {
                    if (valid[i] == 1)
                    {
                        if (runStart == -1) runStart = i;
                    }
                    else
                    {
                        if (runStart != -1)
                        {
                            validBlocks.Add((runStart, i - runStart));
                            runStart = -1;
                        }
                    }
                }
                if (runStart != -1)
                {
                    validBlocks.Add((runStart, n - runStart));
                }

                list.Add(new SecScan
                {
                    FilePos = sec.offset,
                    Va = sec.address,
                    Valid = valid,
                    NonZero = nonZero,
                    PrefInvalid = prefInv,
                    PrefNonZero = prefNz,
                    ValidBlocks = validBlocks
                });
            }
            return list;
        }

        private static bool InExec(SectionHelper helper, ulong va, ulong execMin, ulong execMax)
        {
            if (va < execMin || va >= execMax)
                return false;
            var execs = helper.Exec;
            var count = execs.Count;
            for (var i = 0; i < count; i++)
            {
                var s = execs[i];
                if (va >= s.address && va < s.addressEnd)
                    return true;
            }
            return false;
        }
    }
}
