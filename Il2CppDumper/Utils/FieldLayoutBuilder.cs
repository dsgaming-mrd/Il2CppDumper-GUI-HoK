using System;
using System.Collections.Generic;
using static Il2CppDumper.Il2CppConstants;

namespace Il2CppDumper
{
    /// <summary>
    /// Estimates IL2CPP field offsets when MetadataRegistration.fieldOffsets is missing
    /// (Escher BSS / synthetic registration). Matches common 64-bit Mono/IL2CPP layout
    /// closely enough for dump.cs and DummyDll FieldOffset attributes.
    /// </summary>
    public static class FieldLayoutBuilder
    {
        private static readonly int[] PackingTable = { 0, 1, 2, 4, 8, 16, 32, 64, 128 };

        /// <summary>
        /// Per typeDef index: offset for each field in declaration order (display offsets).
        /// -1 for literals / unknown.
        /// </summary>
        public static int[][] Build(Metadata metadata, Il2Cpp il2Cpp)
        {
            var ptrSize = il2Cpp.PointerSize > 0 ? (int)il2Cpp.PointerSize : 8;
            var typeCount = metadata.typeDefs.Length;
            var result = new int[typeCount][];
            var instanceSizes = new int[typeCount]; // total instance size (class includes header)
            var computed = new bool[typeCount];
            var computing = new bool[typeCount];

            // Reverse map: byvalTypeIndex -> typeDef index
            var byvalToTypeDef = new Dictionary<int, int>();
            for (var i = 0; i < typeCount; i++)
            {
                var bv = metadata.typeDefs[i].byvalTypeIndex;
                if (bv >= 0 && !byvalToTypeDef.ContainsKey(bv))
                    byvalToTypeDef[bv] = i;
            }

            int Ensure(int typeDefIndex)
            {
                if (typeDefIndex < 0 || typeDefIndex >= typeCount)
                    return ptrSize * 2;
                if (computed[typeDefIndex])
                    return instanceSizes[typeDefIndex];
                if (computing[typeDefIndex])
                    return ptrSize * 2; // cycle

                computing[typeDefIndex] = true;
                var td = metadata.typeDefs[typeDefIndex];
                var fieldCount = td.field_count;
                var offsets = new int[fieldCount];
                for (var i = 0; i < fieldCount; i++)
                    offsets[i] = -1;

                var packing = GetPacking(td);
                var isValueType = td.IsValueType && !td.IsEnum;
                var isEnum = td.IsEnum;

                // Instance field cursor
                int instCursor;
                if (isEnum)
                {
                    instCursor = 0;
                }
                else if (isValueType)
                {
                    // Display offsets start at 0x8 (memory-dump convention). Embedded size = end - 8.
                    instCursor = 8;
                }
                else
                {
                    // class: start after parent instance size (header included).
                    // HOK iOS memory dumps use first field at 0x8 for System.Object subclasses
                    // (klass-only header style in dump.cs), not 0x10.
                    var objectHeader = 8;
                    instCursor = objectHeader;
                    if (td.parentIndex >= 0 &&
                        il2Cpp.types != null &&
                        td.parentIndex < il2Cpp.types.Length)
                    {
                        var parentType = il2Cpp.types[td.parentIndex];
                        if (parentType != null &&
                            (parentType.type == Il2CppTypeEnum.IL2CPP_TYPE_CLASS ||
                             parentType.type == Il2CppTypeEnum.IL2CPP_TYPE_VALUETYPE) &&
                            parentType.data.klassIndex >= 0 &&
                            parentType.data.klassIndex < typeCount)
                        {
                            var parentTd = metadata.typeDefs[parentType.data.klassIndex];
                            if (!parentTd.IsValueType)
                                instCursor = Ensure((int)parentType.data.klassIndex);
                        }
                    }
                }

                // Static field cursor (thread-static ignored → same stream)
                var staticCursor = 0;

                for (var fi = 0; fi < fieldCount; fi++)
                {
                    var fieldDef = metadata.fieldDefs[td.fieldStart + fi];
                    var fieldType = (fieldDef.typeIndex >= 0 && il2Cpp.types != null && fieldDef.typeIndex < il2Cpp.types.Length)
                        ? il2Cpp.types[fieldDef.typeIndex]
                        : null;

                    var attrs = fieldType?.attrs ?? 0;
                    // Const fields (LITERAL) — or under synthetic, any field with a default-value blob
                    // (types[] loses LITERAL bit so Path/const string would otherwise inflate layout).
                    Il2CppFieldDefaultValue fdv;
                    if ((attrs & FIELD_ATTRIBUTE_LITERAL) != 0 ||
                        (il2Cpp.IsSynthetic &&
                         metadata.GetFieldDefaultValueFromIndex(td.fieldStart + fi, out fdv) &&
                         fdv.dataIndex != -1))
                    {
                        offsets[fi] = -1;
                        continue;
                    }

                    GetFieldSizeAlign(metadata, il2Cpp, byvalToTypeDef, fieldDef.typeIndex, fieldType, ptrSize, Ensure, out var size, out var align);
                    if (packing > 0 && align > packing)
                        align = packing;
                    if (align < 1) align = 1;

                    var lookupIndex = typeDefIndex;
                    if (il2Cpp.ReferenceDump != null &&
                        il2Cpp.ReferenceDump.NewToOldTypeIndices.TryGetValue(typeDefIndex, out var oldIdx))
                    {
                        lookupIndex = oldIdx;
                    }

                    var isStatic = (attrs & FIELD_ATTRIBUTE_STATIC) != 0;
                    var fieldName = metadata.GetStringFromIndex(fieldDef.nameIndex);
                    if (il2Cpp.ReferenceDump != null &&
                        il2Cpp.ReferenceDump.StaticFields.TryGetValue(lookupIndex, out var sf) &&
                        sf.Contains(fieldName))
                    {
                        isStatic = true;
                    }
                    else if (il2Cpp.IsSynthetic &&
                             (fieldName.StartsWith("s_", StringComparison.Ordinal) ||
                              fieldName.StartsWith("S_", StringComparison.Ordinal) ||
                              fieldName.StartsWith("g_", StringComparison.Ordinal) ||
                              fieldName.StartsWith("G_", StringComparison.Ordinal)))
                    {
                        isStatic = true;
                    }
                    if (isStatic)
                    {
                        staticCursor = Align(staticCursor, align);
                        offsets[fi] = staticCursor;
                        staticCursor += size;
                    }
                    else
                    {
                        instCursor = Align(instCursor, align);
                        offsets[fi] = instCursor;
                        instCursor += size;
                    }
                }

                // Final instance size aligned to packing or pointer.
                // Value types used display base 0x8 — strip it for embedded size.
                var finalAlign = packing > 0 ? packing : ptrSize;
                if (finalAlign < 1) finalAlign = 1;
                var rawEnd = instCursor;
                if (isValueType && rawEnd >= 8)
                    rawEnd -= 8;
                instanceSizes[typeDefIndex] = Align(rawEnd, Math.Min(finalAlign, ptrSize));
                if (instanceSizes[typeDefIndex] == 0 && isValueType)
                    instanceSizes[typeDefIndex] = 1;

                result[typeDefIndex] = offsets;
                computed[typeDefIndex] = true;
                computing[typeDefIndex] = false;
                return instanceSizes[typeDefIndex];
            }

            for (var i = 0; i < typeCount; i++)
                Ensure(i);

            return result;
        }

        private static int GetPacking(Il2CppTypeDefinition td)
        {
            // bitfield: bits 7-10 packing index; bit 11 = default packing
            var bits = td.bitfield;
            if (((bits >> 11) & 1) != 0)
                return 0; // default
            var idx = (int)((bits >> 7) & 0xF);
            if (idx >= 0 && idx < PackingTable.Length)
                return PackingTable[idx];
            return 0;
        }

        private static int Align(int value, int align)
        {
            if (align <= 1) return value;
            return (value + align - 1) & ~(align - 1);
        }

        private static void GetFieldSizeAlign(
            Metadata metadata,
            Il2Cpp il2Cpp,
            Dictionary<int, int> byvalToTypeDef,
            int typeIndex,
            Il2CppType fieldType,
            int ptrSize,
            Func<int, int> ensureTypeDefSize,
            out int size,
            out int align)
        {
            size = ptrSize;
            align = ptrSize;

            if (fieldType == null)
            {
                // Try typeDef reverse map
                if (byvalToTypeDef.TryGetValue(typeIndex, out var tdIdx))
                {
                    var td = metadata.typeDefs[tdIdx];
                    if (td.IsValueType)
                    {
                        size = ensureTypeDefSize(tdIdx);
                        align = Math.Min(ptrSize, Math.Max(1, size <= 1 ? 1 : size <= 2 ? 2 : size <= 4 ? 4 : ptrSize));
                        return;
                    }
                }
                return;
            }

            switch (fieldType.type)
            {
                case Il2CppTypeEnum.IL2CPP_TYPE_BOOLEAN:
                case Il2CppTypeEnum.IL2CPP_TYPE_I1:
                case Il2CppTypeEnum.IL2CPP_TYPE_U1:
                    size = 1; align = 1; return;
                case Il2CppTypeEnum.IL2CPP_TYPE_CHAR:
                case Il2CppTypeEnum.IL2CPP_TYPE_I2:
                case Il2CppTypeEnum.IL2CPP_TYPE_U2:
                    size = 2; align = 2; return;
                case Il2CppTypeEnum.IL2CPP_TYPE_I4:
                case Il2CppTypeEnum.IL2CPP_TYPE_U4:
                case Il2CppTypeEnum.IL2CPP_TYPE_R4:
                    size = 4; align = 4; return;
                case Il2CppTypeEnum.IL2CPP_TYPE_I8:
                case Il2CppTypeEnum.IL2CPP_TYPE_U8:
                case Il2CppTypeEnum.IL2CPP_TYPE_R8:
                    size = 8; align = 8; return;
                case Il2CppTypeEnum.IL2CPP_TYPE_I:
                case Il2CppTypeEnum.IL2CPP_TYPE_U:
                case Il2CppTypeEnum.IL2CPP_TYPE_PTR:
                case Il2CppTypeEnum.IL2CPP_TYPE_FNPTR:
                case Il2CppTypeEnum.IL2CPP_TYPE_STRING:
                case Il2CppTypeEnum.IL2CPP_TYPE_CLASS:
                case Il2CppTypeEnum.IL2CPP_TYPE_OBJECT:
                case Il2CppTypeEnum.IL2CPP_TYPE_SZARRAY:
                case Il2CppTypeEnum.IL2CPP_TYPE_ARRAY:
                case Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST:
                    size = ptrSize; align = ptrSize; return;
                case Il2CppTypeEnum.IL2CPP_TYPE_VALUETYPE:
                    {
                        var idx = (int)fieldType.data.klassIndex;
                        if (idx >= 0 && idx < metadata.typeDefs.Length)
                        {
                            var td = metadata.typeDefs[idx];
                            if (td.IsEnum)
                            {
                                // enum underlying usually I4
                                size = 4; align = 4;
                                // try element type
                                if (td.elementTypeIndex >= 0 && il2Cpp.types != null && td.elementTypeIndex < il2Cpp.types.Length)
                                {
                                    GetFieldSizeAlign(metadata, il2Cpp, byvalToTypeDef, td.elementTypeIndex, il2Cpp.types[td.elementTypeIndex], ptrSize, ensureTypeDefSize, out size, out align);
                                }
                                return;
                            }
                            size = ensureTypeDefSize(idx);
                            align = Math.Min(ptrSize, size <= 1 ? 1 : size <= 2 ? 2 : size <= 4 ? 4 : 8);
                            if (align < 1) align = 1;
                            return;
                        }
                        size = ptrSize; align = ptrSize;
                        return;
                    }
                case Il2CppTypeEnum.IL2CPP_TYPE_VAR:
                case Il2CppTypeEnum.IL2CPP_TYPE_MVAR:
                    size = ptrSize; align = ptrSize; return;
                default:
                    size = ptrSize; align = ptrSize; return;
            }
        }
    }
}
