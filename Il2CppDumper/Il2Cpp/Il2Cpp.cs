using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;

namespace Il2CppDumper
{
    public abstract class Il2Cpp : BinaryStream
    {
        private Il2CppMetadataRegistration pMetadataRegistration;
        private Il2CppCodeRegistration pCodeRegistration;
        public ulong[] methodPointers;
        public ulong[] genericMethodPointers;
        public ulong[] invokerPointers;
        public ulong[] customAttributeGenerators;
        public ulong[] reversePInvokeWrappers;
        public ulong[] unresolvedVirtualCallPointers;
        private ulong[] fieldOffsets;
        public Il2CppType[] types;
        private readonly Dictionary<ulong, Il2CppType> typeDic = new();
        public ulong[] metadataUsages;
        private Il2CppGenericMethodFunctionsDefinitions[] genericMethodTable;
        public ulong[] genericInstPointers;
        public Il2CppGenericInst[] genericInsts;
        public Il2CppMethodSpec[] methodSpecs;
        public Dictionary<int, List<Il2CppMethodSpec>> methodDefinitionMethodSpecs = new();
        public Dictionary<Il2CppMethodSpec, ulong> methodSpecGenericMethodPointers = new();
        private bool fieldOffsetsArePointers;
        protected long metadataUsagesCount;
        public Dictionary<string, Il2CppCodeGenModule> codeGenModules;
        public Dictionary<string, ulong[]> codeGenModuleMethodPointers;
        public Dictionary<string, Dictionary<uint, Il2CppRGCTXDefinition[]>> rgctxsDictionary;
        public bool IsDumped;
        private int[][] syntheticFieldOffsets;
        public bool IsSynthetic { get; private set; }
        public ReferenceDumpData ReferenceDump { get; set; }
        public ulong CodeRegistrationAddress { get; set; }
        public ulong MetadataRegistrationAddress { get; set; }
        public bool HasRegistrationAddresses => CodeRegistrationAddress != 0 && MetadataRegistrationAddress != 0;

        public abstract ulong MapVATR(ulong addr);
        public abstract ulong MapRTVA(ulong addr);
        public abstract bool Search();
        public abstract bool PlusSearch(int methodCount, int typeDefinitionsCount, int imageCount);
        public abstract bool SymbolSearch();
        public abstract SectionHelper GetSectionHelper(int methodCount, int typeDefinitionsCount, int imageCount);
        public abstract bool CheckDump();

        protected Il2Cpp(Stream stream) : base(stream) { }

        public void SetProperties(double version, long metadataUsagesCount)
        {
            Version = version;
            this.metadataUsagesCount = metadataUsagesCount;
        }

        protected bool AutoPlusInit(ulong codeRegistration, ulong metadataRegistration)
        {
            if (codeRegistration != 0)
            {
			    var limit = this is WebAssemblyMemory ? 0x35000u : 0x50000u; //TODO
                if (Version >= 24.2)
                {
                    pCodeRegistration = MapVATR<Il2CppCodeRegistration>(codeRegistration);
                    // Metadata v38/v39 (Unity 6000.3) share the v31 binary
                    // Il2CppCodeRegistration layout, so the same disambiguation
                    // applies. We never downgrade a confirmed v38+ metadata file.
                    if (Version == 31 || Version >= 38)
                    {
                        if (pCodeRegistration.genericMethodPointersCount > limit)
                        {
                            codeRegistration -= PointerSize * 2;
                        }
                        else if (Version == 31)
                        {
                            Version = 29;
                            Console.WriteLine($"Change il2cpp version to: {Version}");
                        }
                    }
                    if (Version == 29)
                    {
                        if (pCodeRegistration.genericMethodPointersCount > limit) //TODO
                        {
                            Version = 29.1;
                            codeRegistration -= PointerSize * 2;
                            Console.WriteLine($"Change il2cpp version to: {Version}");
                        }
                    }
                    if (Version == 27)
                    {
                        if (pCodeRegistration.reversePInvokeWrapperCount > limit) //TODO
                        {
                            Version = 27.1;
                            codeRegistration -= PointerSize;
                            MainForm.Log($"Change il2cpp version to: {Version}");
                        }
                    }
                    if (Version == 24.4)
                    {
                        codeRegistration -= PointerSize * 2;
                        if (pCodeRegistration.reversePInvokeWrapperCount > limit) //TODO
                        {
                            Version = 24.5;
                            codeRegistration -= PointerSize;
                            MainForm.Log($"Change il2cpp version to: {Version}");
                        }
                    }
                    if (Version == 24.2)
                    {
                        if (pCodeRegistration.interopDataCount == 0) //TODO
                        {
                            Version = 24.3;
                            codeRegistration -= PointerSize * 2;
                            MainForm.Log($"Change il2cpp version to: {Version}");
                        }
                    }
                }
            }
            if (codeRegistration != 0 && metadataRegistration != 0)
            {
                MainForm.Log("CodeRegistration : {0:x}", codeRegistration);
                MainForm.Log("MetadataRegistration : {0:x}", metadataRegistration);
                Init(codeRegistration, metadataRegistration);
                return true;
            }
            return false;
        }

        public virtual void Init(ulong codeRegistration, ulong metadataRegistration)
        {
            CodeRegistrationAddress = codeRegistration;
            MetadataRegistrationAddress = metadataRegistration;
            pCodeRegistration = MapVATR<Il2CppCodeRegistration>(codeRegistration);
            var limit = this is WebAssemblyMemory ? 0x35000u : 0x50000u; //TODO
            if (Version == 27 && pCodeRegistration.invokerPointersCount > limit) //TODO
            {
                Version = 27.1;
                MainForm.Log($"Change il2cpp version to: {Version}");
                pCodeRegistration = MapVATR<Il2CppCodeRegistration>(codeRegistration);
            }
            if (Version == 27.1)
            {
                var pCodeGenModules = MapVATR<ulong>(pCodeRegistration.codeGenModules, pCodeRegistration.codeGenModulesCount);
                foreach (var pCodeGenModule in pCodeGenModules)
                {
                    var codeGenModule = MapVATR<Il2CppCodeGenModule>(pCodeGenModule);
                    if (codeGenModule.rgctxsCount > 0)
                    {
                        var rgctxs = MapVATR<Il2CppRGCTXDefinition>(codeGenModule.rgctxs, codeGenModule.rgctxsCount);
                        if (rgctxs.All(x => x.data.rgctxDataDummy > limit))
                        {
                            Version = 27.2;
                            Console.WriteLine($"Change il2cpp version to: {Version}");
                        }
                        break;
                    }
                }
            }
            if (Version == 24.4 && pCodeRegistration.invokerPointersCount > limit) //TODO
            {
                Version = 24.5;
                MainForm.Log($"Change il2cpp version to: {Version}");
                pCodeRegistration = MapVATR<Il2CppCodeRegistration>(codeRegistration);
            }
            if (Version == 24.2 && pCodeRegistration.codeGenModules == 0) //TODO
            {
                Version = 24.3;
                MainForm.Log($"Change il2cpp version to: {Version}");
                pCodeRegistration = MapVATR<Il2CppCodeRegistration>(codeRegistration);
            }
            pMetadataRegistration = MapVATR<Il2CppMetadataRegistration>(metadataRegistration);
            genericMethodPointers = MapVATR<ulong>(pCodeRegistration.genericMethodPointers, pCodeRegistration.genericMethodPointersCount);
            invokerPointers = MapVATR<ulong>(pCodeRegistration.invokerPointers, pCodeRegistration.invokerPointersCount);
            if (Version < 27)
            {
                customAttributeGenerators = MapVATR<ulong>(pCodeRegistration.customAttributeGenerators, pCodeRegistration.customAttributeCount);
            }
            if (Version > 16 && Version < 27)
            {
                metadataUsages = MapVATR<ulong>(pMetadataRegistration.metadataUsages, metadataUsagesCount);
            }
            if (Version >= 22)
            {
                if (pCodeRegistration.reversePInvokeWrapperCount != 0)
                    reversePInvokeWrappers = MapVATR<ulong>(pCodeRegistration.reversePInvokeWrappers, pCodeRegistration.reversePInvokeWrapperCount);
                if (pCodeRegistration.unresolvedVirtualCallCount != 0)
                    unresolvedVirtualCallPointers = MapVATR<ulong>(pCodeRegistration.unresolvedVirtualCallPointers, pCodeRegistration.unresolvedVirtualCallCount);
            }
            genericInstPointers = MapVATR<ulong>(pMetadataRegistration.genericInsts, pMetadataRegistration.genericInstsCount);
            genericInsts = Array.ConvertAll(genericInstPointers, MapVATR<Il2CppGenericInst>);
            fieldOffsetsArePointers = Version > 21;
            if (Version == 21)
            {
                var fieldTest = MapVATR<uint>(pMetadataRegistration.fieldOffsets, 6);
                fieldOffsetsArePointers = fieldTest[0] == 0 && fieldTest[1] == 0 && fieldTest[2] == 0 && fieldTest[3] == 0 && fieldTest[4] == 0 && fieldTest[5] > 0;
            }
            if (fieldOffsetsArePointers)
            {
                fieldOffsets = MapVATR<ulong>(pMetadataRegistration.fieldOffsets, pMetadataRegistration.fieldOffsetsCount);
            }
            else
            {
                fieldOffsets = Array.ConvertAll(MapVATR<uint>(pMetadataRegistration.fieldOffsets, pMetadataRegistration.fieldOffsetsCount), x => (ulong)x);
            }
            var pTypes = MapVATR<ulong>(pMetadataRegistration.types, pMetadataRegistration.typesCount);
            types = new Il2CppType[pMetadataRegistration.typesCount];
            for (var i = 0; i < pMetadataRegistration.typesCount; ++i)
            {
                types[i] = MapVATR<Il2CppType>(pTypes[i]);
                 types[i].Init(Version);
                typeDic.Add(pTypes[i], types[i]);
            }
            if (Version >= 24.2)
            {
                var pCodeGenModules = MapVATR<ulong>(pCodeRegistration.codeGenModules, pCodeRegistration.codeGenModulesCount);
                codeGenModules = new Dictionary<string, Il2CppCodeGenModule>(pCodeGenModules.Length, StringComparer.Ordinal);
                codeGenModuleMethodPointers = new Dictionary<string, ulong[]>(pCodeGenModules.Length, StringComparer.Ordinal);
                rgctxsDictionary = new Dictionary<string, Dictionary<uint, Il2CppRGCTXDefinition[]>>(pCodeGenModules.Length, StringComparer.Ordinal);
                foreach (var pCodeGenModule in pCodeGenModules)
                {
                    var codeGenModule = MapVATR<Il2CppCodeGenModule>(pCodeGenModule);
                    var moduleName = ReadStringToNull(MapVATR(codeGenModule.moduleName));
                    codeGenModules.Add(moduleName, codeGenModule);
                    ulong[] methodPointers;
                    try
                    {
                        methodPointers = MapVATR<ulong>(codeGenModule.methodPointers, codeGenModule.methodPointerCount);
                    }
                    catch
                    {
                        methodPointers = new ulong[codeGenModule.methodPointerCount];
                    }
                    codeGenModuleMethodPointers.Add(moduleName, methodPointers);

                    var rgctxsDefDictionary = new Dictionary<uint, Il2CppRGCTXDefinition[]>();
                    rgctxsDictionary.Add(moduleName, rgctxsDefDictionary);
                    if (codeGenModule.rgctxsCount > 0)
                    {
                        var rgctxs = MapVATR<Il2CppRGCTXDefinition>(codeGenModule.rgctxs, codeGenModule.rgctxsCount);
                        var rgctxRanges = MapVATR<Il2CppTokenRangePair>(codeGenModule.rgctxRanges, codeGenModule.rgctxRangesCount);
                        foreach (var rgctxRange in rgctxRanges)
                        {
                            var rgctxDefs = new Il2CppRGCTXDefinition[rgctxRange.range.length];
                            Array.Copy(rgctxs, rgctxRange.range.start, rgctxDefs, 0, rgctxRange.range.length);
                            rgctxsDefDictionary.Add(rgctxRange.token, rgctxDefs);
                        }
                    }
                }
            }
            else
            {
                methodPointers = MapVATR<ulong>(pCodeRegistration.methodPointers, pCodeRegistration.methodPointersCount);
            }
            genericMethodTable = MapVATR<Il2CppGenericMethodFunctionsDefinitions>(pMetadataRegistration.genericMethodTable, pMetadataRegistration.genericMethodTableCount);
            methodSpecs = MapVATR<Il2CppMethodSpec>(pMetadataRegistration.methodSpecs, pMetadataRegistration.methodSpecsCount);
            foreach (var table in genericMethodTable)
            {
                var methodSpec = methodSpecs[table.genericMethodIndex];
                var methodDefinitionIndex = methodSpec.methodDefinitionIndex;
                if (!methodDefinitionMethodSpecs.TryGetValue(methodDefinitionIndex, out var list))
                {
                    list = new List<Il2CppMethodSpec>();
                    methodDefinitionMethodSpecs.Add(methodDefinitionIndex, list);
                }
                list.Add(methodSpec);
                methodSpecGenericMethodPointers.Add(methodSpec, genericMethodPointers[table.indices.methodIndex]);
            }
        }

        public T MapVATR<T>(ulong addr) where T : new()
        {
            return ReadClass<T>(MapVATR(addr));
        }

        public T[] MapVATR<T>(ulong addr, ulong count) where T : new()
        {
            return ReadClassArray<T>(MapVATR(addr), count);
        }
		
        public T[] MapVATR<T>(ulong addr, long count) where T : new()
        {
            return ReadClassArray<T>(MapVATR(addr), count);
        }

        public int GetFieldOffsetFromIndex(int typeIndex, int fieldIndexInType, int fieldIndex, bool isValueType, bool isStatic)
        {
            try
            {
                // Estimated / reference-imported layout (always dump.cs display offsets).
                if (IsSynthetic && syntheticFieldOffsets != null &&
                    typeIndex >= 0 && typeIndex < syntheticFieldOffsets.Length &&
                    syntheticFieldOffsets[typeIndex] != null &&
                    fieldIndexInType >= 0 && fieldIndexInType < syntheticFieldOffsets[typeIndex].Length)
                {
                    return syntheticFieldOffsets[typeIndex][fieldIndexInType];
                }

                var offset = -1;
                if (fieldOffsetsArePointers)
                {
                    if (fieldOffsets == null || typeIndex < 0 || typeIndex >= fieldOffsets.Length)
                        return -1;
                    var ptr = fieldOffsets[typeIndex];
                    if (ptr > 0)
                    {
                        Position = MapVATR(ptr) + 4ul * (ulong)fieldIndexInType;
                        offset = ReadInt32();
                    }
                }
                else
                {
                    if (fieldOffsets == null || fieldIndex < 0 || fieldIndex >= fieldOffsets.Length)
                        return -1;
                    offset = (int)fieldOffsets[fieldIndex];
                }
                if (offset > 0)
                {
                    if (isValueType && !isStatic)
                    {
                        if (Is32Bit)
                        {
                            offset -= 8;
                        }
                        else
                        {
                            offset -= 16;
                        }
                    }
                }
                return offset;
            }
            catch
            {
                return -1;
            }
        }

        public Il2CppType GetIl2CppType(ulong pointer)
        {
            if (!typeDic.TryGetValue(pointer, out var type))
            {
                return null;
            }
            return type;
        }

        public ulong GetMethodPointer(string imageName, Il2CppMethodDefinition methodDef)
        {
            if (Version >= 24.2)
            {
                if (codeGenModuleMethodPointers == null ||
                    !codeGenModuleMethodPointers.TryGetValue(imageName, out var ptrs) ||
                    ptrs == null || ptrs.Length == 0)
                    return 0;
                var methodPointerIndex = methodDef.token & 0x00FFFFFFu;
                if (methodPointerIndex == 0 || methodPointerIndex > (uint)ptrs.Length)
                    return 0;
                return ptrs[methodPointerIndex - 1];
            }
            else
            {
                var methodIndex = methodDef.methodIndex;
                if (methodIndex >= 0 && methodPointers != null && methodIndex < methodPointers.Length)
                {
                    return methodPointers[methodIndex];
                }
            }
            return 0;
        }

        public virtual ulong GetRVA(ulong pointer)
        {
            return pointer;
        }

        /// <summary>
        /// Build a usable registration state from global-metadata when CodeRegistration /
        /// MetadataRegistration tables are missing or zeroed (Escher / runtime-only BSS).
        /// Enables full Il2CppDecompiler path with type names; method RVAs filled later if found.
        /// </summary>
        public void InitSyntheticFromMetadata(Metadata metadata)
        {
            IsSynthetic = true;

            var maxType = 0;
            foreach (var td in metadata.typeDefs)
            {
                maxType = Math.Max(maxType, td.byvalTypeIndex);
                maxType = Math.Max(maxType, td.parentIndex);
                maxType = Math.Max(maxType, td.declaringTypeIndex);
                maxType = Math.Max(maxType, td.elementTypeIndex);
            }
            if (metadata.methodDefs != null)
            {
                foreach (var md in metadata.methodDefs)
                    maxType = Math.Max(maxType, md.returnType);
            }
            if (metadata.fieldDefs != null)
            {
                foreach (var fd in metadata.fieldDefs)
                    maxType = Math.Max(maxType, fd.typeIndex);
            }
            if (metadata.parameterDefs != null)
            {
                foreach (var pd in metadata.parameterDefs)
                    maxType = Math.Max(maxType, pd.typeIndex);
            }
            if (metadata.interfaceIndices != null)
            {
                foreach (var idx in metadata.interfaceIndices)
                    maxType = Math.Max(maxType, idx);
            }
            if (maxType < metadata.typeDefs.Length)
                maxType = metadata.typeDefs.Length;

            types = new Il2CppType[maxType + 1];
            for (var i = 0; i <= maxType; i++)
                types[i] = MakeSyntheticType(Il2CppTypeEnum.IL2CPP_TYPE_OBJECT, 0);

            for (var ti = 0; ti < metadata.typeDefs.Length; ti++)
            {
                var td = metadata.typeDefs[ti];
                if (td.byvalTypeIndex < 0 || td.byvalTypeIndex > maxType)
                    continue;
                var kind = td.IsValueType ? Il2CppTypeEnum.IL2CPP_TYPE_VALUETYPE : Il2CppTypeEnum.IL2CPP_TYPE_CLASS;
                types[td.byvalTypeIndex] = MakeSyntheticType(kind, (ulong)(long)ti);
            }

            fieldOffsetsArePointers = true;
            fieldOffsets = new ulong[metadata.typeDefs.Length];

            genericMethodPointers = Array.Empty<ulong>();
            invokerPointers = Array.Empty<ulong>();
            reversePInvokeWrappers = Array.Empty<ulong>();
            unresolvedVirtualCallPointers = Array.Empty<ulong>();
            genericInstPointers = Array.Empty<ulong>();
            genericInsts = Array.Empty<Il2CppGenericInst>();
            methodSpecs = Array.Empty<Il2CppMethodSpec>();
            genericMethodTable = Array.Empty<Il2CppGenericMethodFunctionsDefinitions>();
            methodDefinitionMethodSpecs = new Dictionary<int, List<Il2CppMethodSpec>>();
            methodSpecGenericMethodPointers = new Dictionary<Il2CppMethodSpec, ulong>();

            codeGenModules = new Dictionary<string, Il2CppCodeGenModule>(StringComparer.Ordinal);
            codeGenModuleMethodPointers = new Dictionary<string, ulong[]>(StringComparer.Ordinal);
            rgctxsDictionary = new Dictionary<string, Dictionary<uint, Il2CppRGCTXDefinition[]>>(StringComparer.Ordinal);

            foreach (var imageDef in metadata.imageDefs)
            {
                var imageName = metadata.GetStringFromIndex(imageDef.nameIndex);
                var methodCount = 0;
                var typeEnd = imageDef.typeStart + imageDef.typeCount;
                for (var t = imageDef.typeStart; t < typeEnd && t < metadata.typeDefs.Length; t++)
                    methodCount += metadata.typeDefs[t].method_count;

                // Token indices are 1..N; array length must cover highest token.
                if (methodCount == 0)
                    methodCount = 1;

                codeGenModules[imageName] = new Il2CppCodeGenModule
                {
                    methodPointerCount = methodCount
                };
                codeGenModuleMethodPointers[imageName] = new ulong[methodCount];
                rgctxsDictionary[imageName] = new Dictionary<uint, Il2CppRGCTXDefinition[]>();
            }

            try
            {
                SyntheticTypeEnricher.Enrich(this, metadata);
            }
            catch { }

            try
            {
                syntheticFieldOffsets = FieldLayoutBuilder.Build(metadata, this);
            }
            catch
            {
                syntheticFieldOffsets = null;
            }
        }

        private Il2CppType MakeSyntheticType(Il2CppTypeEnum typeEnum, ulong data)
        {
            var t = new Il2CppType
            {
                datapoint = data,
                bits = ((uint)typeEnum) << 16
            };
            t.Init(Version);
            return t;
        }

        /// <summary>Expose type clone for enricher.</summary>
        public Il2CppType CloneIl2CppType(Il2CppType src)
        {
            if (src == null)
                return MakeSyntheticType(Il2CppTypeEnum.IL2CPP_TYPE_OBJECT, 0);
            var t = new Il2CppType
            {
                datapoint = src.datapoint,
                bits = src.bits
            };
            t.Init(Version);
            return t;
        }

        /// <summary>Attach recovered method pointer table for an image (token order).</summary>
        public void SetModuleMethodPointers(string imageName, ulong[] pointers)
        {
            if (string.IsNullOrEmpty(imageName) || pointers == null)
                return;
            codeGenModuleMethodPointers ??= new Dictionary<string, ulong[]>(StringComparer.Ordinal);
            codeGenModuleMethodPointers[imageName] = pointers;
            if (codeGenModules != null && codeGenModules.TryGetValue(imageName, out var mod))
            {
                mod.methodPointerCount = pointers.Length;
                codeGenModules[imageName] = mod;
            }
        }

        public (int fields, int methods) ApplyReferenceDump(Metadata metadata, ReferenceDumpData data)
        {
            ReferenceDump = data;
            var fields = 0;
            var methods = 0;
            if (data == null || metadata == null)
                return (0, 0);

            if (syntheticFieldOffsets == null)
                syntheticFieldOffsets = new int[metadata.typeDefs.Length][];

            var typeMap = ReferenceDumpImporter.BuildTypeMap(metadata);
            fields = ReferenceDumpImporter.ApplyFieldOffsets(data, metadata, syntheticFieldOffsets, this, typeMap);
            methods = ReferenceDumpImporter.ApplyMethodRvas(data, metadata, this, typeMap);
            return (fields, methods);
        }
    }
}
