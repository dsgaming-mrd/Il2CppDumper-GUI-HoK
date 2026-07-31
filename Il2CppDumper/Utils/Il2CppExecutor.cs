using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;

namespace Il2CppDumper
{
    public class Il2CppExecutor
    {
        public Metadata metadata;
        public Il2Cpp il2Cpp;
        private static readonly Dictionary<int, string> TypeString = new()
        {
            {1,"void"},
            {2,"bool"},
            {3,"char"},
            {4,"sbyte"},
            {5,"byte"},
            {6,"short"},
            {7,"ushort"},
            {8,"int"},
            {9,"uint"},
            {10,"long"},
            {11,"ulong"},
            {12,"float"},
            {13,"double"},
            {14,"string"},
            {22,"TypedReference"},
            {24,"IntPtr"},
            {25,"UIntPtr"},
            {28,"object"},
        };
        public ulong[] customAttributeGenerators;

        public Il2CppExecutor(Metadata metadata, Il2Cpp il2Cpp)
        {
            this.metadata = metadata;
            this.il2Cpp = il2Cpp;

            if (il2Cpp.Version >= 27 && il2Cpp.Version < 29)
            {
                customAttributeGenerators = new ulong[metadata.imageDefs.Sum(x => x.customAttributeCount)];
                foreach (var imageDef in metadata.imageDefs)
                {
                    var imageDefName = metadata.GetStringFromIndex(imageDef.nameIndex);
                    var codeGenModule = il2Cpp.codeGenModules[imageDefName];
                    if (imageDef.customAttributeCount > 0)
                    {
                        var pointers = il2Cpp.ReadClassArray<ulong>(il2Cpp.MapVATR(codeGenModule.customAttributeCacheGenerator), imageDef.customAttributeCount);
                        pointers.CopyTo(customAttributeGenerators, imageDef.customAttributeStart);
                    }
                }
            }
            else if (il2Cpp.Version < 27)
            {
                customAttributeGenerators = il2Cpp.customAttributeGenerators;
            }
        }

        public string GetTypeName(Il2CppType il2CppType, bool addNamespace, bool is_nested)
        {
            switch (il2CppType.type)
            {
                case Il2CppTypeEnum.IL2CPP_TYPE_ARRAY:
                    {
                        var arrayType = il2Cpp.MapVATR<Il2CppArrayType>(il2CppType.data.array);
                        var elementType = il2Cpp.GetIl2CppType(arrayType.etype);
                        return $"{GetTypeName(elementType, addNamespace, false)}[{new string(',', arrayType.rank - 1)}]";
                    }
                case Il2CppTypeEnum.IL2CPP_TYPE_SZARRAY:
                    {
                        var elementType = il2Cpp.GetIl2CppType(il2CppType.data.type);
                        return $"{GetTypeName(elementType, addNamespace, false)}[]";
                    }
                case Il2CppTypeEnum.IL2CPP_TYPE_PTR:
                    {
                        var oriType = il2Cpp.GetIl2CppType(il2CppType.data.type);
                        return $"{GetTypeName(oriType, addNamespace, false)}*";
                    }
                case Il2CppTypeEnum.IL2CPP_TYPE_VAR:
                case Il2CppTypeEnum.IL2CPP_TYPE_MVAR:
                    {
                        var param = GetGenericParameteFromIl2CppType(il2CppType);
                        return metadata.GetStringFromIndex(param.nameIndex);
                    }
                case Il2CppTypeEnum.IL2CPP_TYPE_CLASS:
                case Il2CppTypeEnum.IL2CPP_TYPE_VALUETYPE:
                case Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST:
                    {
                        string str = string.Empty;
                        Il2CppTypeDefinition typeDef;
                        Il2CppGenericClass genericClass = null;
                        if (il2CppType.type == Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST)
                        {
                            genericClass = il2Cpp.MapVATR<Il2CppGenericClass>(il2CppType.data.generic_class);
                            typeDef = GetGenericClassTypeDefinition(genericClass);
                        }
                        else
                        {
                            typeDef = GetTypeDefinitionFromIl2CppType(il2CppType);
                        }
                        if (typeDef.declaringTypeIndex == -1 && genericClass == null)
                        {
                            var @namespace = metadata.GetStringFromIndex(typeDef.namespaceIndex);
                            if (@namespace == "System")
                            {
                                var sysTypeName = metadata.GetStringFromIndex(typeDef.nameIndex);
                                var mapped = sysTypeName switch
                                {
                                    "Void" => "void",
                                    "Boolean" => "bool",
                                    "Byte" => "byte",
                                    "SByte" => "sbyte",
                                    "Int16" => "short",
                                    "UInt16" => "ushort",
                                    "Int32" => "int",
                                    "UInt32" => "uint",
                                    "Int64" => "long",
                                    "UInt64" => "ulong",
                                    "Single" => "float",
                                    "Double" => "double",
                                    "Char" => "char",
                                    "String" => "string",
                                    "Object" => "object",
                                    _ => null
                                };
                                if (mapped != null)
                                    return mapped;
                            }
                        }
                        if (typeDef.declaringTypeIndex != -1)
                        {
                            str += GetTypeName(il2Cpp.types[typeDef.declaringTypeIndex], addNamespace, true);
                            str += '.';
                        }
                        else if (addNamespace)
                        {
                            var @namespace = metadata.GetStringFromIndex(typeDef.namespaceIndex);
                            if (@namespace != "")
                            {
                                str += @namespace + ".";
                            }
                        }

                        var typeName = metadata.GetStringFromIndex(typeDef.nameIndex);
                        var index = typeName.IndexOf("`");
                        if (index != -1)
                        {
                            str += typeName[..index];
                        }
                        else
                        {
                            str += typeName;
                        }

                        if (is_nested)
                            return str;

                        if (genericClass != null)
                        {
                            var genericInst = il2Cpp.MapVATR<Il2CppGenericInst>(genericClass.context.class_inst);
                            str += GetGenericInstParams(genericInst);
                        }
                        else if (typeDef.genericContainerIndex >= 0)
                        {
                            var genericContainer = metadata.genericContainers[typeDef.genericContainerIndex];
                            str += GetGenericContainerParams(genericContainer);
                        }

                        return str;
                    }
                default:
                    return TypeString[(int)il2CppType.type];
            }
        }

        public string GetTypeDefName(Il2CppTypeDefinition typeDef, bool addNamespace, bool genericParameter)
        {
            var prefix = string.Empty;
            if (typeDef.declaringTypeIndex != -1)
            {
                prefix = GetTypeName(il2Cpp.types[typeDef.declaringTypeIndex], addNamespace, true) + ".";
            }
            else if (addNamespace)
            {
                var @namespace = metadata.GetStringFromIndex(typeDef.namespaceIndex);
                if (@namespace != "")
                {
                    prefix = @namespace + ".";
                }
            }
            var typeName = metadata.GetStringFromIndex(typeDef.nameIndex);
            if (typeDef.genericContainerIndex >= 0)
            {
                var index = typeName.IndexOf("`");
                if (index != -1)
                {
                    typeName = typeName[..index];
                }
                if (genericParameter)
                {
                    var genericContainer = metadata.genericContainers[typeDef.genericContainerIndex];
                    typeName += GetGenericContainerParams(genericContainer);
                }
            }
            return prefix + typeName;
        }

        public string GetGenericInstParams(Il2CppGenericInst genericInst)
        {
            var genericParameterNames = new List<string>();
            var pointers = il2Cpp.MapVATR<ulong>(genericInst.type_argv, genericInst.type_argc);
            for (int i = 0; i < genericInst.type_argc; i++)
            {
                var il2CppType = il2Cpp.GetIl2CppType(pointers[i]);
                genericParameterNames.Add(GetTypeName(il2CppType, false, false));
            }
            return $"<{string.Join(", ", genericParameterNames)}>";
        }

        public string GetGenericContainerParams(Il2CppGenericContainer genericContainer)
        {
            var genericParameterNames = new List<string>();
            for (int i = 0; i < genericContainer.type_argc; i++)
            {
                var genericParameterIndex = genericContainer.genericParameterStart + i;
                var genericParameter = metadata.genericParameters[genericParameterIndex];
                genericParameterNames.Add(metadata.GetStringFromIndex(genericParameter.nameIndex));
            }
            return $"<{string.Join(", ", genericParameterNames)}>";
        }

        public (string, string) GetMethodSpecName(Il2CppMethodSpec methodSpec, bool addNamespace = false)
        {
            var methodDef = metadata.methodDefs[methodSpec.methodDefinitionIndex];
            var typeDef = metadata.typeDefs[methodDef.declaringType];
            var typeName = GetTypeDefName(typeDef, addNamespace, false);
            if (methodSpec.classIndexIndex != -1)
            {
                var classInst = il2Cpp.genericInsts[methodSpec.classIndexIndex];
                typeName += GetGenericInstParams(classInst);
            }
            var methodName = metadata.GetStringFromIndex(methodDef.nameIndex);
            if (methodSpec.methodIndexIndex != -1)
            {
                var methodInst = il2Cpp.genericInsts[methodSpec.methodIndexIndex];
                methodName += GetGenericInstParams(methodInst);
            }
            return (typeName, methodName);
        }

        public Il2CppGenericContext GetMethodSpecGenericContext(Il2CppMethodSpec methodSpec)
        {
            var classInstPointer = 0ul;
            var methodInstPointer = 0ul;
            if (methodSpec.classIndexIndex != -1)
            {
                classInstPointer = il2Cpp.genericInstPointers[methodSpec.classIndexIndex];
            }
            if (methodSpec.methodIndexIndex != -1)
            {
                methodInstPointer = il2Cpp.genericInstPointers[methodSpec.methodIndexIndex];
            }
            return new Il2CppGenericContext { class_inst = classInstPointer, method_inst = methodInstPointer };
        }

        public Il2CppRGCTXDefinition[] GetRGCTXDefinition(string imageName, Il2CppTypeDefinition typeDef)
        {
            Il2CppRGCTXDefinition[] collection = null;
            if (il2Cpp.Version >= 24.2)
            {
                il2Cpp.rgctxsDictionary[imageName].TryGetValue(typeDef.token, out collection);
            }
            else
            {
                if (typeDef.rgctxCount > 0)
                {
                    collection = new Il2CppRGCTXDefinition[typeDef.rgctxCount];
                    Array.Copy(metadata.rgctxEntries, typeDef.rgctxStartIndex, collection, 0, typeDef.rgctxCount);
                }
            }
            return collection;
        }

        public Il2CppRGCTXDefinition[] GetRGCTXDefinition(string imageName, Il2CppMethodDefinition methodDef)
        {
            Il2CppRGCTXDefinition[] collection = null;
            if (il2Cpp.Version >= 24.2)
            {
                il2Cpp.rgctxsDictionary[imageName].TryGetValue(methodDef.token, out collection);
            }
            else
            {
                if (methodDef.rgctxCount > 0)
                {
                    collection = new Il2CppRGCTXDefinition[methodDef.rgctxCount];
                    Array.Copy(metadata.rgctxEntries, methodDef.rgctxStartIndex, collection, 0, methodDef.rgctxCount);
                }
            }
            return collection;
        }

        public Il2CppTypeDefinition GetGenericClassTypeDefinition(Il2CppGenericClass genericClass)
        {
            if (il2Cpp.Version >= 27)
            {
                var il2CppType = il2Cpp.GetIl2CppType(genericClass.type);
                if (il2CppType == null)
                {
                    return null;
                }
                return GetTypeDefinitionFromIl2CppType(il2CppType);
            }
            if (genericClass.typeDefinitionIndex == 4294967295 || genericClass.typeDefinitionIndex == -1)
            {
                return null;
            }
            return metadata.typeDefs[genericClass.typeDefinitionIndex];
        }

        public Il2CppTypeDefinition GetTypeDefinitionFromIl2CppType(Il2CppType il2CppType)
        {
            if (il2Cpp.Version >= 27 && il2Cpp.IsDumped)
            {
                var offset = il2CppType.data.typeHandle - metadata.ImageBase - metadata.header.typeDefinitionsOffset;
                var index = offset / (ulong)metadata.SizeOf(typeof(Il2CppTypeDefinition));
                return metadata.typeDefs[index];
            }
            else
            {
                return metadata.typeDefs[il2CppType.data.klassIndex];
            }
        }

        public Il2CppGenericParameter GetGenericParameteFromIl2CppType(Il2CppType il2CppType)
        {
            if (il2Cpp.Version >= 27 && il2Cpp.IsDumped)
            {
                var offset = il2CppType.data.genericParameterHandle - metadata.ImageBase - metadata.header.genericParametersOffset;
                var index = offset / (ulong)metadata.SizeOf(typeof(Il2CppGenericParameter));
                return metadata.genericParameters[index];
            }
            else
            {
                return metadata.genericParameters[il2CppType.data.genericParameterIndex];
            }
        }

        public SectionHelper GetSectionHelper()
        {
            return il2Cpp.GetSectionHelper(metadata.methodDefs.Count(x => x.methodIndex >= 0), metadata.typeDefs.Length, metadata.imageDefs.Length);
        }

        public bool TryGetDefaultValue(int typeIndex, int dataIndex, out object value, Il2CppTypeEnum typeEnumOverride = Il2CppTypeEnum.IL2CPP_TYPE_END)
        {
            var pointer = metadata.GetDefaultValueFromIndex(dataIndex);
            var typeEnum = Il2CppTypeEnum.IL2CPP_TYPE_OBJECT;
            if (typeEnumOverride != Il2CppTypeEnum.IL2CPP_TYPE_END)
            {
                typeEnum = typeEnumOverride;
            }
            else if (typeIndex >= 0 && il2Cpp.types != null && typeIndex < il2Cpp.types.Length &&
                     il2Cpp.types[typeIndex] != null)
            {
                typeEnum = il2Cpp.types[typeIndex].type;
            }

            if (typeEnum is not (Il2CppTypeEnum.IL2CPP_TYPE_OBJECT or Il2CppTypeEnum.IL2CPP_TYPE_END or (Il2CppTypeEnum)0))
            {
                metadata.Position = pointer;
                if (GetConstantValueFromBlob(typeEnum, metadata.Reader, out var blobValue))
                {
                    value = blobValue.Value;
                    return true;
                }
            }

            if (typeEnumOverride == Il2CppTypeEnum.IL2CPP_TYPE_END && (il2Cpp.IsSynthetic || typeEnum is Il2CppTypeEnum.IL2CPP_TYPE_OBJECT or (Il2CppTypeEnum)0))
            {
                if (TryProbeDefaultValueBlob(pointer, out value))
                    return true;
            }

            value = pointer;
            return false;
        }

        private bool TryProbeDefaultValueBlob(uint pointer, out object value)
        {
            value = null;
            if (pointer == 0 || pointer >= metadata.Length)
                return false;

            try
            {
                metadata.Position = pointer;
                if (TryReadV29StringConst(metadata.Reader, out var s))
                {
                    if (s == null || IsPlausibleConstString(s))
                    {
                        value = s;
                        return true;
                    }
                }
            }
            catch { }

            try
            {
                metadata.Position = pointer;
                var b = metadata.ReadByte();
                if (b is 0 or 1)
                {
                    value = b != 0;
                    return true;
                }
            }
            catch { }

            try
            {
                metadata.Position = pointer;
                if (GetConstantValueFromBlob(Il2CppTypeEnum.IL2CPP_TYPE_I4, metadata.Reader, out var ib) &&
                    ib?.Value is int i4 && i4 > -50_000_000 && i4 < 50_000_000)
                {
                    value = i4;
                    return true;
                }
            }
            catch { }

            try
            {
                metadata.Position = pointer;
                if (GetConstantValueFromBlob(Il2CppTypeEnum.IL2CPP_TYPE_R4, metadata.Reader, out var fb) &&
                    fb?.Value is float f && !float.IsNaN(f) && !float.IsInfinity(f) && Math.Abs(f) < 1e9f)
                {
                    value = f;
                    return true;
                }
            }
            catch { }

            return false;
        }

        private bool TryReadV29StringConst(BinaryReader reader, out string s)
        {
            s = null;
            if (il2Cpp.Version < 29)
            {
                var len = reader.ReadInt32();
                if (len < 0 || len > 4096)
                    return false;
                s = reader.ReadString(len);
                return true;
            }

            var length = reader.ReadCompressedInt32();
            if (length == -1)
            {
                s = null;
                return true;
            }
            if (length < 0 || length > 4096)
                return false;
            if (reader.BaseStream.Position + length > reader.BaseStream.Length)
                return false;
            s = Encoding.UTF8.GetString(reader.ReadBytes(length));
            return true;
        }

        private static bool IsPlausibleConstString(string s)
        {
            if (s == null) return true;
            if (s.Length > 4096) return false;
            if (s.Length == 0) return true;
            if (s.IndexOf('\0') >= 0) return false;

            var letters = 0;
            var pathy = 0;
            var weird = 0;
            foreach (var ch in s)
            {
                if (char.IsLetterOrDigit(ch) || ch >= 0x4E00)
                    letters++;
                if (ch is '/' or '\\' or '.' or '_' or '-' or ' ')
                    pathy++;
                if (char.IsControl(ch) && ch is not ('\t' or '\n' or '\r'))
                    weird++;
                if (s.Length > 8 && ch is '`' or '^' or '~' or '|' or '?')
                    weird++;
            }
            if (weird > s.Length * 0.1) return false;
            if (letters + pathy < s.Length * 0.5) return false;

            if (s.Contains('/') || s.Contains('\\') ||
                s.Contains(".prefab", StringComparison.OrdinalIgnoreCase) ||
                s.Contains("Prefab", StringComparison.Ordinal) ||
                s.Contains("UGUI", StringComparison.Ordinal) ||
                s.Contains("Effect", StringComparison.Ordinal) ||
                s.Contains("Assets", StringComparison.Ordinal))
                return true;

            if (s.Length <= 128 && letters >= s.Length * 0.6)
                return true;

            if (s.Any(c => c > 0x3000) && weird == 0)
                return true;

            return false;
        }

        public bool GetConstantValueFromBlob(Il2CppTypeEnum type, BinaryReader reader, out BlobValue value)
        {
            value = new BlobValue
            {
                il2CppTypeEnum = type
            };
            switch (type)
            {
                case Il2CppTypeEnum.IL2CPP_TYPE_BOOLEAN:
                    value.Value = reader.ReadBoolean();
                    return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_U1:
                    value.Value = reader.ReadByte();
                    return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_I1:
                    value.Value = reader.ReadSByte();
                    return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_CHAR:
                    value.Value = BitConverter.ToChar(reader.ReadBytes(2), 0);
                    return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_U2:
                    value.Value = reader.ReadUInt16();
                    return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_I2:
                    value.Value = reader.ReadInt16();
                    return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_U4:
                    if (il2Cpp.Version >= 29)
                    {
                        value.Value = reader.ReadCompressedUInt32();
                    }
                    else
                    {
                        value.Value = reader.ReadUInt32();
                    }
                    return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_I4:
                    if (il2Cpp.Version >= 29)
                    {
                        value.Value = reader.ReadCompressedInt32();
                    }
                    else
                    {
                        value.Value = reader.ReadInt32();
                    }
                    return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_U8:
                    value.Value = reader.ReadUInt64();
                    return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_I8:
                    value.Value = reader.ReadInt64();
                    return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_R4:
                    value.Value = reader.ReadSingle();
                    return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_R8:
                    value.Value = reader.ReadDouble();
                    return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_STRING:
                    int length;
                    if (il2Cpp.Version >= 29)
                    {
                        length = reader.ReadCompressedInt32();
                        if (length == -1)
                        {
                            value.Value = null;
                        }
                        else
                        {
                            value.Value = Encoding.UTF8.GetString(reader.ReadBytes(length));
                        }
                    }
                    else
                    {
                        length = reader.ReadInt32();
                        value.Value = reader.ReadString(length);
                    }
                    return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_SZARRAY:
                    var arrayLen = reader.ReadCompressedInt32();
                    if (arrayLen == -1)
                    {
                        value.Value = null;
                    }
                    else
                    {
                        var array = new BlobValue[arrayLen];
                        var arrayElementType = ReadEncodedTypeEnum(reader, out var enumType);
                        var arrayElementsAreDifferent = reader.ReadByte();
                        for (int i = 0; i < arrayLen; i++)
                        {
                            var elementType = arrayElementType;
                            if (arrayElementsAreDifferent == 1)
                            {
                                elementType = ReadEncodedTypeEnum(reader, out enumType);
                            }
                            GetConstantValueFromBlob(elementType, reader, out var data);
                            if (data == null)
                            {
                                data = new BlobValue { il2CppTypeEnum = elementType };
                            }
                            data.il2CppTypeEnum = elementType;
                            data.EnumType = enumType;
                            array[i] = data;
                        }
                        value.Value = array;
                    }
                    return true;
                case Il2CppTypeEnum.IL2CPP_TYPE_IL2CPP_TYPE_INDEX:
                    var typeIndex = reader.ReadCompressedInt32();
                    if (typeIndex == -1)
                    {
                        value.Value = null;
                    }
                    else
                    {
                        value.Value = il2Cpp.types[typeIndex];
                    }
                    return true;
                default:
                    value = null;
                    return false;
            }
        }

        public Il2CppTypeEnum ReadEncodedTypeEnum(BinaryReader reader, out Il2CppType enumType)
        {
            enumType = null;
            var type = (Il2CppTypeEnum)reader.ReadByte();
            if (type == Il2CppTypeEnum.IL2CPP_TYPE_ENUM)
            {
                var enumTypeIndex = reader.ReadCompressedInt32();
                enumType = il2Cpp.types[enumTypeIndex];
                var typeDef = GetTypeDefinitionFromIl2CppType(enumType);
                type = il2Cpp.types[typeDef.elementTypeIndex].type;
            }
            return type;
        }
    }
}
