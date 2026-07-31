using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using static Il2CppDumper.Il2CppConstants;

namespace Il2CppDumper
{
    public class Il2CppDecompiler
    {
        private readonly Il2CppExecutor executor;
        private readonly Metadata metadata;
        private readonly Il2Cpp il2Cpp;
        private readonly Dictionary<Il2CppMethodDefinition, string> methodModifiers;

        public Il2CppDecompiler(Il2CppExecutor il2CppExecutor)
        {
            executor = il2CppExecutor;
            metadata = il2CppExecutor.metadata;
            il2Cpp = il2CppExecutor.il2Cpp;
            methodModifiers = new();
        }

        public void Decompile(Config config, string outputDir)
        {
            var writer = new StreamWriter(new FileStream(outputDir + "dump.cs", FileMode.Create), new UTF8Encoding(false));
            //dump image
            for (var imageIndex = 0; imageIndex < metadata.imageDefs.Length; imageIndex++)
            {
                var imageDef = metadata.imageDefs[imageIndex];
                writer.Write($"// Image {imageIndex}: {metadata.GetStringFromIndex(imageDef.nameIndex)} - {imageDef.typeStart}\n");
            }
            //dump type
            foreach (var imageDef in metadata.imageDefs)
            {
                var imageName = metadata.GetStringFromIndex(imageDef.nameIndex);
                var typeEnd = imageDef.typeStart + imageDef.typeCount;
                for (int typeDefIndex = imageDef.typeStart; typeDefIndex < typeEnd; typeDefIndex++)
                {
                    try
                    {
                        var typeDef = metadata.typeDefs[typeDefIndex];
                        var extends = new List<string>();
                        if (typeDef.parentIndex >= 0)
                        {
                            var parent = SafeGetType(typeDef.parentIndex);
                            var parentFullName = executor.GetTypeName(parent, true, false);
                            var parentName = executor.GetTypeName(parent, false, false);
                            if (!typeDef.IsValueType && !typeDef.IsEnum && parentName != "object" && parentFullName != "System.Object")
                            {
                                extends.Add(parentName);
                            }
                        }
                        if (typeDef.interfaces_count > 0 && metadata.interfaceIndices != null)
                        {
                            for (int i = 0; i < typeDef.interfaces_count; i++)
                            {
                                var ii = typeDef.interfacesStart + i;
                                if (ii >= 0 && ii < metadata.interfaceIndices.Length)
                                {
                                    var @interface = SafeGetType(metadata.interfaceIndices[ii]);
                                    extends.Add(executor.GetTypeName(@interface, false, false));
                                }
                            }
                        }
                        writer.Write($"\n// Namespace: {metadata.GetStringFromIndex(typeDef.namespaceIndex)}\n");
                        if (config.DumpAttribute)
                        {
                            writer.Write(GetCustomAttribute(imageDef, typeDef.customAttributeIndex, typeDef.token));
                        }
                        if (config.DumpAttribute && (typeDef.flags & TYPE_ATTRIBUTE_SERIALIZABLE) != 0)
                            writer.Write("[Serializable]\n");
                        var visibility = typeDef.flags & TYPE_ATTRIBUTE_VISIBILITY_MASK;
                        switch (visibility)
                        {
                            case TYPE_ATTRIBUTE_PUBLIC:
                            case TYPE_ATTRIBUTE_NESTED_PUBLIC:
                                writer.Write("public ");
                                break;
                            case TYPE_ATTRIBUTE_NOT_PUBLIC:
                            case TYPE_ATTRIBUTE_NESTED_FAM_AND_ASSEM:
                            case TYPE_ATTRIBUTE_NESTED_ASSEMBLY:
                                writer.Write("internal ");
                                break;
                            case TYPE_ATTRIBUTE_NESTED_PRIVATE:
                                writer.Write("private ");
                                break;
                            case TYPE_ATTRIBUTE_NESTED_FAMILY:
                                writer.Write("protected ");
                                break;
                            case TYPE_ATTRIBUTE_NESTED_FAM_OR_ASSEM:
                                writer.Write("protected internal ");
                                break;
                        }
                        if ((typeDef.flags & TYPE_ATTRIBUTE_ABSTRACT) != 0 && (typeDef.flags & TYPE_ATTRIBUTE_SEALED) != 0)
                            writer.Write("static ");
                        else if ((typeDef.flags & TYPE_ATTRIBUTE_INTERFACE) == 0 && (typeDef.flags & TYPE_ATTRIBUTE_ABSTRACT) != 0)
                            writer.Write("abstract ");
                        else if (!typeDef.IsValueType && !typeDef.IsEnum && (typeDef.flags & TYPE_ATTRIBUTE_SEALED) != 0)
                            writer.Write("sealed ");
                        if ((typeDef.flags & TYPE_ATTRIBUTE_INTERFACE) != 0)
                            writer.Write("interface ");
                        else if (typeDef.IsEnum)
                            writer.Write("enum ");
                        else if (typeDef.IsValueType)
                            writer.Write("struct ");
                        else
                            writer.Write("class ");
                        var typeName = executor.GetTypeDefName(typeDef, false, true);
                        writer.Write($"{typeName}");
                        if (extends.Count > 0)
                            writer.Write($" : {string.Join(", ", extends)}");
                        if (config.DumpTypeDefIndex)
                            writer.Write($" // TypeDefIndex: {typeDefIndex}\n{{");
                        else
                            writer.Write("\n{");
                        //dump field
                        if (config.DumpField && typeDef.field_count > 0 && metadata.fieldDefs != null)
                        {
                            writer.Write("\n\t// Fields\n");
                            var fieldEnd = typeDef.fieldStart + typeDef.field_count;
                            for (var i = typeDef.fieldStart; i < fieldEnd; ++i)
                            {
                                if (i < 0 || i >= metadata.fieldDefs.Length)
                                    continue;
                                var fieldDef = metadata.fieldDefs[i];
                                var fieldType = SafeGetType(fieldDef.typeIndex);
                                var isStatic = false;
                                var isConst = false;
                                var fieldName = metadata.GetStringFromIndex(fieldDef.nameIndex);
                                var isEnumLiteral = il2Cpp.IsSynthetic && typeDef.IsEnum && fieldName != "value__";
                                var isEnumValueField = il2Cpp.IsSynthetic && typeDef.IsEnum && fieldName == "value__";

                                var isFieldDefault = metadata.GetFieldDefaultValueFromIndex(i, out var fieldDefaultValue) && fieldDefaultValue.dataIndex != -1;
                                if (isFieldDefault && !isEnumValueField)
                                {
                                    isConst = true;
                                }

                                if (config.DumpAttribute)
                                {
                                    writer.Write(GetCustomAttribute(imageDef, fieldDef.customAttributeIndex, fieldDef.token, "\t"));
                                }
                                writer.Write("\t");
                                var access = fieldType.attrs & FIELD_ATTRIBUTE_FIELD_ACCESS_MASK;
                                if (typeDef.IsEnum)
                                {
                                    access = FIELD_ATTRIBUTE_PUBLIC;
                                }
                                else if (access == 0)
                                {
                                    access = FIELD_ATTRIBUTE_PRIVATE;
                                }
                                switch (access)
                                {
                                    case FIELD_ATTRIBUTE_PRIVATE:
                                        writer.Write("private ");
                                        break;
                                    case FIELD_ATTRIBUTE_PUBLIC:
                                        writer.Write("public ");
                                        break;
                                    case FIELD_ATTRIBUTE_FAMILY:
                                        writer.Write("protected ");
                                        break;
                                    case FIELD_ATTRIBUTE_ASSEMBLY:
                                    case FIELD_ATTRIBUTE_FAM_AND_ASSEM:
                                        writer.Write("internal ");
                                        break;
                                    case FIELD_ATTRIBUTE_FAM_OR_ASSEM:
                                        writer.Write("protected internal ");
                                        break;
                                }
                                if ((fieldType.attrs & FIELD_ATTRIBUTE_LITERAL) != 0 || isEnumLiteral)
                                {
                                    isConst = true;
                                    writer.Write("const ");
                                }
                                else
                                {
                                    var lookupIndex = typeDefIndex;
                                    if (il2Cpp.ReferenceDump != null &&
                                        il2Cpp.ReferenceDump.NewToOldTypeIndices.TryGetValue(typeDefIndex, out var oldIdx))
                                    {
                                        lookupIndex = oldIdx;
                                    }

                                    if ((fieldType.attrs & FIELD_ATTRIBUTE_STATIC) != 0 ||
                                        (il2Cpp.ReferenceDump != null &&
                                         il2Cpp.ReferenceDump.StaticFields.TryGetValue(lookupIndex, out var sf) &&
                                         sf.Contains(fieldName)))
                                    {
                                        isStatic = true;
                                        writer.Write("static ");
                                    }
                                    else if (il2Cpp.IsSynthetic &&
                                             (fieldName.StartsWith("s_", StringComparison.Ordinal) ||
                                              fieldName.StartsWith("S_", StringComparison.Ordinal) ||
                                              fieldName.StartsWith("g_", StringComparison.Ordinal) ||
                                              fieldName.StartsWith("G_", StringComparison.Ordinal)))
                                    {
                                        isStatic = true;
                                        writer.Write("static ");
                                    }
                                    if ((fieldType.attrs & FIELD_ATTRIBUTE_INIT_ONLY) != 0)
                                    {
                                        writer.Write("readonly ");
                                    }
                                }
                                string fieldTypeName;
                                if (isEnumLiteral)
                                {
                                    fieldTypeName = executor.GetTypeDefName(typeDef, false, true);
                                }
                                else if (isEnumValueField)
                                {
                                    fieldTypeName = GetEnumUnderlyingTypeName(typeDef);
                                }
                                else
                                {
                                    fieldTypeName = ResolveFieldTypeName(typeDefIndex, typeDef, fieldDef, fieldType);
                                }
                                writer.Write($"{fieldTypeName} {fieldName}");
                                if (isFieldDefault)
                                {
                                    Il2CppTypeEnum typeEnumOverride = Il2CppTypeEnum.IL2CPP_TYPE_END;
                                    if (isEnumLiteral)
                                    {
                                        typeEnumOverride = GetEnumUnderlyingTypeEnum(fieldTypeName);
                                    }
                                    if (executor.TryGetDefaultValue(fieldDefaultValue.typeIndex, fieldDefaultValue.dataIndex, out var value, typeEnumOverride))
                                    {
                                        writer.Write($" = ");
                                        if (value is string str)
                                        {
                                            writer.Write($"\"{str.ToEscapedString()}\"");
                                        }
                                        else if (value is char c)
                                        {
                                            var v = (int)c;
                                            writer.Write($"'\\x{v:x}'");
                                        }
                                        else if (value is bool b)
                                        {
                                            writer.Write(b ? "true" : "false");
                                        }
                                        else if (value is float f)
                                        {
                                            writer.Write(f.ToString(System.Globalization.CultureInfo.InvariantCulture) + "f");
                                        }
                                        else if (value is double d)
                                        {
                                            writer.Write(d.ToString(System.Globalization.CultureInfo.InvariantCulture));
                                        }
                                        else if (value != null)
                                        {
                                            writer.Write(Convert.ToString(value, System.Globalization.CultureInfo.InvariantCulture));
                                        }
                                        else
                                        {
                                            writer.Write("null");
                                        }
                                    }
                                    else
                                     {
                                         writer.Write($" /*Metadata offset 0x{value:X}*/");
                                     }
                                }
                                if (config.DumpFieldOffset && !isConst)
                                    writer.Write("; // 0x{0:X}\n", il2Cpp.GetFieldOffsetFromIndex(typeDefIndex, i - typeDef.fieldStart, i, typeDef.IsValueType, isStatic));
                                else
                                    writer.Write(";\n");
                            }
                        }
                        //dump property
                        if (config.DumpProperty && typeDef.property_count > 0 && metadata.propertyDefs != null)
                        {
                            writer.Write("\n\t// Properties\n");
                            var propertyEnd = typeDef.propertyStart + typeDef.property_count;
                            for (var i = typeDef.propertyStart; i < propertyEnd; ++i)
                            {
                                if (i < 0 || i >= metadata.propertyDefs.Length)
                                    continue;
                                var propertyDef = metadata.propertyDefs[i];
                                if (config.DumpAttribute)
                                {
                                    writer.Write(GetCustomAttribute(imageDef, propertyDef.customAttributeIndex, propertyDef.token, "\t"));
                                }
                                writer.Write("\t");
                                if (propertyDef.get >= 0 && metadata.methodDefs != null)
                                {
                                    var methodIndex = typeDef.methodStart + propertyDef.get;
                                    if (methodIndex >= 0 && methodIndex < metadata.methodDefs.Length)
                                    {
                                        var methodDef = metadata.methodDefs[methodIndex];
                                        writer.Write(GetModifiers(methodDef));
                                        var propertyType = SafeGetType(methodDef.returnType);
                                        writer.Write($"{executor.GetTypeName(propertyType, false, false)} {metadata.GetStringFromIndex(propertyDef.nameIndex)} {{ ");
                                    }
                                }
                                else if (propertyDef.set >= 0 && metadata.methodDefs != null)
                                {
                                    var methodIndex = typeDef.methodStart + propertyDef.set;
                                    if (methodIndex >= 0 && methodIndex < metadata.methodDefs.Length)
                                    {
                                        var methodDef = metadata.methodDefs[methodIndex];
                                        writer.Write(GetModifiers(methodDef));
                                        if (methodDef.parameterCount > 0 && metadata.parameterDefs != null &&
                                            methodDef.parameterStart >= 0 && methodDef.parameterStart < metadata.parameterDefs.Length)
                                        {
                                            var parameterDef = metadata.parameterDefs[methodDef.parameterStart];
                                            var propertyType = SafeGetType(parameterDef.typeIndex);
                                            writer.Write($"{executor.GetTypeName(propertyType, false, false)} {metadata.GetStringFromIndex(propertyDef.nameIndex)} {{ ");
                                        }
                                    }
                                }
                                if (propertyDef.get >= 0)
                                    writer.Write("get; ");
                                if (propertyDef.set >= 0)
                                    writer.Write("set; ");
                                writer.Write("}");
                                writer.Write("\n");
                            }
                        }
                        //dump method
                        if (config.DumpMethod && typeDef.method_count > 0 && metadata.methodDefs != null)
                        {
                            writer.Write("\n\t// Methods\n");
                            var methodEnd = typeDef.methodStart + typeDef.method_count;
                            for (var i = typeDef.methodStart; i < methodEnd; ++i)
                            {
                                if (i < 0 || i >= metadata.methodDefs.Length)
                                    continue;
                                writer.Write("\n");
                                var methodDef = metadata.methodDefs[i];
                                var isAbstract = (methodDef.flags & METHOD_ATTRIBUTE_ABSTRACT) != 0;
                                if (config.DumpMethodOffset)
                                {
                                    var methodPointer = il2Cpp.GetMethodPointer(imageName, methodDef);
                                    if (!isAbstract && methodPointer > 0)
                                    {
                                        var fixedMethodPointer = il2Cpp.GetRVA(methodPointer);
                                        writer.Write("\t// RVA: 0x{0:X} Offset: 0x{1:X} VA: 0x{2:X}", fixedMethodPointer, il2Cpp.MapVATR(methodPointer), methodPointer);
                                    }
                                    else
                                    {
                                        writer.Write("\t// RVA: -1 Offset: -1");
                                    }
                                    if (methodDef.slot != ushort.MaxValue)
                                    {
                                        writer.Write(" Slot: {0}", methodDef.slot);
                                    }
                                    writer.Write("\n");
                                }
                                if (config.DumpAttribute)
                                {
                                    writer.Write(GetCustomAttribute(imageDef, methodDef.customAttributeIndex, methodDef.token, "\t"));
                                }
                                writer.Write("\t");
                                writer.Write(GetModifiers(methodDef));
                                var methodReturnType = SafeGetType(methodDef.returnType);
                                var methodName = metadata.GetStringFromIndex(methodDef.nameIndex);
                                if (methodDef.genericContainerIndex >= 0 && metadata.genericContainers != null &&
                                    methodDef.genericContainerIndex < metadata.genericContainers.Length)
                                {
                                    var genericContainer = metadata.genericContainers[methodDef.genericContainerIndex];
                                    methodName += executor.GetGenericContainerParams(genericContainer);
                                }
                                if (methodReturnType.byref == 1)
                                {
                                    writer.Write("ref ");
                                }
                                writer.Write($"{executor.GetTypeName(methodReturnType, false, false)} {methodName}(");
                                var parameterStrs = new List<string>();
                                for (var j = 0; j < methodDef.parameterCount; ++j)
                                {
                                    var paramIndex = methodDef.parameterStart + j;
                                    if (metadata.parameterDefs == null || paramIndex < 0 || paramIndex >= metadata.parameterDefs.Length)
                                        continue;
                                    var parameterStr = "";
                                    var parameterDef = metadata.parameterDefs[paramIndex];
                                    var parameterName = metadata.GetStringFromIndex(parameterDef.nameIndex);
                                    var parameterType = SafeGetType(parameterDef.typeIndex);
                                    var parameterTypeName = executor.GetTypeName(parameterType, false, false);
                                    if (parameterType.byref == 1)
                                    {
                                        if ((parameterType.attrs & PARAM_ATTRIBUTE_OUT) != 0 && (parameterType.attrs & PARAM_ATTRIBUTE_IN) == 0)
                                        {
                                            parameterStr += "out ";
                                        }
                                        else if ((parameterType.attrs & PARAM_ATTRIBUTE_OUT) == 0 && (parameterType.attrs & PARAM_ATTRIBUTE_IN) != 0)
                                        {
                                            parameterStr += "in ";
                                        }
                                        else
                                        {
                                            parameterStr += "ref ";
                                        }
                                    }
                                    else
                                    {
                                        if ((parameterType.attrs & PARAM_ATTRIBUTE_IN) != 0)
                                        {
                                            parameterStr += "[In] ";
                                        }
                                        if ((parameterType.attrs & PARAM_ATTRIBUTE_OUT) != 0)
                                        {
                                            parameterStr += "[Out] ";
                                        }
                                    }
                                    parameterStr += $"{parameterTypeName} {parameterName}";
                                    if (metadata.GetParameterDefaultValueFromIndex(methodDef.parameterStart + j, out var parameterDefault) && parameterDefault.dataIndex != -1)
                                    {
                                        if (executor.TryGetDefaultValue(parameterDefault.typeIndex, parameterDefault.dataIndex, out var value))
                                        {
                                            parameterStr += " = ";
                                            if (value is string str)
                                            {
                                                parameterStr += $"\"{str.ToEscapedString()}\"";
                                            }
                                            else if (value is char c)
                                            {
                                                var v = (int)c;
                                                parameterStr += $"'\\x{v:x}'";
                                            }
                                            else if (value != null)
                                            {
                                                parameterStr += $"{value}";
                                            }
                                            else
                                            {
                                                writer.Write("null");
                                            }
                                        }
                                        else
                                        {
                                            parameterStr += $" /*Metadata offset 0x{value:X}*/";
                                        }
                                    }
                                    parameterStrs.Add(parameterStr);
                                }
                                writer.Write(string.Join(", ", parameterStrs));
                                if (isAbstract)
                                {
                                    writer.Write(");\n");
                                }
                                else
                                {
                                    writer.Write(") { }\n");
                                }

                                if (il2Cpp.methodDefinitionMethodSpecs.TryGetValue(i, out var methodSpecs))
                                {
                                    writer.Write("\t/* GenericInstMethod :\n");
                                    var groups = methodSpecs.GroupBy(x => il2Cpp.methodSpecGenericMethodPointers[x]);
                                    foreach (var group in groups)
                                    {
                                        writer.Write("\t|\n");
                                        var genericMethodPointer = group.Key;
                                        if (genericMethodPointer > 0)
                                        {
                                            var fixedPointer = il2Cpp.GetRVA(genericMethodPointer);
                                            writer.Write($"\t|-RVA: 0x{fixedPointer:X} Offset: 0x{il2Cpp.MapVATR(genericMethodPointer):X} VA: 0x{genericMethodPointer:X}\n");
                                        }
                                        else
                                        {
                                            writer.Write("\t|-RVA: -1 Offset: -1\n");
                                        }
                                        foreach (var methodSpec in group)
                                        {
                                            (var methodSpecTypeName, var methodSpecMethodName) = executor.GetMethodSpecName(methodSpec);
                                            writer.Write($"\t|-{methodSpecTypeName}.{methodSpecMethodName}\n");
                                        }
                                    }
                                    writer.Write("\t*/\n");
                                }
                            }
                        }
                        writer.Write("}\n");
                    }
                    catch (Exception e)
                    {
                        writer.Write("/*");
                        writer.Write(e);
                        writer.Write("*/\n}\n");
                    }
                }
            }
            writer.Close();
        }

        private Il2CppType SafeGetType(int typeIndex)
        {
            if (typeIndex >= 0 && il2Cpp.types != null && typeIndex < il2Cpp.types.Length && il2Cpp.types[typeIndex] != null)
                return il2Cpp.types[typeIndex];
            var t = new Il2CppType { datapoint = 0, bits = ((uint)Il2CppTypeEnum.IL2CPP_TYPE_OBJECT) << 16 };
            t.Init(il2Cpp.Version);
            return t;
        }

        private string GetEnumUnderlyingTypeName(Il2CppTypeDefinition typeDef)
        {
            var fieldEnd = typeDef.fieldStart + typeDef.field_count;
            for (var i = typeDef.fieldStart; i < fieldEnd; ++i)
            {
                if (i >= 0 && i < metadata.fieldDefs.Length)
                {
                    var fd = metadata.fieldDefs[i];
                    if (metadata.GetFieldDefaultValueFromIndex(i, out var fdv) && fdv.dataIndex != -1)
                    {
                        if (executor.TryGetDefaultValue(fdv.typeIndex, fdv.dataIndex, out var val))
                        {
                            switch (val)
                            {
                                case int: return "int";
                                case uint: return "uint";
                                case byte: return "byte";
                                case sbyte: return "sbyte";
                                case short: return "short";
                                case ushort: return "ushort";
                                case long: return "long";
                                case ulong: return "ulong";
                            }
                        }
                    }
                }
            }
            return "int";
        }

        private SyntheticTypeEnricher.TypeNameIndex typeNameIndex;

        private SyntheticTypeEnricher.TypeNameIndex GetTypeNameIndex()
        {
            return typeNameIndex ??= SyntheticTypeEnricher.TypeNameIndex.Build(metadata);
        }

        private string ResolveFieldTypeName(int typeDefIndex, Il2CppTypeDefinition typeDef, Il2CppFieldDefinition fieldDef, Il2CppType fieldType)
        {
            var name = executor.GetTypeName(fieldType, false, false);
            if (!il2Cpp.IsSynthetic)
                return name;

            var fieldName = metadata.GetStringFromIndex(fieldDef.nameIndex);


            var display = SyntheticTypeEnricher.ResolveDisplayTypeName(
                GetTypeNameIndex(),
                fieldName,
                idx =>
                {
                    var byval = metadata.typeDefs[idx].byvalTypeIndex;
                    if (byval < 0 || byval >= il2Cpp.types.Length)
                        return null;
                    return executor.GetTypeName(il2Cpp.types[byval], false, false);
                });

            if (!string.IsNullOrEmpty(display) && display != "object" && display != "Object")
            {
                if (name == "object" || name == "Object")
                {
                    var idx = GetTypeNameIndex().ResolveTypeDef(fieldName);
                    if (idx >= 0)
                    {
                        var byval = metadata.typeDefs[idx].byvalTypeIndex;
                        if (byval >= 0 && byval < il2Cpp.types.Length)
                        {
                            var cloned = il2Cpp.CloneIl2CppType(il2Cpp.types[byval]);
                            var vis = SyntheticTypeEnricher.GuessFieldVisibility(fieldName);
                            cloned.bits = (cloned.bits & 0xFFFF0000u) | vis;
                            cloned.Init(il2Cpp.Version);
                            il2Cpp.types[fieldDef.typeIndex] = cloned;
                        }
                    }
                    return display;
                }
                var curScore = SyntheticTypeEnricher.TypeNameMatchScore(fieldName, name);
                var dispScore = SyntheticTypeEnricher.TypeNameMatchScore(fieldName, display);
                if (display.StartsWith("List<", StringComparison.Ordinal) || display.EndsWith("[]", StringComparison.Ordinal))
                    return display;
                if (dispScore > curScore)
                    return display;
            }

            return name;
        }

        private Il2CppTypeEnum GetEnumUnderlyingTypeEnum(string typeName)
        {
            return typeName switch
            {
                "int" => Il2CppTypeEnum.IL2CPP_TYPE_I4,
                "uint" => Il2CppTypeEnum.IL2CPP_TYPE_U4,
                "byte" => Il2CppTypeEnum.IL2CPP_TYPE_U1,
                "sbyte" => Il2CppTypeEnum.IL2CPP_TYPE_I1,
                "short" => Il2CppTypeEnum.IL2CPP_TYPE_I2,
                "ushort" => Il2CppTypeEnum.IL2CPP_TYPE_U2,
                "long" => Il2CppTypeEnum.IL2CPP_TYPE_I8,
                "ulong" => Il2CppTypeEnum.IL2CPP_TYPE_U8,
                _ => Il2CppTypeEnum.IL2CPP_TYPE_I4
            };
        }

        public string GetCustomAttribute(Il2CppImageDefinition imageDef, int customAttributeIndex, uint token, string padding = "")
        {
            if (il2Cpp.Version < 21)
                return string.Empty;
            var attributeIndex = metadata.GetCustomAttributeIndex(imageDef, customAttributeIndex, token);
            if (attributeIndex >= 0)
            {
                if (il2Cpp.Version < 29)
                {
                    var methodPointer = executor.customAttributeGenerators[attributeIndex];
                    var fixedMethodPointer = il2Cpp.GetRVA(methodPointer);
                    var attributeTypeRange = metadata.attributeTypeRanges[attributeIndex];
                    var sb = new StringBuilder();
                    for (var i = 0; i < attributeTypeRange.count; i++)
                    {
                        var idx = attributeTypeRange.start + i;
                        if (metadata.attributeTypes != null && idx >= 0 && idx < metadata.attributeTypes.Length)
                        {
                            var typeIndex = metadata.attributeTypes[idx];
                            sb.AppendFormat("{0}[{1}] // RVA: 0x{2:X} Offset: 0x{3:X} VA: 0x{4:X}\n",
                                padding,
                                executor.GetTypeName(SafeGetType(typeIndex), false, false),
                                fixedMethodPointer,
                                il2Cpp.MapVATR(methodPointer),
                                methodPointer);
                        }
                    }
                    return sb.ToString();
                }
                else
                {
                    try
                    {
                        var startRange = metadata.attributeDataRanges[attributeIndex];
                        int endOffset = attributeIndex + 1 < metadata.attributeDataRanges.Length
                            ? (int)metadata.attributeDataRanges[attributeIndex + 1].startOffset
                            : metadata.header.attributeDataSize;
                        metadata.Position = metadata.header.attributeDataOffset + startRange.startOffset;
                        var buff = metadata.ReadBytes(endOffset - (int)startRange.startOffset);
                        var reader = new CustomAttributeDataReader(executor, buff);
                        if (reader.Count == 0)
                        {
                            return string.Empty;
                        }
                        var sb = new StringBuilder();
                        for (var i = 0; i < reader.Count; i++)
                        {
                            sb.Append(padding);
                            sb.Append(reader.GetStringCustomAttributeData());
                            sb.Append('\n');
                        }
                        return sb.ToString();
                    }
                    catch (Exception e)
                    {
                        return $"{padding}/*Custom Attribute Error: {e.Message}*/\n";
                    }
                }
            }
            else
            {
                return string.Empty;
            }
        }

        public string GetModifiers(Il2CppMethodDefinition methodDef)
        {
            if (methodModifiers.TryGetValue(methodDef, out string str))
                return str;
            var access = methodDef.flags & METHOD_ATTRIBUTE_MEMBER_ACCESS_MASK;
            switch (access)
            {
                case METHOD_ATTRIBUTE_PRIVATE:
                    str += "private ";
                    break;
                case METHOD_ATTRIBUTE_PUBLIC:
                    str += "public ";
                    break;
                case METHOD_ATTRIBUTE_FAMILY:
                    str += "protected ";
                    break;
                case METHOD_ATTRIBUTE_ASSEM:
                case METHOD_ATTRIBUTE_FAM_AND_ASSEM:
                    str += "internal ";
                    break;
                case METHOD_ATTRIBUTE_FAM_OR_ASSEM:
                    str += "protected internal ";
                    break;
            }
            if ((methodDef.flags & METHOD_ATTRIBUTE_STATIC) != 0)
                str += "static ";
            if ((methodDef.flags & METHOD_ATTRIBUTE_ABSTRACT) != 0)
            {
                str += "abstract ";
                if ((methodDef.flags & METHOD_ATTRIBUTE_VTABLE_LAYOUT_MASK) == METHOD_ATTRIBUTE_REUSE_SLOT)
                    str += "override ";
            }
            else if ((methodDef.flags & METHOD_ATTRIBUTE_FINAL) != 0)
            {
                if ((methodDef.flags & METHOD_ATTRIBUTE_VTABLE_LAYOUT_MASK) == METHOD_ATTRIBUTE_REUSE_SLOT)
                    str += "sealed override ";
            }
            else if ((methodDef.flags & METHOD_ATTRIBUTE_VIRTUAL) != 0)
            {
                if ((methodDef.flags & METHOD_ATTRIBUTE_VTABLE_LAYOUT_MASK) == METHOD_ATTRIBUTE_NEW_SLOT)
                    str += "virtual ";
                else
                    str += "override ";
            }
            if ((methodDef.flags & METHOD_ATTRIBUTE_PINVOKE_IMPL) != 0)
                str += "extern ";
            methodModifiers.Add(methodDef, str);
            return str;
        }

    }
}
