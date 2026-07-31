using System;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using Newtonsoft.Json;
using Newtonsoft.Json.Linq;

namespace Il2CppDumper
{
    /// <summary>
    /// Import ground-truth field offsets, field type names, and method RVAs from a
    /// full memory dump (e.g. HonorofKings_MemoryDump_IOS: dump.cs + script.json).
    /// Used when disk CR/MR are empty so synthetic estimates can be corrected.
    /// </summary>
    public class ReferenceMethodData
    {
        public string ReturnType;
        public List<string> ParameterTypes = new();
    }

    public sealed class ReferenceDumpData
    {
        /// <summary>old typeDefIndex (from reference dump.cs) → full name string (e.g. UnityEngine.Physics)</summary>
        public Dictionary<int, string> TypeIndexToFullName { get; } = new();

        /// <summary>new typeDefIndex → old typeDefIndex</summary>
        public Dictionary<int, int> NewToOldTypeIndices { get; } = new();

        /// <summary>typeDefIndex → fieldName → offset (as printed in dump.cs, e.g. 0x20)</summary>
        public Dictionary<int, Dictionary<string, int>> FieldOffsets { get; } = new();

        /// <summary>typeDefIndex → set of static field names</summary>
        public Dictionary<int, HashSet<string>> StaticFields { get; } = new();

        /// <summary>typeDefIndex → fieldName → type name string from reference</summary>
        public Dictionary<int, Dictionary<string, string>> FieldTypes { get; } = new();

        /// <summary>ScriptMethod Name (Namespace.Type$$Method) → Address (RVA)</summary>
        public Dictionary<string, ulong> MethodRvaByScriptName { get; } = new(StringComparer.Ordinal);

        /// <summary>typeDefIndex → methodName → first RVA seen (fallback if script name missing)</summary>
        public Dictionary<int, Dictionary<string, ulong>> MethodRvaByTypeMethod { get; } = new();

        /// <summary>typeDefIndex → methodName → list of method signatures parsed from reference</summary>
        public Dictionary<int, Dictionary<string, List<ReferenceMethodData>>> MethodSignatures { get; } = new();

        public int FieldOffsetCount { get; set; }
        public int FieldTypeCount { get; set; }
        public int MethodRvaCount { get; set; }

        /// <summary>ScriptString entries from reference (path strings + addresses for IDA).</summary>
        public List<ScriptString> ScriptStrings { get; } = new();

        /// <summary>ScriptMetadataMethod entries from reference.</summary>
        public List<ScriptMetadataMethod> ScriptMetadataMethods { get; } = new();

        /// <summary>ScriptMetadata (TypeInfo/Type) entries from reference.</summary>
        public List<ScriptMetadata> ScriptMetadatas { get; } = new();

        /// <summary>typeDefIndex → fieldName → const value as printed (string already unescaped where possible)</summary>
        public Dictionary<int, Dictionary<string, object>> FieldConstValues { get; } = new();
        public int FieldConstCount { get; set; }
    }

    public static class ReferenceDumpImporter
    {
        private static readonly Regex TypeDefHeader = new(
            @"//\s*TypeDefIndex:\s*(\d+)\s*$",
            RegexOptions.Compiled);

        private static readonly Regex ClassOrStruct = new(
            @"^\s*(?:public|internal|private|protected)?\s*(?:abstract\s+|sealed\s+|static\s+)*(?:class|struct|interface|enum)\s+",
            RegexOptions.Compiled);

        private static readonly Regex FieldLine = new(
            @"^\s*(?:public|private|protected|internal|static|readonly|const|volatile|\s)+.+?\s+(\S+)\s*;\s*//\s*0x([0-9A-Fa-f]+)\s*$",
            RegexOptions.Compiled);

        private static readonly Regex FieldLineLoose = new(
            @"^\s*.+\s+(\S+)\s*;\s*//\s*0x([0-9A-Fa-f]+)\s*$",
            RegexOptions.Compiled);

        // public const string s_foo = "Prefab_...";
        // private const int X = 123;
        // public const float Y = 1.5;
        private static readonly Regex ConstFieldLine = new(
            @"^\s*(?:public|private|protected|internal)?\s*const\s+(\S+)\s+(\S+)\s*=\s*(.+?)\s*;\s*$",
            RegexOptions.Compiled);

        private static readonly Regex RvaLine = new(
            @"^\s*//\s*RVA:\s*0x([0-9A-Fa-f]+)\s+Offset:\s*0x([0-9A-Fa-f]+)",
            RegexOptions.Compiled);

        private static readonly Regex MethodLine = new(
            @"^\s*(?:public|private|protected|internal|static|virtual|override|abstract|extern|new|sealed|\s)+.+?\s+(\S+)\s*\(",
            RegexOptions.Compiled);

        public sealed class LoadOptions
        {
            /// <summary>Import 700k+ ScriptMetadataMethod (slow). Default false.</summary>
            public bool ImportScriptMetadataMethods { get; set; }

            /// <summary>Use disk cache for parsed reference. Default true.</summary>
            public bool UseCache { get; set; } = true;
        }

        /// <summary>
        /// Resolve reference dump directory. Only explicit / env / config / local "reference" folder —
        /// does NOT auto-scan Downloads/Telegram (that made dumps slow and forced a dependency).
        /// </summary>
        public static string FindReferenceDir(string explicitPath, string outputDir, string binaryPath, string configPath = null)
        {
            if (!string.IsNullOrWhiteSpace(explicitPath) && Directory.Exists(explicitPath))
                return Path.GetFullPath(explicitPath);

            var env = Environment.GetEnvironmentVariable("IL2CPP_REFERENCE_DUMP");
            if (!string.IsNullOrWhiteSpace(env) && Directory.Exists(env))
                return Path.GetFullPath(env);

            if (!string.IsNullOrWhiteSpace(configPath) && Directory.Exists(configPath))
                return Path.GetFullPath(configPath);

            // Optional local convention only (user opts in by placing folder here)
            var parentDir = !string.IsNullOrEmpty(binaryPath) ? Path.GetDirectoryName(binaryPath) : null;
            var parentParentDir = !string.IsNullOrEmpty(parentDir) ? Path.GetDirectoryName(parentDir) : null;

            var candidates = new[]
            {
                !string.IsNullOrEmpty(outputDir) ? Path.Combine(outputDir, "reference") : null,
                !string.IsNullOrEmpty(parentDir) ? Path.Combine(parentDir, "reference") : null,
                !string.IsNullOrEmpty(parentParentDir) ? Path.Combine(parentParentDir, "reference") : null,
                !string.IsNullOrEmpty(parentParentDir) ? Path.Combine(parentParentDir, "dump old") : null,
                !string.IsNullOrEmpty(parentParentDir) ? Path.Combine(parentParentDir, "dump_old") : null,
                !string.IsNullOrEmpty(parentDir) ? Path.Combine(parentDir, "dump old") : null,
                !string.IsNullOrEmpty(parentDir) ? Path.Combine(parentDir, "dump_old") : null,
            };

            foreach (var c in candidates)
            {
                try
                {
                    if (string.IsNullOrEmpty(c)) continue;
                    var full = Path.GetFullPath(c);
                    if (Directory.Exists(full) &&
                        (File.Exists(Path.Combine(full, "dump.cs")) || File.Exists(Path.Combine(full, "script.json"))))
                        return full;
                }
                catch { /* skip */ }
            }

            return null;
        }

        public static ReferenceDumpData Load(string referenceDir, LoadOptions options = null)
        {
            options ??= new LoadOptions();
            var data = new ReferenceDumpData();
            if (string.IsNullOrEmpty(referenceDir) || !Directory.Exists(referenceDir))
                return data;

            if (options.UseCache && TryLoadCache(referenceDir, options, out var cached))
                return cached;

            var dumpCs = Path.Combine(referenceDir, "dump.cs");
            if (File.Exists(dumpCs))
                ParseDumpCs(dumpCs, data);

            var scriptJson = Path.Combine(referenceDir, "script.json");
            if (File.Exists(scriptJson))
                ParseScriptJson(scriptJson, data, options.ImportScriptMetadataMethods);

            if (options.UseCache)
                TrySaveCache(referenceDir, options, data);

            return data;
        }

        private static string CachePath(string referenceDir, LoadOptions options)
        {
            var tag = options.ImportScriptMetadataMethods ? "full" : "lite";
            return Path.Combine(referenceDir, $".il2cpp_ref_cache_{tag}.json");
        }

        private static string CacheStamp(string referenceDir)
        {
            long stamp = 0;
            foreach (var name in new[] { "dump.cs", "script.json" })
            {
                var p = Path.Combine(referenceDir, name);
                if (!File.Exists(p)) continue;
                var fi = new FileInfo(p);
                stamp ^= fi.Length;
                stamp ^= fi.LastWriteTimeUtc.Ticks;
            }
            return stamp.ToString("X");
        }

        private sealed class CacheFile
        {
            public string Stamp;
            public Dictionary<int, Dictionary<string, int>> FieldOffsets;
            public Dictionary<int, Dictionary<string, string>> FieldTypes;
            public Dictionary<string, ulong> MethodRvaByScriptName;
            public Dictionary<int, Dictionary<string, ulong>> MethodRvaByTypeMethod;
            public List<ScriptString> ScriptStrings;
            public List<ScriptMetadataMethod> ScriptMetadataMethods;
            public List<ScriptMetadata> ScriptMetadatas;
            public Dictionary<int, Dictionary<string, string>> FieldConstValuesAsString;
            public int FieldOffsetCount, FieldTypeCount, MethodRvaCount, FieldConstCount;
        }

        private static bool TryLoadCache(string referenceDir, LoadOptions options, out ReferenceDumpData data)
        {
            data = null;
            try
            {
                var path = CachePath(referenceDir, options);
                if (!File.Exists(path)) return false;
                var cache = JsonConvert.DeserializeObject<CacheFile>(File.ReadAllText(path));
                if (cache == null || cache.Stamp != CacheStamp(referenceDir))
                    return false;

                data = new ReferenceDumpData();
                if (cache.FieldOffsets != null)
                    foreach (var kv in cache.FieldOffsets)
                        data.FieldOffsets[kv.Key] = kv.Value;
                if (cache.FieldTypes != null)
                    foreach (var kv in cache.FieldTypes)
                        data.FieldTypes[kv.Key] = kv.Value;
                if (cache.MethodRvaByScriptName != null)
                    foreach (var kv in cache.MethodRvaByScriptName)
                        data.MethodRvaByScriptName[kv.Key] = kv.Value;
                if (cache.MethodRvaByTypeMethod != null)
                    foreach (var kv in cache.MethodRvaByTypeMethod)
                        data.MethodRvaByTypeMethod[kv.Key] = kv.Value;
                if (cache.ScriptStrings != null)
                    data.ScriptStrings.AddRange(cache.ScriptStrings);
                if (cache.ScriptMetadataMethods != null)
                    data.ScriptMetadataMethods.AddRange(cache.ScriptMetadataMethods);
                if (cache.ScriptMetadatas != null)
                    data.ScriptMetadatas.AddRange(cache.ScriptMetadatas);
                if (cache.FieldConstValuesAsString != null)
                {
                    foreach (var kv in cache.FieldConstValuesAsString)
                    {
                        var map = new Dictionary<string, object>(StringComparer.Ordinal);
                        data.FieldTypes.TryGetValue(kv.Key, out var typesForTd);
                        foreach (var f in kv.Value)
                        {
                            var ctype = "string";
                            if (typesForTd != null && typesForTd.TryGetValue(f.Key, out var tn))
                                ctype = tn;
                            map[f.Key] = ParseConstLiteral(ctype, f.Value);
                        }
                        data.FieldConstValues[kv.Key] = map;
                    }
                }
                data.FieldOffsetCount = cache.FieldOffsetCount;
                data.FieldTypeCount = cache.FieldTypeCount;
                data.MethodRvaCount = cache.MethodRvaCount;
                data.FieldConstCount = cache.FieldConstCount;
                return true;
            }
            catch
            {
                data = null;
                return false;
            }
        }

        private static void TrySaveCache(string referenceDir, LoadOptions options, ReferenceDumpData data)
        {
            try
            {
                var constStr = new Dictionary<int, Dictionary<string, string>>();
                foreach (var kv in data.FieldConstValues)
                {
                    var m = new Dictionary<string, string>(StringComparer.Ordinal);
                    foreach (var f in kv.Value)
                        m[f.Key] = f.Value switch
                        {
                            null => "null",
                            string s => "\"" + s.Replace("\\", "\\\\").Replace("\"", "\\\"") + "\"",
                            bool b => b ? "true" : "false",
                            _ => Convert.ToString(f.Value, CultureInfo.InvariantCulture)
                        };
                    constStr[kv.Key] = m;
                }

                var cache = new CacheFile
                {
                    Stamp = CacheStamp(referenceDir),
                    FieldOffsets = data.FieldOffsets,
                    FieldTypes = data.FieldTypes,
                    MethodRvaByScriptName = data.MethodRvaByScriptName,
                    MethodRvaByTypeMethod = data.MethodRvaByTypeMethod,
                    ScriptStrings = data.ScriptStrings,
                    ScriptMetadataMethods = options.ImportScriptMetadataMethods ? data.ScriptMetadataMethods : new List<ScriptMetadataMethod>(),
                    ScriptMetadatas = data.ScriptMetadatas,
                    FieldConstValuesAsString = constStr,
                    FieldOffsetCount = data.FieldOffsetCount,
                    FieldTypeCount = data.FieldTypeCount,
                    MethodRvaCount = data.MethodRvaCount,
                    FieldConstCount = data.FieldConstCount
                };
                File.WriteAllText(CachePath(referenceDir, options),
                    JsonConvert.SerializeObject(cache), new UTF8Encoding(false));
            }
            catch { /* cache is optional */ }
        }

        private static int GetIndentationDepth(string line)
        {
            var depth = 0;
            for (var i = 0; i < line.Length; i++)
            {
                if (line[i] == '\t') depth++;
                else if (line[i] == ' ')
                {
                    var spaces = 0;
                    while (i < line.Length && line[i] == ' ')
                    {
                        spaces++;
                        i++;
                    }
                    depth += spaces / 4;
                    if (i < line.Length) i--;
                }
                else break;
            }
            return depth;
        }

        private static void ParseDumpCs(string path, ReferenceDumpData data)
        {
            var typeDefIndex = -1;
            var inFields = false;
            var inMethods = false;
            ulong pendingRva = 0;
            var hasPendingRva = false;

            var currentNamespace = "";
            var nestingStack = new List<string>();

            foreach (var raw in File.ReadLines(path))
            {
                var line = raw;

                var nsPrefix = "// Namespace: ";
                if (line.StartsWith(nsPrefix, StringComparison.Ordinal))
                {
                    currentNamespace = line.Substring(nsPrefix.Length).Trim();
                    continue;
                }

                // class Foo // TypeDefIndex: 123
                if (line.Contains("TypeDefIndex:", StringComparison.Ordinal))
                {
                    var m = TypeDefHeader.Match(line);
                    if (m.Success && int.TryParse(m.Groups[1].Value, out var idx))
                    {
                        typeDefIndex = idx;
                        inFields = false;
                        inMethods = false;
                        hasPendingRva = false;

                        var classIndex = line.IndexOf("class ", StringComparison.Ordinal);
                        if (classIndex < 0) classIndex = line.IndexOf("struct ", StringComparison.Ordinal);
                        if (classIndex < 0) classIndex = line.IndexOf("interface ", StringComparison.Ordinal);
                        if (classIndex < 0) classIndex = line.IndexOf("enum ", StringComparison.Ordinal);

                        if (classIndex >= 0)
                        {
                            var start = classIndex + 6;
                            if (line.IndexOf("struct ", StringComparison.Ordinal) == classIndex) start = classIndex + 7;
                            else if (line.IndexOf("interface ", StringComparison.Ordinal) == classIndex) start = classIndex + 10;
                            else if (line.IndexOf("enum ", StringComparison.Ordinal) == classIndex) start = classIndex + 5;

                            var end = start;
                            while (end < line.Length && line[end] != ' ' && line[end] != ':' && line[end] != '/' && line[end] != '\r' && line[end] != '\n')
                            {
                                end++;
                            }
                            var currentClassName = line.Substring(start, end - start).Trim();
                            if (!string.IsNullOrEmpty(currentClassName))
                            {
                                var depth = GetIndentationDepth(line);
                                while (nestingStack.Count > depth)
                                {
                                    nestingStack.RemoveAt(nestingStack.Count - 1);
                                }
                                var fullName = currentNamespace;
                                if (nestingStack.Count > 0)
                                {
                                    fullName = string.IsNullOrEmpty(fullName) 
                                        ? string.Join("/", nestingStack) + "/" + currentClassName 
                                        : fullName + "." + string.Join("/", nestingStack) + "/" + currentClassName;
                                }
                                else
                                {
                                    fullName = string.IsNullOrEmpty(fullName) ? currentClassName : fullName + "." + currentClassName;
                                }
                                data.TypeIndexToFullName[idx] = fullName;
                                nestingStack.Add(currentClassName);
                            }
                        }
                    }
                    continue;
                }

                if (typeDefIndex < 0)
                    continue;

                var trimmed = line.Trim();
                if (trimmed == "// Fields" || trimmed == "//Fields")
                {
                    inFields = true;
                    inMethods = false;
                    continue;
                }
                if (trimmed is "// Methods" or "//Methods" or "// Properties" or "//Properties")
                {
                    inFields = false;
                    inMethods = trimmed.Contains("Method", StringComparison.Ordinal);
                    continue;
                }
                if (trimmed == "}" && (inFields || inMethods))
                {
                    // end of type
                    typeDefIndex = -1;
                    inFields = false;
                    inMethods = false;
                    hasPendingRva = false;
                    continue;
                }

                if (inFields)
                {
                    // const string/int/float with initializer (no // 0x offset)
                    var cm = ConstFieldLine.Match(line);
                    if (cm.Success)
                    {
                        var ctype = cm.Groups[1].Value;
                        var fname = cm.Groups[2].Value;
                        var rawVal = cm.Groups[3].Value.Trim();
                        if (!data.FieldTypes.TryGetValue(typeDefIndex, out var ft))
                        {
                            ft = new Dictionary<string, string>(StringComparer.Ordinal);
                            data.FieldTypes[typeDefIndex] = ft;
                        }
                        ft[fname] = ctype;
                        data.FieldTypeCount++;

                        if (!data.FieldConstValues.TryGetValue(typeDefIndex, out var cv))
                        {
                            cv = new Dictionary<string, object>(StringComparer.Ordinal);
                            data.FieldConstValues[typeDefIndex] = cv;
                        }
                        cv[fname] = ParseConstLiteral(ctype, rawVal);
                        data.FieldConstCount++;
                        continue;
                    }

                    var fm = FieldLine.Match(line);
                    if (!fm.Success)
                        fm = FieldLineLoose.Match(line);
                    if (fm.Success &&
                        int.TryParse(fm.Groups[2].Value, NumberStyles.HexNumber, CultureInfo.InvariantCulture, out var off))
                    {
                        var fname = fm.Groups[1].Value;
                        if (!data.FieldOffsets.TryGetValue(typeDefIndex, out var fo))
                        {
                            fo = new Dictionary<string, int>(StringComparer.Ordinal);
                            data.FieldOffsets[typeDefIndex] = fo;
                        }
                        fo[fname] = off;
                        data.FieldOffsetCount++;

                        var semi = line.IndexOf(';');
                        if (semi >= 0)
                        {
                            var beforeSemi = line.Substring(0, semi);
                            var parts = beforeSemi.Split((char[])null, StringSplitOptions.RemoveEmptyEntries);
                            if (parts.Contains("static"))
                            {
                                if (!data.StaticFields.TryGetValue(typeDefIndex, out var sf))
                                {
                                    sf = new HashSet<string>(StringComparer.Ordinal);
                                    data.StaticFields[typeDefIndex] = sf;
                                }
                                sf.Add(fname);
                            }
                        }

                        var typeName = ExtractFieldTypeName(line, fname);
                        if (!string.IsNullOrEmpty(typeName))
                        {
                            if (!data.FieldTypes.TryGetValue(typeDefIndex, out var ft))
                            {
                                ft = new Dictionary<string, string>(StringComparer.Ordinal);
                                data.FieldTypes[typeDefIndex] = ft;
                            }
                            ft[fname] = typeName;
                            data.FieldTypeCount++;
                        }
                    }
                    continue;
                }

                if (inMethods)
                {
                    var rm = RvaLine.Match(line);
                    if (rm.Success &&
                        ulong.TryParse(rm.Groups[1].Value, NumberStyles.HexNumber, CultureInfo.InvariantCulture, out var rva))
                    {
                        pendingRva = rva;
                        hasPendingRva = true;
                        continue;
                    }

                    if (hasPendingRva)
                    {
                        var mm = MethodLine.Match(line);
                        if (mm.Success)
                        {
                            var mname = mm.Groups[1].Value;
                            // strip generic arity Method`1 → Method
                            var tick = mname.IndexOf('`');
                            if (tick > 0)
                                mname = mname.Substring(0, tick);

                            var sig = ParseMethodSignature(line, mname);
                            if (sig != null)
                            {
                                if (!data.MethodSignatures.TryGetValue(typeDefIndex, out var ms))
                                {
                                    ms = new Dictionary<string, List<ReferenceMethodData>>(StringComparer.Ordinal);
                                    data.MethodSignatures[typeDefIndex] = ms;
                                }
                                if (!ms.TryGetValue(mname, out var list))
                                {
                                    list = new List<ReferenceMethodData>();
                                    ms[mname] = list;
                                }
                                list.Add(sig);
                            }

                            if (!data.MethodRvaByTypeMethod.TryGetValue(typeDefIndex, out var md))
                            {
                                md = new Dictionary<string, ulong>(StringComparer.Ordinal);
                                data.MethodRvaByTypeMethod[typeDefIndex] = md;
                            }
                            // keep first (overloads share name — first is OK for many cases)
                            if (!md.ContainsKey(mname) && pendingRva != 0 && pendingRva != ulong.MaxValue)
                            {
                                md[mname] = pendingRva;
                                data.MethodRvaCount++;
                            }
                            hasPendingRva = false;
                        }
                    }
                }
            }
        }

        private static ReferenceMethodData ParseMethodSignature(string line, string methodName)
        {
            try
            {
                var openParen = line.IndexOf('(');
                if (openParen < 0) return null;
                var closeParen = line.IndexOf(')', openParen);
                if (closeParen < 0) return null;

                var decl = line.Substring(0, openParen).Trim();
                var paramStr = line.Substring(openParen + 1, closeParen - openParen - 1).Trim();

                var declParts = decl.Split((char[])null, StringSplitOptions.RemoveEmptyEntries);
                if (declParts.Length < 2) return null;

                var nameIndex = -1;
                for (var i = 0; i < declParts.Length; i++)
                {
                    if (declParts[i].StartsWith(methodName, StringComparison.Ordinal))
                    {
                        nameIndex = i;
                        break;
                    }
                }
                if (nameIndex <= 0) return null;

                var retType = declParts[nameIndex - 1];

                var sig = new ReferenceMethodData { ReturnType = retType };

                if (!string.IsNullOrEmpty(paramStr))
                {
                    var paramParts = SplitParameters(paramStr);
                    foreach (var p in paramParts)
                    {
                        var trimmed = p.Trim();
                        var lastSpace = trimmed.LastIndexOf(' ');
                        if (lastSpace > 0)
                        {
                            var pType = trimmed.Substring(0, lastSpace).Trim();
                            sig.ParameterTypes.Add(pType);
                        }
                    }
                }

                return sig;
            }
            catch
            {
                return null;
            }
        }

        private static List<string> SplitParameters(string paramStr)
        {
            var list = new List<string>();
            var start = 0;
            var depth = 0;
            for (var i = 0; i < paramStr.Length; i++)
            {
                if (paramStr[i] == '<') depth++;
                else if (paramStr[i] == '>') depth--;
                else if (paramStr[i] == ',' && depth == 0)
                {
                    list.Add(paramStr.Substring(start, i - start));
                    start = i + 1;
                }
            }
            if (start < paramStr.Length)
            {
                list.Add(paramStr.Substring(start));
            }
            return list;
        }

        private static object ParseConstLiteral(string typeName, string raw)
        {
            if (raw.Equals("null", StringComparison.OrdinalIgnoreCase))
                return null;
            if (raw.Equals("true", StringComparison.OrdinalIgnoreCase))
                return true;
            if (raw.Equals("false", StringComparison.OrdinalIgnoreCase))
                return false;

            // string: "...."
            if (raw.Length >= 2 && raw[0] == '"')
            {
                var end = raw.LastIndexOf('"');
                if (end > 0)
                {
                    var inner = raw.Substring(1, end - 1);
                    // minimal unescape
                    return inner.Replace("\\\\", "\\").Replace("\\\"", "\"").Replace("\\n", "\n").Replace("\\t", "\t");
                }
            }

            // char
            if (raw.Length >= 3 && raw[0] == '\'')
                return raw[1];

            // float
            if (typeName.Contains("float", StringComparison.OrdinalIgnoreCase) || raw.EndsWith("f", StringComparison.OrdinalIgnoreCase))
            {
                var t = raw.TrimEnd('f', 'F');
                if (float.TryParse(t, NumberStyles.Float, CultureInfo.InvariantCulture, out var f))
                    return f;
            }

            if (typeName.Contains("double", StringComparison.OrdinalIgnoreCase) ||
                double.TryParse(raw, NumberStyles.Float, CultureInfo.InvariantCulture, out var d) &&
                typeName.Contains("double", StringComparison.OrdinalIgnoreCase))
            {
                if (double.TryParse(raw, NumberStyles.Float, CultureInfo.InvariantCulture, out d))
                    return d;
            }

            if (long.TryParse(raw, NumberStyles.Integer, CultureInfo.InvariantCulture, out var l))
            {
                if (typeName is "int" or "Int32") return (int)l;
                if (typeName is "uint" or "UInt32") return (uint)l;
                if (typeName is "byte") return (byte)l;
                if (typeName is "bool") return l != 0;
                return (int)l;
            }

            return raw;
        }

        public static bool TryGetFieldConst(ReferenceDumpData data, int typeDefIndex, string fieldName, out object value)
        {
            value = null;
            if (data?.FieldConstValues == null || string.IsNullOrEmpty(fieldName))
                return false;
            if (!data.FieldConstValues.TryGetValue(typeDefIndex, out var map))
                return false;
            return map.TryGetValue(fieldName, out value);
        }

        private static string ExtractFieldTypeName(string line, string fieldName)
        {
            try
            {
                var semi = line.IndexOf(';');
                if (semi < 0) return null;
                var before = line.Substring(0, semi).Trim();
                // remove trailing field name
                if (!before.EndsWith(fieldName, StringComparison.Ordinal))
                    return null;
                before = before.Substring(0, before.Length - fieldName.Length).Trim();
                // strip modifiers
                var parts = before.Split((char[])null, StringSplitOptions.RemoveEmptyEntries);
                var mods = new HashSet<string>(StringComparer.Ordinal)
                {
                    "public", "private", "protected", "internal", "static", "readonly",
                    "volatile", "const", "new", "unsafe"
                };
                var typeParts = new List<string>();
                foreach (var p in parts)
                {
                    if (mods.Contains(p)) continue;
                    typeParts.Add(p);
                }
                if (typeParts.Count == 0) return null;
                return string.Join(" ", typeParts);
            }
            catch
            {
                return null;
            }
        }

        private static void ParseScriptJson(string path, ReferenceDumpData data, bool importScriptMetadataMethods)
        {
            // Stream parse — reference script.json can be 200MB+; avoid full JObject materialization.
            try
            {
                using var sr = new StreamReader(path);
                using var reader = new JsonTextReader(sr) { CloseInput = true };
                if (!reader.Read() || reader.TokenType != JsonToken.StartObject)
                    return;

                while (reader.Read())
                {
                    if (reader.TokenType == JsonToken.EndObject)
                        break;
                    if (reader.TokenType != JsonToken.PropertyName)
                        continue;

                    var prop = reader.Value?.ToString();
                    if (!reader.Read())
                        break;

                    if (reader.TokenType != JsonToken.StartArray)
                    {
                        if (reader.TokenType is JsonToken.StartObject or JsonToken.StartArray)
                            SkipContainer(reader);
                        continue;
                    }

                    switch (prop)
                    {
                        case "ScriptMethod":
                            ParseScriptMethodArray(reader, data);
                            break;
                        case "ScriptString":
                            ParseScriptStringArray(reader, data);
                            break;
                        case "ScriptMetadataMethod":
                            if (importScriptMetadataMethods)
                                ParseScriptMetadataMethodArray(reader, data);
                            else
                                SkipContainer(reader); // huge (700k+) — skip unless requested
                            break;
                        case "ScriptMetadata":
                            ParseScriptMetadataArray(reader, data);
                            break;
                        default:
                            SkipContainer(reader);
                            break;
                    }
                }

                data.MethodRvaCount = Math.Max(data.MethodRvaCount, data.MethodRvaByScriptName.Count);
            }
            catch
            {
                // keep whatever was parsed
            }
        }

        private static void SkipContainer(JsonTextReader reader)
        {
            var depth = 1;
            while (depth > 0 && reader.Read())
            {
                if (reader.TokenType is JsonToken.StartArray or JsonToken.StartObject)
                    depth++;
                else if (reader.TokenType is JsonToken.EndArray or JsonToken.EndObject)
                    depth--;
            }
        }

        private static void ParseScriptMethodArray(JsonTextReader reader, ReferenceDumpData data)
        {
            while (reader.Read() && reader.TokenType != JsonToken.EndArray)
            {
                if (reader.TokenType != JsonToken.StartObject) continue;
                string name = null;
                ulong addr = 0;
                while (reader.Read() && reader.TokenType != JsonToken.EndObject)
                {
                    if (reader.TokenType != JsonToken.PropertyName) continue;
                    var p = reader.Value?.ToString();
                    if (!reader.Read()) break;
                    if (p == "Name") name = reader.Value?.ToString();
                    else if (p == "Address") TryReadUlongToken(reader, out addr);
                }
                if (!string.IsNullOrEmpty(name) && addr != 0)
                    data.MethodRvaByScriptName[name] = addr;
            }
        }

        private static void ParseScriptStringArray(JsonTextReader reader, ReferenceDumpData data)
        {
            while (reader.Read() && reader.TokenType != JsonToken.EndArray)
            {
                if (reader.TokenType != JsonToken.StartObject) continue;
                string value = null;
                ulong addr = 0;
                var hasAddr = false;
                while (reader.Read() && reader.TokenType != JsonToken.EndObject)
                {
                    if (reader.TokenType != JsonToken.PropertyName) continue;
                    var p = reader.Value?.ToString();
                    if (!reader.Read()) break;
                    if (p == "Value") value = reader.Value?.ToString() ?? "";
                    else if (p == "Address") hasAddr = TryReadUlongToken(reader, out addr);
                }
                if (hasAddr && value != null)
                    data.ScriptStrings.Add(new ScriptString { Address = addr, Value = value });
            }
        }

        private static void ParseScriptMetadataMethodArray(JsonTextReader reader, ReferenceDumpData data)
        {
            while (reader.Read() && reader.TokenType != JsonToken.EndArray)
            {
                if (reader.TokenType != JsonToken.StartObject) continue;
                string name = null;
                ulong addr = 0, methodAddr = 0;
                var hasAddr = false;
                while (reader.Read() && reader.TokenType != JsonToken.EndObject)
                {
                    if (reader.TokenType != JsonToken.PropertyName) continue;
                    var p = reader.Value?.ToString();
                    if (!reader.Read()) break;
                    if (p == "Name") name = reader.Value?.ToString();
                    else if (p == "Address") hasAddr = TryReadUlongToken(reader, out addr);
                    else if (p == "MethodAddress") TryReadUlongToken(reader, out methodAddr);
                }
                if (hasAddr && !string.IsNullOrEmpty(name))
                {
                    data.ScriptMetadataMethods.Add(new ScriptMetadataMethod
                    {
                        Address = addr,
                        Name = name,
                        MethodAddress = methodAddr
                    });
                }
            }
        }

        private static void ParseScriptMetadataArray(JsonTextReader reader, ReferenceDumpData data)
        {
            while (reader.Read() && reader.TokenType != JsonToken.EndArray)
            {
                if (reader.TokenType != JsonToken.StartObject) continue;
                string name = null, sig = null;
                ulong addr = 0;
                var hasAddr = false;
                while (reader.Read() && reader.TokenType != JsonToken.EndObject)
                {
                    if (reader.TokenType != JsonToken.PropertyName) continue;
                    var p = reader.Value?.ToString();
                    if (!reader.Read()) break;
                    if (p == "Name") name = reader.Value?.ToString();
                    else if (p == "Signature") sig = reader.Value?.ToString();
                    else if (p == "Address") hasAddr = TryReadUlongToken(reader, out addr);
                }
                if (hasAddr && !string.IsNullOrEmpty(name))
                {
                    data.ScriptMetadatas.Add(new ScriptMetadata
                    {
                        Address = addr,
                        Name = name,
                        Signature = sig
                    });
                }
            }
        }

        private static bool TryReadUlongToken(JsonTextReader reader, out ulong value)
        {
            value = 0;
            try
            {
                switch (reader.TokenType)
                {
                    case JsonToken.Integer:
                        if (reader.Value is long l)
                        {
                            value = unchecked((ulong)l);
                            return true;
                        }
                        if (reader.Value is int i)
                        {
                            value = unchecked((ulong)i);
                            return true;
                        }
                        if (reader.Value is ulong ul)
                        {
                            value = ul;
                            return true;
                        }
                        // BigInteger or other
                        return ulong.TryParse(reader.Value?.ToString(), out value);
                    case JsonToken.Float:
                        // may lose precision; still better than skip
                        try
                        {
                            value = Convert.ToUInt64(reader.Value);
                            return true;
                        }
                        catch { return false; }
                    case JsonToken.String:
                        return ulong.TryParse(reader.Value?.ToString(), out value);
                    default:
                        return ulong.TryParse(reader.Value?.ToString(), out value);
                }
            }
            catch
            {
                return false;
            }
        }

        /// <summary>
        /// Merge reference ScriptString (path strings) into generated script.json.
        /// ScriptMetadataMethod is large (700k+) — merged only when reference has more than local scan.
        /// Uses streaming rewrite to avoid deserializing the full ScriptMethod array twice.
        /// </summary>
        public static (int strings, int metaMethods, int metas) MergeScriptJsonSections(
            ReferenceDumpData data,
            string scriptJsonPath)
        {
            if (data == null || string.IsNullOrEmpty(scriptJsonPath) || !File.Exists(scriptJsonPath))
                return (0, 0, 0);

            if (data.ScriptStrings.Count == 0 && data.ScriptMetadataMethods.Count == 0)
                return (0, 0, 0);

            // Lightweight: only replace ScriptString / ScriptMetadataMethod arrays via JObject load
            // of generated file. Generated script is large but already in memory after WriteScript.
            JObject root;
            try
            {
                using var sr = new StreamReader(scriptJsonPath);
                using var reader = new JsonTextReader(sr);
                root = JObject.Load(reader);
            }
            catch
            {
                return (0, 0, 0);
            }

            var stringAdded = 0;
            if (data.ScriptStrings.Count > 0)
            {
                var localCount = (root["ScriptString"] as JArray)?.Count ?? 0;
                if (localCount < data.ScriptStrings.Count)
                {
                    var arr = new JArray();
                    foreach (var s in data.ScriptStrings)
                    {
                        arr.Add(new JObject
                        {
                            ["Address"] = s.Address,
                            ["Value"] = s.Value
                        });
                    }
                    root["ScriptString"] = arr;
                    stringAdded = data.ScriptStrings.Count;
                }
            }

            var mmAdded = 0;
            if (data.ScriptMetadataMethods.Count > 0)
            {
                var localCount = (root["ScriptMetadataMethod"] as JArray)?.Count ?? 0;
                // Only replace when reference is substantially larger (memory dump has full table)
                if (localCount < data.ScriptMetadataMethods.Count / 2)
                {
                    var arr = new JArray();
                    foreach (var m in data.ScriptMetadataMethods)
                    {
                        arr.Add(new JObject
                        {
                            ["Address"] = m.Address,
                            ["Name"] = m.Name,
                            ["MethodAddress"] = m.MethodAddress
                        });
                    }
                    root["ScriptMetadataMethod"] = arr;
                    mmAdded = data.ScriptMetadataMethods.Count;
                }
            }

            var metaAdded = 0;
            if (data.ScriptMetadatas.Count > 0)
            {
                var local = root["ScriptMetadata"] as JArray ?? new JArray();
                var existing = new HashSet<ulong>();
                foreach (var t in local)
                {
                    if (TryReadUlongTokenValue(t["Address"], out var a))
                        existing.Add(a);
                }
                foreach (var m in data.ScriptMetadatas)
                {
                    if (!existing.Add(m.Address)) continue;
                    local.Add(new JObject
                    {
                        ["Address"] = m.Address,
                        ["Name"] = m.Name,
                        ["Signature"] = m.Signature
                    });
                    metaAdded++;
                }
                root["ScriptMetadata"] = local;
            }

            using (var sw = new StreamWriter(scriptJsonPath, false, new UTF8Encoding(false)))
            using (var writer = new JsonTextWriter(sw) { Formatting = Formatting.Indented })
            {
                root.WriteTo(writer);
            }

            return (stringAdded, mmAdded, metaAdded);
        }

        private static bool TryReadUlongTokenValue(JToken tok, out ulong value)
        {
            value = 0;
            if (tok == null || tok.Type == JTokenType.Null) return false;
            try
            {
                if (tok.Type == JTokenType.Integer)
                {
                    value = tok.Value<ulong>();
                    return true;
                }
                return ulong.TryParse(tok.ToString(), out value);
            }
            catch
            {
                try
                {
                    value = unchecked((ulong)tok.Value<long>());
                    return true;
                }
                catch { return false; }
            }
        }

        private static bool IsValidStringLiteral(string value)
        {
            if (string.IsNullOrWhiteSpace(value))
                return false;

            for (var i = 0; i < value.Length; i++)
            {
                var c = value[i];
                if (c == '\0') 
                    return false;
                if (char.IsControl(c) && c != '\r' && c != '\n' && c != '\t')
                    return false;
                if (c >= 0xD800)
                    return false;
            }
            return true;
        }

        /// <summary>
        /// Enrich stringliteral.json entries with Address when value matches reference ScriptString.
        /// </summary>
        public static int EnrichStringLiteralAddresses(ReferenceDumpData data, Metadata metadata, Il2Cpp il2Cpp, string outputDir)
        {
            if (metadata?.stringLiterals == null)
                return 0;
            if (!outputDir.EndsWith(Path.DirectorySeparatorChar) && !outputDir.EndsWith(Path.AltDirectorySeparatorChar))
                outputDir += Path.DirectorySeparatorChar;

            // 1. Load newly generated script.json strings
            var newStrValToAddr = new Dictionary<string, ulong>(StringComparer.Ordinal);
            var newScriptJsonPath = Path.Combine(outputDir, "script.json");
            if (File.Exists(newScriptJsonPath))
            {
                try
                {
                    var newScriptData = ReferenceDumpImporter.Load(outputDir, new ReferenceDumpImporter.LoadOptions { UseCache = false });
                    if (newScriptData?.ScriptStrings != null)
                    {
                        foreach (var s in newScriptData.ScriptStrings)
                        {
                            if (s.Value != null && s.Address != 0 && !newStrValToAddr.ContainsKey(s.Value))
                            {
                                newStrValToAddr[s.Value] = s.Address;
                            }
                        }
                    }
                }
                catch { }
            }

            // 2. Load reference dump strings
            var valueToAddr = new Dictionary<string, ulong>(StringComparer.Ordinal);
            if (data?.ScriptStrings != null)
            {
                foreach (var s in data.ScriptStrings)
                {
                    if (s.Value == null || valueToAddr.ContainsKey(s.Value)) continue;
                    valueToAddr[s.Value] = s.Address;
                }
            }

            var list = new List<object>();
            var hit = 0;
            for (uint i = 0; i < metadata.stringLiterals.Length; i++)
            {
                string value;
                try { value = metadata.GetStringLiteralFromIndex(i); }
                catch { continue; }

                if (!IsValidStringLiteral(value))
                    continue;

                var addrStr = "0x0";
                if (newStrValToAddr.TryGetValue(value, out var newAddr) && newAddr != 0)
                {
                    addrStr = $"0x{newAddr:X}";
                    hit++;
                }

                if (addrStr == "0x0" && valueToAddr.TryGetValue(value, out var oldAddr) && oldAddr != 0)
                {
                    addrStr = $"0x{oldAddr:X}";
                    hit++;
                }

                if (addrStr != "0x0" && addrStr != "0")
                {
                    list.Add(new { value, address = addrStr });
                }
            }

            File.WriteAllText(
                outputDir + "stringliteral.json",
                JsonConvert.SerializeObject(list, Formatting.Indented),
                new UTF8Encoding(false));
            return hit;
        }

        public static void WriteStringLiterals(Metadata metadata, Il2Cpp il2Cpp, string outputDir)
        {
            if (metadata?.stringLiterals == null || metadata.stringLiterals.Length == 0)
                return;
            if (!outputDir.EndsWith(Path.DirectorySeparatorChar) && !outputDir.EndsWith(Path.AltDirectorySeparatorChar))
                outputDir += Path.DirectorySeparatorChar;

            // Load newly generated script.json strings
            var newStrValToAddr = new Dictionary<string, ulong>(StringComparer.Ordinal);
            var newScriptJsonPath = Path.Combine(outputDir, "script.json");
            if (File.Exists(newScriptJsonPath))
            {
                try
                {
                    var newScriptData = ReferenceDumpImporter.Load(outputDir, new ReferenceDumpImporter.LoadOptions { UseCache = false });
                    if (newScriptData?.ScriptStrings != null)
                    {
                        foreach (var s in newScriptData.ScriptStrings)
                        {
                            if (s.Value != null && s.Address != 0 && !newStrValToAddr.ContainsKey(s.Value))
                            {
                                newStrValToAddr[s.Value] = s.Address;
                            }
                        }
                    }
                }
                catch { }
            }

            var list = new List<object>();
            for (uint i = 0; i < metadata.stringLiterals.Length; i++)
            {
                string value;
                try { value = metadata.GetStringLiteralFromIndex(i); }
                catch { continue; }

                if (!IsValidStringLiteral(value))
                    continue;

                var addrStr = "0x0";
                if (newStrValToAddr.TryGetValue(value, out var addr) && addr != 0)
                {
                    addrStr = $"0x{addr:X}";
                }

                if (addrStr != "0x0" && addrStr != "0")
                {
                    list.Add(new { value, address = addrStr });
                }
            }

            File.WriteAllText(
                outputDir + "stringliteral.json",
                JsonConvert.SerializeObject(list, Formatting.Indented),
                new UTF8Encoding(false));
        }

        private static Il2CppType MakePrimitiveSyntheticType(Il2CppTypeEnum typeEnum, Il2Cpp il2Cpp)
        {
            var t = new Il2CppType
            {
                datapoint = 0,
                bits = ((uint)typeEnum) << 16
            };
            t.Init(il2Cpp.Version);
            return t;
        }

        private static Il2CppType ResolveTypeFromName(
            string typeName, Metadata metadata, Il2Cpp il2Cpp, Dictionary<string, int> typeMap,
            Il2CppMethodDefinition methodContext = null, Il2CppTypeDefinition typeContext = null)
        {
            if (string.IsNullOrEmpty(typeName))
                return null;

            if (methodContext != null && methodContext.genericContainerIndex >= 0 &&
                methodContext.genericContainerIndex < metadata.genericContainers.Length)
            {
                var gc = metadata.genericContainers[methodContext.genericContainerIndex];
                for (var i = 0; i < gc.type_argc; i++)
                {
                    var gpIndex = gc.genericParameterStart + i;
                    if (gpIndex >= 0 && gpIndex < metadata.genericParameters.Length)
                    {
                        var gp = metadata.genericParameters[gpIndex];
                        var gpName = metadata.GetStringFromIndex(gp.nameIndex);
                        if (gpName == typeName)
                        {
                            var t = new Il2CppType
                            {
                                datapoint = (ulong)gpIndex,
                                bits = ((uint)Il2CppTypeEnum.IL2CPP_TYPE_MVAR) << 16
                            };
                            t.Init(il2Cpp.Version);
                            return t;
                        }
                    }
                }
            }

            if (typeContext != null && typeContext.genericContainerIndex >= 0 &&
                typeContext.genericContainerIndex < metadata.genericContainers.Length)
            {
                var gc = metadata.genericContainers[typeContext.genericContainerIndex];
                for (var i = 0; i < gc.type_argc; i++)
                {
                    var gpIndex = gc.genericParameterStart + i;
                    if (gpIndex >= 0 && gpIndex < metadata.genericParameters.Length)
                    {
                        var gp = metadata.genericParameters[gpIndex];
                        var gpName = metadata.GetStringFromIndex(gp.nameIndex);
                        if (gpName == typeName)
                        {
                            var t = new Il2CppType
                            {
                                datapoint = (ulong)gpIndex,
                                bits = ((uint)Il2CppTypeEnum.IL2CPP_TYPE_VAR) << 16
                            };
                            t.Init(il2Cpp.Version);
                            return t;
                        }
                    }
                }
            }

            if (typeName.EndsWith("[]", StringComparison.Ordinal))
            {
                var elemName = typeName.Substring(0, typeName.Length - 2);
                var elemType = ResolveTypeFromName(elemName, metadata, il2Cpp, typeMap, methodContext, typeContext);
                if (elemType != null)
                {
                    var arrType = new Il2CppType
                    {
                        datapoint = elemType.datapoint,
                        bits = ((uint)Il2CppTypeEnum.IL2CPP_TYPE_SZARRAY) << 16
                    };
                    arrType.Init(il2Cpp.Version);
                    return arrType;
                }
            }

            var primitiveEnum = typeName switch
            {
                "int" or "Int32" => Il2CppTypeEnum.IL2CPP_TYPE_I4,
                "uint" or "UInt32" => Il2CppTypeEnum.IL2CPP_TYPE_U4,
                "short" or "Int16" => Il2CppTypeEnum.IL2CPP_TYPE_I2,
                "ushort" or "UInt16" => Il2CppTypeEnum.IL2CPP_TYPE_U2,
                "long" or "Int64" => Il2CppTypeEnum.IL2CPP_TYPE_I8,
                "ulong" or "UInt64" => Il2CppTypeEnum.IL2CPP_TYPE_U8,
                "byte" or "Byte" => Il2CppTypeEnum.IL2CPP_TYPE_U1,
                "sbyte" or "SByte" => Il2CppTypeEnum.IL2CPP_TYPE_I1,
                "bool" or "Boolean" => Il2CppTypeEnum.IL2CPP_TYPE_BOOLEAN,
                "char" or "Char" => Il2CppTypeEnum.IL2CPP_TYPE_CHAR,
                "float" or "Single" => Il2CppTypeEnum.IL2CPP_TYPE_R4,
                "double" or "Double" => Il2CppTypeEnum.IL2CPP_TYPE_R8,
                "string" or "String" => Il2CppTypeEnum.IL2CPP_TYPE_STRING,
                "object" or "Object" => Il2CppTypeEnum.IL2CPP_TYPE_OBJECT,
                "void" or "Void" => Il2CppTypeEnum.IL2CPP_TYPE_VOID,
                _ => Il2CppTypeEnum.IL2CPP_TYPE_END
            };

            if (primitiveEnum != Il2CppTypeEnum.IL2CPP_TYPE_END)
            {
                return MakePrimitiveSyntheticType(primitiveEnum, il2Cpp);
            }

            if (typeMap.TryGetValue(typeName, out var idx))
            {
                var td = metadata.typeDefs[idx];
                var byval = td.byvalTypeIndex;
                if (byval >= 0 && byval < il2Cpp.types.Length)
                {
                    return il2Cpp.CloneIl2CppType(il2Cpp.types[byval]);
                }
            }

            return null;
        }

        public static Dictionary<string, int> BuildTypeMap(Metadata metadata)
        {
            var typeMap = new Dictionary<string, int>(StringComparer.Ordinal);
            if (metadata?.typeDefs == null)
                return typeMap;
            for (var i = 0; i < metadata.typeDefs.Length; i++)
            {
                var td = metadata.typeDefs[i];
                var name = metadata.GetStringFromIndex(td.nameIndex);
                if (string.IsNullOrEmpty(name)) continue;

                var nestedName = name;
                var curr = td;
                while (curr.declaringTypeIndex >= 0 && curr.declaringTypeIndex < metadata.typeDefs.Length)
                {
                    curr = metadata.typeDefs[curr.declaringTypeIndex];
                    nestedName = metadata.GetStringFromIndex(curr.nameIndex) + "." + nestedName;
                }

                var ns = metadata.GetStringFromIndex(td.namespaceIndex);
                var fullName = string.IsNullOrEmpty(ns) ? nestedName : $"{ns}.{nestedName}";

                typeMap[fullName] = i;
                typeMap[nestedName] = i;
                typeMap[name] = i;
            }
            return typeMap;
        }

        /// <summary>
        /// Overlay reference field offsets and types onto synthetic layout arrays.
        /// </summary>
        public static int ApplyFieldOffsets(ReferenceDumpData data, Metadata metadata, int[][] syntheticFieldOffsets, Il2Cpp il2Cpp, Dictionary<string, int> typeMap)
        {
            if (data == null || metadata?.typeDefs == null || syntheticFieldOffsets == null || il2Cpp == null || typeMap == null)
                return 0;

            data.NewToOldTypeIndices.Clear();
            foreach (var pair in data.TypeIndexToFullName)
            {
                if (typeMap.TryGetValue(pair.Value, out var newIdx))
                {
                    data.NewToOldTypeIndices[newIdx] = pair.Key;
                }
            }

            var applied = 0;
            foreach (var kv in data.FieldOffsets)
            {
                var oldTypeDefIndex = kv.Key;
                if (!data.TypeIndexToFullName.TryGetValue(oldTypeDefIndex, out var fullName) ||
                    !typeMap.TryGetValue(fullName, out var typeDefIndex))
                {
                    continue;
                }

                if (typeDefIndex < 0 || typeDefIndex >= metadata.typeDefs.Length)
                    continue;
                if (typeDefIndex >= syntheticFieldOffsets.Length)
                    continue;

                var td = metadata.typeDefs[typeDefIndex];
                var arr = syntheticFieldOffsets[typeDefIndex];
                if (arr == null || arr.Length != td.field_count)
                {
                    arr = new int[td.field_count];
                    for (var i = 0; i < arr.Length; i++)
                        arr[i] = -1;
                    syntheticFieldOffsets[typeDefIndex] = arr;
                }

                for (var fi = 0; fi < td.field_count; fi++)
                {
                    var fd = metadata.fieldDefs[td.fieldStart + fi];
                    var fname = metadata.GetStringFromIndex(fd.nameIndex);
                    if (kv.Value.TryGetValue(fname, out var off))
                    {
                        arr[fi] = off;
                        applied++;
                    }

                    if (data.FieldTypes.TryGetValue(oldTypeDefIndex, out var ft) &&
                        ft.TryGetValue(fname, out var typeName))
                    {
                        var resolvedType = ResolveTypeFromName(typeName, metadata, il2Cpp, typeMap, typeContext: td);
                        if (resolvedType != null)
                        {
                            var isStatic = false;
                            if (data.StaticFields.TryGetValue(oldTypeDefIndex, out var sf) &&
                                sf.Contains(fname))
                            {
                                isStatic = true;
                            }

                            var access = 0x0001; // private
                            if (isStatic)
                            {
                                access |= 0x0010; // static
                            }
                            resolvedType.bits = (resolvedType.bits & 0xFFFF0000u) | (uint)access;
                            resolvedType.Init(il2Cpp.Version);

                            if (fd.typeIndex >= 0 && fd.typeIndex < il2Cpp.types.Length)
                            {
                                il2Cpp.types[fd.typeIndex] = resolvedType;
                            }
                        }
                    }
                }
            }
            return applied;
        }

        /// <summary>
        /// Overlay method RVAs from reference into per-image method pointer tables.
        /// Pointers stored as absolute VA = ImageBase + RVA when ImageBase known, else RVA as VA
        /// (Mach-O vmaddr 0 → RVA == VA).
        /// </summary>
        public static int ApplyMethodRvas(ReferenceDumpData data, Metadata metadata, Il2Cpp il2Cpp, Dictionary<string, int> typeMap)
        {
            if (data == null || metadata == null || il2Cpp == null || typeMap == null)
                return 0;
            if (il2Cpp.codeGenModuleMethodPointers == null)
                return 0;

            var applied = 0;
            var newToOld = new Dictionary<int, int>();
            foreach (var pair in data.TypeIndexToFullName)
            {
                if (typeMap.TryGetValue(pair.Value, out var newIdx))
                {
                    newToOld[newIdx] = pair.Key;
                }
            }

            // Build typeDef → image name
            var typeToImage = new string[metadata.typeDefs.Length];
            foreach (var imageDef in metadata.imageDefs)
            {
                var imageName = metadata.GetStringFromIndex(imageDef.nameIndex);
                var end = imageDef.typeStart + imageDef.typeCount;
                for (var t = imageDef.typeStart; t < end && t < typeToImage.Length; t++)
                    typeToImage[t] = imageName;
            }

            // namespace+name for script.json matching
            for (var ti = 0; ti < metadata.typeDefs.Length; ti++)
            {
                var td = metadata.typeDefs[ti];
                var imageName = typeToImage[ti];
                if (string.IsNullOrEmpty(imageName))
                    continue;
                if (!il2Cpp.codeGenModuleMethodPointers.TryGetValue(imageName, out var ptrs) || ptrs == null)
                    continue;

                var typeName = metadata.GetStringFromIndex(td.nameIndex);
                var ns = td.declaringTypeIndex >= 0
                    ? null
                    : metadata.GetStringFromIndex(td.namespaceIndex);
                // Prefer full namespace from metadata
                if (td.namespaceIndex >= 0)
                    ns = metadata.GetStringFromIndex(td.namespaceIndex);

                var oldIdx = -1;
                newToOld.TryGetValue(ti, out oldIdx);

                for (var mi = 0; mi < td.method_count; mi++)
                {
                    var md = metadata.methodDefs[td.methodStart + mi];
                    var mname = metadata.GetStringFromIndex(md.nameIndex);

                    if (oldIdx >= 0 && data.MethodSignatures.TryGetValue(oldIdx, out var ms) && ms.TryGetValue(mname, out var sigs))
                    {
                        var sig = sigs.FirstOrDefault(x => x.ParameterTypes.Count == md.parameterCount);
                        if (sig != null)
                        {
                            var resolvedRet = ResolveTypeFromName(sig.ReturnType, metadata, il2Cpp, typeMap, methodContext: md, typeContext: td);
                            if (resolvedRet != null && md.returnType >= 0 && md.returnType < il2Cpp.types.Length)
                            {
                                il2Cpp.types[md.returnType] = resolvedRet;
                            }

                            for (var pi = 0; pi < md.parameterCount; pi++)
                            {
                                if (md.parameterStart + pi >= 0 && md.parameterStart + pi < metadata.parameterDefs.Length)
                                {
                                    var paramDef = metadata.parameterDefs[md.parameterStart + pi];
                                    var refParamType = sig.ParameterTypes[pi];
                                    var resolvedParam = ResolveTypeFromName(refParamType, metadata, il2Cpp, typeMap, methodContext: md, typeContext: td);
                                    if (resolvedParam != null && paramDef.typeIndex >= 0 && paramDef.typeIndex < il2Cpp.types.Length)
                                    {
                                        il2Cpp.types[paramDef.typeIndex] = resolvedParam;
                                    }
                                }
                            }
                        }
                    }

                    var tokenIndex = (int)(md.token & 0x00FFFFFF) - 1;
                    if (tokenIndex < 0 || tokenIndex >= ptrs.Length)
                        continue;

                    ulong rva = 0;
                    if (!string.IsNullOrEmpty(ns))
                    {
                        var key = ns + "." + typeName + "$$" + mname;
                        data.MethodRvaByScriptName.TryGetValue(key, out rva);
                        if (rva == 0)
                        {
                            key = ns + "." + typeName.Replace('/', '+') + "$$" + mname;
                            data.MethodRvaByScriptName.TryGetValue(key, out rva);
                        }
                    }
                    if (rva == 0)
                        data.MethodRvaByScriptName.TryGetValue(typeName + "$$" + mname, out rva);

                    if (rva == 0 && oldIdx >= 0 &&
                        data.MethodRvaByTypeMethod.TryGetValue(oldIdx, out var byMethod) &&
                        byMethod.TryGetValue(mname, out var rva2))
                        rva = rva2;

                    if (rva == 0)
                        continue;

                    ptrs[tokenIndex] = rva;
                    applied++;
                }
            }

            return applied;
        }

        public static bool TryGetFieldType(ReferenceDumpData data, int typeDefIndex, string fieldName, out string typeName)
        {
            typeName = null;
            if (data?.FieldTypes == null || string.IsNullOrEmpty(fieldName))
                return false;
            var lookupIndex = typeDefIndex;
            if (data.NewToOldTypeIndices.TryGetValue(typeDefIndex, out var oldIdx))
            {
                lookupIndex = oldIdx;
            }
            if (!data.FieldTypes.TryGetValue(lookupIndex, out var map))
                return false;
            return map.TryGetValue(fieldName, out typeName) && !string.IsNullOrEmpty(typeName);
        }

        public static bool TryGetFieldOffset(ReferenceDumpData data, int typeDefIndex, string fieldName, out int offset)
        {
            offset = -1;
            if (data?.FieldOffsets == null || string.IsNullOrEmpty(fieldName))
                return false;
            var lookupIndex = typeDefIndex;
            if (data.NewToOldTypeIndices.TryGetValue(typeDefIndex, out var oldIdx))
            {
                lookupIndex = oldIdx;
            }
            if (!data.FieldOffsets.TryGetValue(lookupIndex, out var map))
                return false;
            return map.TryGetValue(fieldName, out offset);
        }
    }
}
