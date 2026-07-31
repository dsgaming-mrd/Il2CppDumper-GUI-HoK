using System;
using System.Collections.Generic;
using System.Linq;

namespace Il2CppDumper
{
    /// <summary>
    /// Fill field typeIndex slots that stay OBJECT under synthetic registration by
    /// copying resolved Il2CppType from property getters/setters and related methods.
    /// Also recovers ref types by field-name ↔ typeDef-name heuristics.
    /// List/array GENERICINST is missing from disk — display names are recovered in the decompiler.
    /// </summary>
    public static class SyntheticTypeEnricher
    {
        public static int Enrich(Il2Cpp il2Cpp, Metadata metadata)
        {
            if (il2Cpp?.types == null || metadata?.typeDefs == null)
                return 0;

            var filled = 0;
            var index = TypeNameIndex.Build(metadata);

            // byvalTypeIndex slots must never be overwritten — they define the type itself.
            // Field typeIndex often collides with a byval under synthetic init; those fields are
            // fixed at display-time in the decompiler instead.
            var byvalSlots = new HashSet<int>();
            foreach (var tdef in metadata.typeDefs)
            {
                if (tdef.byvalTypeIndex >= 0)
                    byvalSlots.Add(tdef.byvalTypeIndex);
            }

            // Name heuristics for dedicated (non-byval) field type slots.
            // List/array GENERICINST missing — decompiler prints List&lt;T&gt; / T[] display names.
            for (var ti = 0; ti < metadata.typeDefs.Length; ti++)
            {
                var td = metadata.typeDefs[ti];
                if (td.IsEnum)
                    continue;
                var fEnd = td.fieldStart + td.field_count;
                for (var fi = td.fieldStart; fi < fEnd; fi++)
                {
                    if (fi < 0 || fi >= metadata.fieldDefs.Length)
                        continue;
                    var fd = metadata.fieldDefs[fi];
                    if (fd.typeIndex < 0 || fd.typeIndex >= il2Cpp.types.Length)
                        continue;

                    // Do not corrupt typeDef.byvalTypeIndex entries
                    if (byvalSlots.Contains(fd.typeIndex))
                        continue;

                    var fieldName = metadata.GetStringFromIndex(fd.nameIndex);
                    if (string.IsNullOrEmpty(fieldName) || fieldName.Length < 2)
                        continue;

                    if (LooksLikeCollectionField(fieldName))
                        continue;

                    var typeDefIdx = index.ResolveTypeDef(fieldName);
                    if (typeDefIdx < 0)
                        continue;

                    var candidateName = metadata.GetStringFromIndex(metadata.typeDefs[typeDefIdx].nameIndex);
                    var candidateScore = TypeNameMatchScore(fieldName, candidateName);
                    if (candidateScore < 75)
                        continue;

                    var curScore = CurrentTypeNameScore(il2Cpp, metadata, fd.typeIndex, fieldName);
                    if (!IsUnresolved(il2Cpp, fd.typeIndex) && curScore >= candidateScore)
                        continue;

                    var byval = metadata.typeDefs[typeDefIdx].byvalTypeIndex;
                    if (byval < 0 || byval >= il2Cpp.types.Length || IsUnresolved(il2Cpp, byval))
                        continue;

                    ApplyType(il2Cpp, fd.typeIndex, byval, fieldName);
                    filled++;
                }
            }

            return filled;
        }

        private static int CurrentTypeNameScore(Il2Cpp il2Cpp, Metadata metadata, int typeIndex, string fieldName)
        {
            if (IsUnresolved(il2Cpp, typeIndex))
                return 0;
            var t = il2Cpp.types[typeIndex];
            if (t == null) return 0;
            if (t.type is not (Il2CppTypeEnum.IL2CPP_TYPE_CLASS or Il2CppTypeEnum.IL2CPP_TYPE_VALUETYPE))
                return 0;
            var idx = (int)t.data.klassIndex;
            if (idx < 0 || idx >= metadata.typeDefs.Length)
                return 0;
            var typeName = metadata.GetStringFromIndex(metadata.typeDefs[idx].nameIndex);
            return TypeNameMatchScore(fieldName, typeName);
        }

        private static void ApplyType(Il2Cpp il2Cpp, int fieldTypeIndex, int sourceTypeIndex, string fieldName)
        {
            var cloned = il2Cpp.CloneIl2CppType(il2Cpp.types[sourceTypeIndex]);
            var vis = GuessFieldVisibility(fieldName);
            cloned.bits = (cloned.bits & 0xFFFF0000u) | vis;
            cloned.Init(il2Cpp.Version);
            il2Cpp.types[fieldTypeIndex] = cloned;
        }

        /// <summary>
        /// Property/method type must either name-match the field strongly, or at least
        /// share a meaningful token — blocks resHeroCfgInfo → ResOfflineHeroConfig style misses.
        /// </summary>
        private static bool SourceTypeAgreesWithField(Il2Cpp il2Cpp, Metadata metadata, int typeIndex, string fieldName)
        {
            if (typeIndex < 0 || typeIndex >= il2Cpp.types.Length)
                return false;
            var t = il2Cpp.types[typeIndex];
            if (t == null) return false;

            // Interfaces / classes / valuetypes with klassIndex
            if (t.type is Il2CppTypeEnum.IL2CPP_TYPE_CLASS or Il2CppTypeEnum.IL2CPP_TYPE_VALUETYPE)
            {
                var idx = (int)t.data.klassIndex;
                if (idx >= 0 && idx < metadata.typeDefs.Length)
                {
                    var typeName = metadata.GetStringFromIndex(metadata.typeDefs[idx].nameIndex);
                    if (TypeNameMatchScore(fieldName, typeName) >= 50)
                        return true;
                    // Shared substantial token (Hero, Skill, Anim, …)
                    var fCore = NormalizeCore(fieldName);
                    var tCore = NormalizeCore(typeName);
                    if (fCore.Length >= 4 && tCore.Length >= 4)
                    {
                        if (fCore.IndexOf(tCore, StringComparison.OrdinalIgnoreCase) >= 0 ||
                            tCore.IndexOf(fCore, StringComparison.OrdinalIgnoreCase) >= 0)
                            return true;
                    }
                    // Interface often I + field role: IObjLinkerWrapper vs ActorControl — allow if prop path scored high
                    if (typeName.StartsWith("I", StringComparison.Ordinal) && typeName.Length > 2 && char.IsUpper(typeName[1]))
                        return true;
                    return false;
                }
            }
            // primitives / generics already filtered elsewhere
            return true;
        }

        /// <summary>
        /// Display-only recovery for dump.cs when type slot is still object
        /// (List/array GENERICINST, or name heuristics).
        /// </summary>
        public static string ResolveDisplayTypeName(TypeNameIndex index, string fieldName, Func<int, string> byvalTypeName)
        {
            if (string.IsNullOrEmpty(fieldName) || index == null)
                return null;

            if (TryCollectionDisplay(index, fieldName, byvalTypeName, out var coll))
                return coll;

            var typeDefIdx = index.ResolveTypeDef(fieldName);
            if (typeDefIdx >= 0)
            {
                var tn = byvalTypeName(typeDefIdx);
                if (!IsObjectName(tn))
                    return tn;
            }

            return null;
        }

        private static bool TryCollectionDisplay(
            TypeNameIndex index,
            string fieldName,
            Func<int, string> byvalTypeName,
            out string display)
        {
            display = null;
            if (!LooksLikeCollectionField(fieldName))
                return false;

            var bare = StripFieldPrefix(fieldName);
            var elemCandidates = new List<string>();

            void AddElem(string s)
            {
                if (string.IsNullOrEmpty(s) || s.Length < 2) return;
                elemCandidates.Add(s);
                if (char.IsLower(s[0]))
                    elemCandidates.Add(char.ToUpperInvariant(s[0]) + s.Substring(1));
            }

            if (bare.EndsWith("List", StringComparison.OrdinalIgnoreCase) && bare.Length > 4)
                AddElem(bare.Substring(0, bare.Length - 4));
            else if (bare.EndsWith("Array", StringComparison.OrdinalIgnoreCase) && bare.Length > 5)
                AddElem(bare.Substring(0, bare.Length - 5));
            else if (bare.EndsWith("Components", StringComparison.Ordinal) && bare.Length > 10)
            {
                AddElem(bare.Substring(0, bare.Length - 1)); // Component
                AddElem(bare.Substring(0, bare.Length - 10) + "Component");
            }
            else if (bare.EndsWith("Items", StringComparison.Ordinal) && bare.Length > 5)
                AddElem(bare.Substring(0, bare.Length - 5));
            else if (bare.EndsWith("s", StringComparison.Ordinal) && bare.Length > 3 &&
                     char.IsLower(bare[bare.Length - 2]))
                AddElem(bare.Substring(0, bare.Length - 1));

            AddElem(bare);

            foreach (var c in elemCandidates.Distinct(StringComparer.Ordinal))
            {
                var idx = index.ResolveTypeDef(c);
                if (idx < 0)
                {
                    // exact name only for simple element tokens
                    idx = index.FindExact(c);
                    if (idx < 0 && char.IsLower(c[0]))
                        idx = index.FindExact(char.ToUpperInvariant(c[0]) + c.Substring(1));
                }
                if (idx < 0)
                    continue;

                var tn = byvalTypeName(idx);
                if (IsObjectName(tn))
                    continue;

                if (bare.EndsWith("Array", StringComparison.OrdinalIgnoreCase) ||
                    (bare.EndsWith("s", StringComparison.Ordinal) &&
                     !bare.EndsWith("List", StringComparison.OrdinalIgnoreCase) &&
                     !bare.EndsWith("Components", StringComparison.Ordinal) &&
                     !bare.EndsWith("Items", StringComparison.Ordinal)))
                    display = tn + "[]";
                else
                    display = "List<" + tn + ">";
                return true;
            }

            if (bare.EndsWith("Array", StringComparison.OrdinalIgnoreCase))
                display = "object[]";
            else
                display = "List<object>";
            return true;
        }

        /// <summary>Precomputed typeDef name indexes — O(types) build, O(candidates)/field lookup.</summary>
        public sealed class TypeNameIndex
        {
            private readonly Metadata metadata;
            private readonly Dictionary<string, int> byExact;
            // Full-name camel suffixes long enough to be unique-ish (len>=6)
            private readonly Dictionary<string, int> bySuffix;
            // Camel prefixes → candidate typeDef indices (EnemyIcon → EnemyIconOutOfVisionComponent)
            private readonly Dictionary<string, List<int>> byPrefix;

            private TypeNameIndex(
                Metadata metadata,
                Dictionary<string, int> byExact,
                Dictionary<string, int> bySuffix,
                Dictionary<string, List<int>> byPrefix)
            {
                this.metadata = metadata;
                this.byExact = byExact;
                this.bySuffix = bySuffix;
                this.byPrefix = byPrefix;
            }

            public static TypeNameIndex Build(Metadata metadata)
            {
                var byExact = new Dictionary<string, int>(StringComparer.Ordinal);
                var bySuffix = new Dictionary<string, int>(StringComparer.OrdinalIgnoreCase);
                var byPrefix = new Dictionary<string, List<int>>(StringComparer.OrdinalIgnoreCase);

                for (var i = 0; i < metadata.typeDefs.Length; i++)
                {
                    var n = metadata.GetStringFromIndex(metadata.typeDefs[i].nameIndex);
                    if (string.IsNullOrEmpty(n))
                        continue;

                    if (!byExact.ContainsKey(n))
                        byExact[n] = i;

                    // Only register long suffixes to avoid IconComponent collisions
                    foreach (var suf in CamelSuffixes(n))
                    {
                        if (suf.Length < 6) continue;
                        if (!bySuffix.ContainsKey(suf))
                            bySuffix[suf] = i;
                    }

                    foreach (var pre in CamelPrefixes(n))
                    {
                        if (pre.Length < 5) continue;
                        if (!byPrefix.TryGetValue(pre, out var list))
                        {
                            list = new List<int>(4);
                            byPrefix[pre] = list;
                        }
                        // No small cap — early types would starve later correct matches
                        // (e.g. Equip* fills 12 slots before EquipLinkerComponent).
                        list.Add(i);
                    }
                }

                return new TypeNameIndex(metadata, byExact, bySuffix, byPrefix);
            }

            public int FindExact(string name)
            {
                if (string.IsNullOrEmpty(name)) return -1;
                return byExact.TryGetValue(name, out var i) ? i : -1;
            }

            public int ResolveTypeDef(string fieldName)
            {
                if (string.IsNullOrEmpty(fieldName))
                    return -1;

                var bare = StripFieldPrefix(fieldName);
                var pascal = ToPascal(bare);
                var bestIdx = -1;
                var bestScore = 0;

                void Consider(int idx)
                {
                    if (idx < 0 || idx >= metadata.typeDefs.Length) return;
                    var typeName = metadata.GetStringFromIndex(metadata.typeDefs[idx].nameIndex);
                    var score = TypeNameMatchScore(fieldName, typeName);
                    // Tie-break: prefer names that start with field core / equal length closer to field
                    if (score > bestScore ||
                        (score == bestScore && score > 0 && bestIdx >= 0 &&
                         PreferType(fieldName, typeName,
                             metadata.GetStringFromIndex(metadata.typeDefs[bestIdx].nameIndex))))
                    {
                        bestScore = score;
                        bestIdx = idx;
                    }
                }

                // 1) Exact name hits from guesses (MatHurtEffect → MaterialHurtEffect, etc.)
                foreach (var g in GenerateTypeNameGuesses(fieldName))
                {
                    if (byExact.TryGetValue(g, out var ei))
                        Consider(ei);
                }

                // Exact field name / pascal
                if (byExact.TryGetValue(pascal, out var ex))
                    Consider(ex);
                if (byExact.TryGetValue(bare, out ex))
                    Consider(ex);

                // 2) Suffix candidates (updateFreqController → ActorLinkerUpdateFreqController)
                if (pascal.Length >= 8 && bySuffix.TryGetValue(pascal, out var si))
                    Consider(si);
                if (bare.Length >= 8 && bySuffix.TryGetValue(bare, out si))
                    Consider(si);

                // 3) Prefix candidates (EnemyIcon → EnemyIconOutOfVisionComponent, Anim → AnimPlayComponentBase)
                foreach (var key in PrefixLookupKeys(fieldName))
                {
                    if (!byPrefix.TryGetValue(key, out var list)) continue;
                    foreach (var idx in list)
                        Consider(idx);
                }

                var head = pascal;
                foreach (var suf in new[] { "Component", "Control", "Controller", "Proxy", "Effect" })
                {
                    if (head.EndsWith(suf, StringComparison.Ordinal) && head.Length > suf.Length + 3)
                    {
                        head = head.Substring(0, head.Length - suf.Length);
                        if (byPrefix.TryGetValue(head, out var list))
                        {
                            foreach (var idx in list)
                                Consider(idx);
                        }
                        // Also try head + "Play" common pattern (Anim → AnimPlay…)
                        if (byPrefix.TryGetValue(head + "Play", out list))
                        {
                            foreach (var idx in list)
                                Consider(idx);
                        }
                        break;
                    }
                }

                // Require strong match; exact-name style (>=95) always ok; fuzzy >=75
                return bestScore >= 75 ? bestIdx : -1;
            }

            private static bool PreferType(string fieldName, string candidate, string currentBest)
            {
                // Prefer exact / shorter extension over *Wrapper / Follow* prefixes when scores tie
                var bare = ToPascal(StripFieldPrefix(fieldName));
                var candExact = string.Equals(candidate, bare, StringComparison.OrdinalIgnoreCase);
                var bestExact = string.Equals(currentBest, bare, StringComparison.OrdinalIgnoreCase);
                if (candExact && !bestExact) return true;
                if (!candExact && bestExact) return false;
                // Prefer type starting with field core
                var core = NormalizeCore(fieldName);
                var cStarts = candidate.StartsWith(core, StringComparison.OrdinalIgnoreCase);
                var bStarts = currentBest.StartsWith(core, StringComparison.OrdinalIgnoreCase);
                if (cStarts && !bStarts) return true;
                if (!cStarts && bStarts) return false;
                // Prefer not Wrapper/Proxy/Follow when field doesn't say so
                var fieldWantsWrapper = bare.IndexOf("Wrapper", StringComparison.OrdinalIgnoreCase) >= 0;
                if (!fieldWantsWrapper)
                {
                    var cWrap = candidate.EndsWith("Wrapper", StringComparison.Ordinal);
                    var bWrap = currentBest.EndsWith("Wrapper", StringComparison.Ordinal);
                    if (!cWrap && bWrap) return true;
                    if (cWrap && !bWrap) return false;
                }
                // Prefer closer length to bare name
                return Math.Abs(candidate.Length - bare.Length) < Math.Abs(currentBest.Length - bare.Length);
            }
        }

        private static IEnumerable<string> PrefixLookupKeys(string fieldName)
        {
            var bare = StripFieldPrefix(fieldName);
            var pascal = ToPascal(bare);
            if (pascal.Length >= 5) yield return pascal;
            if (bare.Length >= 5 && !string.Equals(bare, pascal, StringComparison.Ordinal))
                yield return bare;

            foreach (var g in GenerateTypeNameGuesses(fieldName))
            {
                if (g.Length >= 5) yield return g;
                // MaterialHurt → still useful if type is MaterialHurtEffect
                if (g.EndsWith("Effect", StringComparison.Ordinal) && g.Length > 6)
                    yield return g.Substring(0, g.Length - 6);
            }

            // EnemyIcon from EnemyIconComponent
            foreach (var suf in new[] { "Component", "Control", "Controller", "Proxy" })
            {
                if (pascal.EndsWith(suf, StringComparison.Ordinal) && pascal.Length > suf.Length + 3)
                {
                    yield return pascal.Substring(0, pascal.Length - suf.Length);
                    break;
                }
            }
        }

        private static IEnumerable<string> CamelPrefixes(string name)
        {
            if (string.IsNullOrEmpty(name))
                yield break;
            yield return name;
            for (var i = 1; i < name.Length; i++)
            {
                if (char.IsUpper(name[i]))
                    yield return name.Substring(0, i);
            }
        }

        public static int TypeNameMatchScore(string fieldName, string typeName)
        {
            if (string.IsNullOrEmpty(fieldName) || string.IsNullOrEmpty(typeName))
                return 0;

            var bare = StripFieldPrefix(fieldName);
            if (string.Equals(bare, typeName, StringComparison.Ordinal))
                return 100;
            if (string.Equals(bare, typeName, StringComparison.OrdinalIgnoreCase))
                return 95;

            // High-priority HOK/engine aliases (must beat XControl→XComponent = 98)
            if (string.Equals(ToPascal(bare), "ActorControl", StringComparison.Ordinal) &&
                (typeName == "ObjLinkerWrapper" || typeName == "IObjLinkerWrapper"))
                return 99;
            if ((string.Equals(bare, "miniMap", StringComparison.OrdinalIgnoreCase) ||
                 string.Equals(ToPascal(bare), "MiniMap", StringComparison.Ordinal)) &&
                typeName.IndexOf("Minimap", StringComparison.OrdinalIgnoreCase) >= 0 &&
                typeName.EndsWith("Proxy", StringComparison.Ordinal))
                return 99;

            foreach (var g in GenerateTypeNameGuesses(fieldName))
            {
                if (string.Equals(g, typeName, StringComparison.Ordinal))
                    return 98;
                if (string.Equals(g, typeName, StringComparison.OrdinalIgnoreCase))
                    return 96;
            }

            // Prefer *Proxy when field is a short camel name that is a prefix (miniMap ⊂ MinimapSysProxy)
            if (typeName.EndsWith("Proxy", StringComparison.Ordinal) && bare.Length >= 4 &&
                typeName.IndexOf(bare, StringComparison.OrdinalIgnoreCase) >= 0)
            {
                var ratio = (double)bare.Length / (typeName.Length - 5); // ignore Proxy suffix
                if (ratio >= 0.4) return 84;
            }

            var aCore = NormalizeCore(fieldName);
            var bCore = NormalizeCore(typeName);
            if (aCore.Length >= 3 && string.Equals(aCore, bCore, StringComparison.OrdinalIgnoreCase))
                return 90;

            // EnemyIcon ⊂ EnemyIconOutOfVision (field XComponent → type X…Component)
            if (aCore.Length >= 5 && bCore.Length > aCore.Length &&
                bCore.StartsWith(aCore, StringComparison.OrdinalIgnoreCase))
            {
                var ratio = (double)aCore.Length / bCore.Length;
                if (ratio >= 0.55) return 86;
                if (ratio >= 0.4) return 78;
                if (ratio >= 0.3 && aCore.Length >= 8) return 72;
            }

            var pascal = ToPascal(bare);
            if (pascal.Length >= 8 && typeName.EndsWith(pascal, StringComparison.OrdinalIgnoreCase))
                return 88;
            if (bare.Length >= 6 && typeName.IndexOf(bare, StringComparison.OrdinalIgnoreCase) >= 0)
            {
                var ratio = (double)bare.Length / typeName.Length;
                if (ratio >= 0.5) return 80;
                if (ratio >= 0.4) return 70;
            }
            // Field core appears as contiguous prefix of type name
            if (aCore.Length >= 5 && typeName.StartsWith(aCore, StringComparison.OrdinalIgnoreCase))
                return 82;

            if (bare.EndsWith("Control", StringComparison.Ordinal) && bare.Length > 7)
            {
                var head = bare.Substring(0, bare.Length - 7);
                if (head.Length >= 3 &&
                    typeName.IndexOf(head, StringComparison.OrdinalIgnoreCase) >= 0 &&
                    (typeName.EndsWith("Component", StringComparison.Ordinal) ||
                     typeName.EndsWith("ComponentBase", StringComparison.Ordinal) ||
                     typeName.EndsWith("Control", StringComparison.Ordinal) ||
                     typeName.EndsWith("Controller", StringComparison.Ordinal)))
                {
                    if (typeName.StartsWith(head + "Play", StringComparison.OrdinalIgnoreCase))
                        return 94; // AnimControl → AnimPlayComponentBase
                    if (typeName.StartsWith(head, StringComparison.OrdinalIgnoreCase) &&
                        typeName.EndsWith("LinkerComponent", StringComparison.Ordinal))
                        return 93;
                    if (typeName.StartsWith(head, StringComparison.OrdinalIgnoreCase) &&
                        typeName.EndsWith("Component", StringComparison.Ordinal))
                        return 88;
                    if (typeName.EndsWith(bare, StringComparison.OrdinalIgnoreCase) ||
                        typeName.EndsWith(ToPascal(bare), StringComparison.OrdinalIgnoreCase))
                        return 76; // FollowAnimControl — weaker than AnimPlay*
                    return 70;
                }
            }

            if (bare.StartsWith("Mat", StringComparison.Ordinal) && typeName.StartsWith("Material", StringComparison.Ordinal))
            {
                var rest = bare.Substring(3);
                if (rest.Length >= 3 && typeName.IndexOf(rest, StringComparison.OrdinalIgnoreCase) >= 0)
                    return 92;
            }

            if (bare.IndexOf("Shadow", StringComparison.OrdinalIgnoreCase) >= 0 &&
                typeName.IndexOf("Shadow", StringComparison.OrdinalIgnoreCase) >= 0)
            {
                var fieldStatic = bare.IndexOf("Static", StringComparison.OrdinalIgnoreCase) >= 0;
                var typeStatic = typeName.IndexOf("Static", StringComparison.OrdinalIgnoreCase) >= 0;
                if (fieldStatic == typeStatic)
                    return 72;
            }

            return 0;
        }

        private static IEnumerable<string> GenerateTypeNameGuesses(string fieldName)
        {
            var bare = StripFieldPrefix(fieldName);
            if (string.IsNullOrEmpty(bare))
                yield break;

            yield return bare;
            var pascal = ToPascal(bare);
            if (!string.Equals(pascal, bare, StringComparison.Ordinal))
                yield return pascal;

            // MatHurtEffect → MaterialHurtEffect
            if (bare.StartsWith("Mat", StringComparison.Ordinal) && bare.Length > 3 &&
                (char.IsUpper(bare[3]) || bare.Length > 3))
            {
                if (bare.Length > 3)
                    yield return "Material" + bare.Substring(3);
                if (!string.Equals(pascal, bare, StringComparison.Ordinal) && pascal.StartsWith("Mat", StringComparison.Ordinal))
                    yield return "Material" + pascal.Substring(3);
            }

            // XControl → XLinkerComponent / XComponent / I* variants / XPlayComponent
            if (bare.EndsWith("Control", StringComparison.Ordinal) && bare.Length > 7)
            {
                var head = bare.Substring(0, bare.Length - 7);
                var ph = ToPascal(head);
                yield return ph + "LinkerComponent";
                yield return head + "LinkerComponent";
                yield return "I" + ph + "LinkerComponent";
                yield return "I" + ph + "Component3D"; // HudControl → IHudComponent3D
                yield return "I" + ph + "Component";
                yield return ph + "Component3D";
                yield return ph + "PlayComponentBase";
                yield return ph + "PlayComponent";
                // Prefer Linker / Play / I* before bare XComponent (ActorControl→ActorComponent is weak)
                yield return ph + "Component";
                yield return head + "Component";
                yield return ph + "Controller";
                yield return head;
            }

            // ActorControl → ObjLinkerWrapper (HOK naming; beat ActorComponent guess)
            if (pascal.Equals("ActorControl", StringComparison.Ordinal) ||
                bare.Equals("ActorControl", StringComparison.OrdinalIgnoreCase))
            {
                yield return "IObjLinkerWrapper";
                yield return "ObjLinkerWrapper";
            }
            if (pascal.EndsWith("Control", StringComparison.Ordinal) && pascal.Length > 7 &&
                !string.Equals(pascal, bare, StringComparison.Ordinal))
            {
                var head = pascal.Substring(0, pascal.Length - 7);
                yield return head + "LinkerComponent";
                yield return "I" + head + "LinkerComponent";
                yield return "I" + head + "Component3D";
                yield return head + "PlayComponentBase";
                yield return head + "Component";
            }

            // miniMap → MinimapSysProxy
            if (pascal.Equals("MiniMap", StringComparison.OrdinalIgnoreCase) ||
                bare.Equals("miniMap", StringComparison.OrdinalIgnoreCase))
            {
                yield return "MinimapSysProxy";
                yield return "MinimapSys";
                yield return "MiniMapSysProxy";
            }

            // resHeroCfgInfo / heroCfgInfo → ResHeroCfgInfo (not Wrapper)
            if (bare.IndexOf("HeroCfg", StringComparison.OrdinalIgnoreCase) >= 0 ||
                bare.IndexOf("HeroConfig", StringComparison.OrdinalIgnoreCase) >= 0)
            {
                yield return "ResHeroCfgInfo";
            }

            // ShadowEffect → UpdateShadowPlane
            if (bare.StartsWith("ShadowEffect", StringComparison.OrdinalIgnoreCase) ||
                pascal.StartsWith("ShadowEffect", StringComparison.OrdinalIgnoreCase))
            {
                if (bare.IndexOf("Static", StringComparison.OrdinalIgnoreCase) >= 0 ||
                    pascal.IndexOf("Static", StringComparison.OrdinalIgnoreCase) >= 0)
                    yield return "UpdateShadowPlane_Static";
                else
                    yield return "UpdateShadowPlane";
            }
        }

        private static IEnumerable<string> AlternateCores(string fieldName)
        {
            var bare = StripFieldPrefix(fieldName);
            yield return NormalizeCore(bare);
            yield return NormalizeCore(ToPascal(bare));
            if (bare.EndsWith("Control", StringComparison.Ordinal) && bare.Length > 7)
                yield return NormalizeCore(bare.Substring(0, bare.Length - 7));
            if (bare.StartsWith("Mat", StringComparison.Ordinal) && bare.Length > 3)
                yield return NormalizeCore("Material" + bare.Substring(3));
        }

        private static string NormalizeCore(string name)
        {
            if (string.IsNullOrEmpty(name))
                return string.Empty;
            var n = StripFieldPrefix(name);
            bool stripped;
            do
            {
                stripped = false;
                foreach (var suf in new[]
                         {
                             "LinkerComponent", "Component", "Controller", "Control", "Proxy",
                             "Manager", "System", "Handler", "Provider", "Factory", "Wrapper"
                         })
                {
                    if (n.EndsWith(suf, StringComparison.Ordinal) && n.Length > suf.Length + 2)
                    {
                        n = n.Substring(0, n.Length - suf.Length);
                        stripped = true;
                        break;
                    }
                }
            } while (stripped);

            if (n.StartsWith("Material", StringComparison.Ordinal) && n.Length > 8)
                n = "Mat" + n.Substring(8);

            return n;
        }

        private static IEnumerable<string> CamelSuffixes(string name)
        {
            if (string.IsNullOrEmpty(name))
                yield break;
            yield return name;
            for (var i = 1; i < name.Length; i++)
            {
                if (char.IsUpper(name[i]))
                    yield return name.Substring(i);
            }
            // also underscore split
            var us = name.IndexOf('_');
            if (us > 0 && us + 1 < name.Length)
                yield return name.Substring(us + 1);
        }

        private static List<string> CamelTokens(string name)
        {
            var list = new List<string>();
            if (string.IsNullOrEmpty(name)) return list;
            var start = 0;
            for (var i = 1; i < name.Length; i++)
            {
                if (char.IsUpper(name[i]))
                {
                    list.Add(name.Substring(start, i - start));
                    start = i;
                }
            }
            list.Add(name.Substring(start));
            return list;
        }

        public static bool LooksLikeCollectionField(string fieldName)
        {
            if (string.IsNullOrEmpty(fieldName))
                return false;
            var bare = StripFieldPrefix(fieldName);
            if (bare.EndsWith("List", StringComparison.OrdinalIgnoreCase)) return true;
            if (bare.EndsWith("Array", StringComparison.OrdinalIgnoreCase)) return true;
            if (bare.EndsWith("Components", StringComparison.Ordinal)) return true;
            if (bare.EndsWith("Items", StringComparison.Ordinal)) return true;
            if (bare.EndsWith("Ids", StringComparison.Ordinal) || bare.EndsWith("IDs", StringComparison.Ordinal))
                return true;
            if (bare.Length >= 5 && bare.EndsWith("s", StringComparison.Ordinal) &&
                char.IsLower(bare[bare.Length - 2]) &&
                !bare.EndsWith("ss", StringComparison.Ordinal) &&
                !bare.EndsWith("us", StringComparison.Ordinal) &&
                !bare.EndsWith("is", StringComparison.Ordinal) &&
                !bare.EndsWith("Status", StringComparison.Ordinal) &&
                !bare.EndsWith("Flags", StringComparison.Ordinal) &&
                !bare.EndsWith("Bounds", StringComparison.Ordinal) &&
                !bare.EndsWith("Params", StringComparison.Ordinal) &&
                !bare.EndsWith("Class", StringComparison.Ordinal) &&
                !bare.EndsWith("Bones", StringComparison.Ordinal))
            {
                for (var i = 1; i < bare.Length - 1; i++)
                    if (char.IsUpper(bare[i])) return true;
                if (bare.Length >= 6) return true;
            }
            return false;
        }

        private static string StripFieldPrefix(string fieldName)
        {
            if (string.IsNullOrEmpty(fieldName))
                return fieldName;
            if (fieldName.Length > 16 && fieldName[0] == '<' &&
                fieldName.Contains(">k__BackingField", StringComparison.Ordinal))
            {
                var end = fieldName.IndexOf('>');
                if (end > 1)
                    return fieldName.Substring(1, end - 1);
            }
            if (fieldName.StartsWith("m_", StringComparison.Ordinal) || fieldName.StartsWith("s_", StringComparison.Ordinal))
                return fieldName.Substring(2);
            if (fieldName.StartsWith("_", StringComparison.Ordinal))
                return fieldName.Substring(1);
            // mFoo but not mat/mesh/move/max/mini/monster
            if (fieldName.StartsWith("m", StringComparison.Ordinal) && fieldName.Length > 1 && char.IsUpper(fieldName[1]))
            {
                if (!fieldName.StartsWith("mini", StringComparison.OrdinalIgnoreCase) &&
                    !fieldName.StartsWith("max", StringComparison.OrdinalIgnoreCase) &&
                    !fieldName.StartsWith("mesh", StringComparison.OrdinalIgnoreCase) &&
                    !fieldName.StartsWith("mat", StringComparison.OrdinalIgnoreCase) &&
                    !fieldName.StartsWith("move", StringComparison.OrdinalIgnoreCase) &&
                    !fieldName.StartsWith("monster", StringComparison.OrdinalIgnoreCase) &&
                    !fieldName.StartsWith("meta", StringComparison.OrdinalIgnoreCase) &&
                    !fieldName.StartsWith("main", StringComparison.OrdinalIgnoreCase))
                    return fieldName.Substring(1);
            }
            return fieldName;
        }

        private static string ToPascal(string name)
        {
            if (string.IsNullOrEmpty(name)) return name;
            if (char.IsUpper(name[0])) return name;
            return char.ToUpperInvariant(name[0]) + name.Substring(1);
        }

        private static bool IsObjectName(string tn) =>
            string.IsNullOrEmpty(tn) || tn == "object" || tn == "Object";

        private static int FindBestSource(
            List<string> candidates,
            List<(string name, int typeIndex)> props,
            List<(string name, int typeIndex)> methods,
            Il2Cpp il2Cpp,
            Metadata metadata,
            string fieldName)
        {
            var bestScore = 0;
            var bestTi = -1;

            void Consider(string otherName, int ti)
            {
                if (IsUnresolved(il2Cpp, ti)) return;
                if (IsPrimitiveType(il2Cpp, metadata, ti) && !FieldNameLooksPrimitive(fieldName))
                    return;
                foreach (var c in candidates)
                {
                    var score = MatchScore(c, otherName);
                    if (score > bestScore)
                    {
                        bestScore = score;
                        bestTi = ti;
                    }
                }
            }

            foreach (var (pn, ti) in props)
                Consider(pn, ti);
            foreach (var (mn, ti) in methods)
                Consider(mn, ti);

            return bestScore >= 50 ? bestTi : -1;
        }

        private static readonly HashSet<string> PrimitiveTypeNames = new(StringComparer.Ordinal)
        {
            "Boolean", "Byte", "SByte", "Char", "Int16", "UInt16", "Int32", "UInt32",
            "Int64", "UInt64", "Single", "Double", "IntPtr", "UIntPtr", "Decimal"
        };

        private static bool IsPrimitiveType(Il2Cpp il2Cpp, Metadata metadata, int typeIndex)
        {
            if (typeIndex < 0 || typeIndex >= il2Cpp.types.Length)
                return false;
            var t = il2Cpp.types[typeIndex];
            if (t == null) return false;
            switch (t.type)
            {
                case Il2CppTypeEnum.IL2CPP_TYPE_BOOLEAN:
                case Il2CppTypeEnum.IL2CPP_TYPE_CHAR:
                case Il2CppTypeEnum.IL2CPP_TYPE_I1:
                case Il2CppTypeEnum.IL2CPP_TYPE_U1:
                case Il2CppTypeEnum.IL2CPP_TYPE_I2:
                case Il2CppTypeEnum.IL2CPP_TYPE_U2:
                case Il2CppTypeEnum.IL2CPP_TYPE_I4:
                case Il2CppTypeEnum.IL2CPP_TYPE_U4:
                case Il2CppTypeEnum.IL2CPP_TYPE_I8:
                case Il2CppTypeEnum.IL2CPP_TYPE_U8:
                case Il2CppTypeEnum.IL2CPP_TYPE_R4:
                case Il2CppTypeEnum.IL2CPP_TYPE_R8:
                case Il2CppTypeEnum.IL2CPP_TYPE_I:
                case Il2CppTypeEnum.IL2CPP_TYPE_U:
                    return true;
            }
            if (t.type is Il2CppTypeEnum.IL2CPP_TYPE_VALUETYPE or Il2CppTypeEnum.IL2CPP_TYPE_CLASS)
            {
                var idx = (int)t.data.klassIndex;
                if (idx >= 0 && idx < metadata.typeDefs.Length)
                {
                    var n = metadata.GetStringFromIndex(metadata.typeDefs[idx].nameIndex);
                    if (PrimitiveTypeNames.Contains(n))
                        return true;
                }
            }
            return false;
        }

        private static bool FieldNameLooksPrimitive(string fieldName)
        {
            if (string.IsNullOrEmpty(fieldName)) return false;
            var n = StripFieldPrefix(fieldName);
            if (n.StartsWith("b", StringComparison.Ordinal) && n.Length > 1 && char.IsUpper(n[1]))
                return true;
            if (n.StartsWith("is", StringComparison.OrdinalIgnoreCase) ||
                n.StartsWith("has", StringComparison.OrdinalIgnoreCase) ||
                n.StartsWith("can", StringComparison.OrdinalIgnoreCase) ||
                n.StartsWith("enable", StringComparison.OrdinalIgnoreCase) ||
                n.StartsWith("use", StringComparison.OrdinalIgnoreCase))
                return true;
            if (n.EndsWith("Count", StringComparison.Ordinal) ||
                n.EndsWith("Id", StringComparison.Ordinal) ||
                n.EndsWith("ID", StringComparison.Ordinal) ||
                n.EndsWith("Index", StringComparison.Ordinal) ||
                n.EndsWith("Num", StringComparison.Ordinal) ||
                n.EndsWith("Flag", StringComparison.Ordinal) ||
                (n.EndsWith("Type", StringComparison.Ordinal) && n.Length < 12))
                return true;
            return false;
        }

        private static int MatchScore(string fieldKey, string other)
        {
            if (string.IsNullOrEmpty(fieldKey) || string.IsNullOrEmpty(other))
                return 0;
            if (string.Equals(fieldKey, other, StringComparison.Ordinal))
                return 100;
            if (string.Equals(fieldKey, other, StringComparison.OrdinalIgnoreCase))
                return 95;

            var aCore = NormalizeCore(fieldKey);
            var bCore = NormalizeCore(other);
            if (string.Equals(aCore, bCore, StringComparison.OrdinalIgnoreCase))
                return 90;

            static int ContainScore(string shorter, string longer)
            {
                if (shorter.Length < 5) return 0;
                if (longer.IndexOf(shorter, StringComparison.OrdinalIgnoreCase) < 0)
                    return 0;
                var ratio = (double)shorter.Length / longer.Length;
                if (ratio >= 0.6) return 80;
                if (ratio >= 0.4 && shorter.Length >= 8) return 60;
                if (shorter.Length >= 10) return 55;
                return 0;
            }

            var s1 = aCore.Length <= bCore.Length ? ContainScore(aCore, bCore) : ContainScore(bCore, aCore);
            if (s1 > 0) return s1;
            return ContainScore(
                fieldKey.Length <= other.Length ? fieldKey : other,
                fieldKey.Length > other.Length ? fieldKey : other);
        }

        private static bool IsUnresolved(Il2Cpp il2Cpp, int typeIndex)
        {
            if (typeIndex < 0 || typeIndex >= il2Cpp.types.Length)
                return true;
            var t = il2Cpp.types[typeIndex];
            if (t == null)
                return true;
            return t.type == Il2CppTypeEnum.IL2CPP_TYPE_OBJECT && t.datapoint == 0;
        }

        public static uint GuessFieldVisibility(string fieldName)
        {
            if (string.IsNullOrEmpty(fieldName))
                return 1;
            if (fieldName.StartsWith("m_", StringComparison.Ordinal) ||
                fieldName.StartsWith("s_", StringComparison.Ordinal) ||
                fieldName.StartsWith("_", StringComparison.Ordinal) ||
                fieldName.StartsWith("<", StringComparison.Ordinal))
                return 1;
            if (char.IsUpper(fieldName[0]))
                return 6;
            return 1;
        }

        private static List<string> FieldNameCandidates(string fieldName)
        {
            var list = new List<string>();
            if (string.IsNullOrEmpty(fieldName))
                return list;

            if (fieldName.Length > 16 && fieldName[0] == '<' &&
                fieldName.Contains(">k__BackingField", StringComparison.Ordinal))
            {
                var end = fieldName.IndexOf('>');
                if (end > 1)
                    list.Add(fieldName.Substring(1, end - 1));
            }

            var bare = StripFieldPrefix(fieldName);
            if (bare.Length > 0)
            {
                list.Add(bare);
                list.Add(ToPascal(bare));
                list.Add(fieldName);
                if (bare.EndsWith("Control", StringComparison.Ordinal) && bare.Length > 7)
                {
                    var head = bare.Substring(0, bare.Length - 7);
                    list.Add(head);
                    list.Add(head + "Component");
                    list.Add(ToPascal(head) + "Component");
                }
                if (bare.EndsWith("Proxy", StringComparison.Ordinal) && bare.Length > 5)
                    list.Add(bare.Substring(0, bare.Length - 5));
            }
            return list.Distinct(StringComparer.Ordinal).ToList();
        }
    }
}
