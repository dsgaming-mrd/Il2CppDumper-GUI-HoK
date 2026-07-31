namespace Il2CppDumper
{
    /// <summary>
    /// Holds the on-disk byte width (1, 2 or 4) of every variable-width metadata
    /// index kind for a given metadata file. For versions &lt; 38 every width is 4.
    /// </summary>
    public sealed class IndexWidths
    {
        public byte TypeDef = 4;
        public byte GenericContainer = 4;
        public byte TypeIndex = 4;
        public byte ParameterDef = 4;
        public byte InterfaceOffset = 4;
        public byte Event = 4;
        public byte Property = 4;
        public byte NestedType = 4;
        public byte Method = 4;
        public byte GenericParam = 4;
        public byte Field = 4;
        public byte DefaultValueData = 4;

        public byte Get(IndexKind kind)
        {
            return kind switch
            {
                IndexKind.TypeDef => TypeDef,
                IndexKind.GenericContainer => GenericContainer,
                IndexKind.TypeIndex => TypeIndex,
                IndexKind.ParameterDef => ParameterDef,
                IndexKind.InterfaceOffset => InterfaceOffset,
                IndexKind.Event => Event,
                IndexKind.Property => Property,
                IndexKind.NestedType => NestedType,
                IndexKind.Method => Method,
                IndexKind.GenericParam => GenericParam,
                IndexKind.Field => Field,
                IndexKind.DefaultValueData => DefaultValueData,
                _ => 4,
            };
        }

        /// <summary>
        /// Width based on the number of entries in a table: an unsigned index
        /// can address up to (2^bits - 1) entries, with the all-ones value
        /// reserved as the "invalid" (-1) sentinel.
        /// </summary>
        private static byte WidthForCount(int count)
        {
            if (count <= 0) return 4;
            if (count <= 0xFF) return 1;
            if (count <= 0xFFFF) return 2;
            return 4;
        }

        /// <summary>
        /// The width of a TypeIndex is derived from the size of an interface
        /// offset pair entry (a TypeIndex followed by a 4-byte offset).
        /// </summary>
        public static byte TypeIndexSize(Il2CppGlobalMetadataHeader h)
        {
            if (h.interfaceOffsetsCount > 0 && h.interfaceOffsetsSize > 0)
            {
                var bytesPerEntry = h.interfaceOffsetsSize / h.interfaceOffsetsCount;
                if (bytesPerEntry > 4)
                    return (byte)(bytesPerEntry - 4);
            }
            return 4;
        }

        public static IndexWidths FromHeader(Il2CppGlobalMetadataHeader h, double version)
        {
            var w = new IndexWidths();
            if (version < 38)
            {
                return w; // everything stays 4 bytes
            }

            w.TypeDef = WidthForCount(h.typeDefinitionsCount);
            w.GenericContainer = WidthForCount(h.genericContainersCount);
            w.TypeIndex = TypeIndexSize(h);

            // parameter definitions became variable-width in v39
            w.ParameterDef = version >= 39 ? WidthForCount(h.parametersCount) : (byte)4;

            // the remaining tables only became variable-width in the
            // experimental Unity 6000.5 metadata versions (104/105/106)
            w.InterfaceOffset = version >= 104 ? WidthForCount(h.interfaceOffsetsCount) : (byte)4;
            w.Event = version >= 104 ? WidthForCount(h.eventsCount) : (byte)4;
            w.Property = version >= 104 ? WidthForCount(h.propertiesCount) : (byte)4;
            w.NestedType = version >= 104 ? WidthForCount(h.nestedTypesCount) : (byte)4;
            w.Method = version >= 105 ? WidthForCount(h.methodsCount) : (byte)4;
            w.GenericParam = version >= 106 ? WidthForCount(h.genericParametersCount) : (byte)4;
            w.Field = version >= 106 ? WidthForCount(h.fieldsCount) : (byte)4;
            w.DefaultValueData = version >= 106 ? WidthForCount(h.fieldAndParameterDefaultValueDataCount) : (byte)4;

            return w;
        }
    }
}