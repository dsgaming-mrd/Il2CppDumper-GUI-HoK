using System;

namespace Il2CppDumper
{
    /// <summary>
    /// The kind of metadata index a field represents. Starting with metadata
    /// version 38 (Unity 6000.3.0a5) and 39 (Unity 6000.3.0b1), several index
    /// fields in global-metadata.dat are stored using a *variable* width
    /// (1, 2 or 4 bytes) that is derived from the number of entries in the
    /// corresponding metadata table. Each kind maps to one such table.
    /// </summary>
    public enum IndexKind
    {
        /// <summary>Not an index / always a fixed 4-byte int32.</summary>
        None = 0,
        TypeDef,            // Il2CppTypeDefinition table (type_definitions_count)
        GenericContainer,   // Il2CppGenericContainer table (generic_containers_count)
        TypeIndex,          // Il2CppType table (derived from interface_offsets element size)
        ParameterDef,       // Il2CppParameterDefinition table (parameters_count) - variable in v39+
        InterfaceOffset,    // interface offsets table - variable in v104+
        Event,              // events table - variable in v104+
        Property,           // properties table - variable in v104+
        NestedType,         // nested types table - variable in v104+
        Method,             // methods table - variable in v105+
        GenericParam,       // generic parameters table - variable in v106+
        Field,              // fields table - variable in v106+
        DefaultValueData,   // field/parameter default value data - variable in v106+
    }

    /// <summary>
    /// Marks an int32 metadata field as a table index whose on-disk width is
    /// variable for metadata version 38+. For versions &lt; 38 the field is
    /// always read as a regular 4-byte int32, so this attribute is a no-op there.
    /// </summary>
    [AttributeUsage(AttributeTargets.Field)]
    public sealed class IndexAttribute : Attribute
    {
        public IndexKind Kind { get; set; } = IndexKind.None;
    }
}