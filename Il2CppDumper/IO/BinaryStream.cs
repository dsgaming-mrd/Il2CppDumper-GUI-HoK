using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Text;

namespace Il2CppDumper
{
    public class BinaryStream : IDisposable
    {
        public double Version;
        public bool Is32Bit;
        public ulong ImageBase;
        private readonly Stream stream;
        private readonly BinaryReader reader;
        private readonly BinaryWriter writer;
        private readonly MethodInfo readClass;
        private readonly MethodInfo readClassArray;
        private readonly Dictionary<Type, MethodInfo> genericMethodCache;
        private readonly Dictionary<FieldInfo, VersionAttribute[]> attributeCache;
        private readonly Dictionary<FieldInfo, IndexAttribute> indexAttributeCache;

        /// <summary>
        /// Variable-width index sizes for the current metadata file. Defaults to
        /// all 4-byte widths; populated from the header for metadata version 38+.
        /// </summary>
        public IndexWidths IndexSizes = new IndexWidths();

        public BinaryStream(Stream input)
        {
            stream = input;
            reader = new BinaryReader(stream, Encoding.UTF8, true);
            writer = new BinaryWriter(stream, Encoding.UTF8, true);
            readClass = GetType().GetMethod("ReadClass", Type.EmptyTypes);
            readClassArray = GetType().GetMethod("ReadClassArray", new[] { typeof(long) });
            genericMethodCache = new();
            attributeCache = new();
            indexAttributeCache = new();
        }

        public bool ReadBoolean() => reader.ReadBoolean();

        public byte ReadByte() => reader.ReadByte();

        public byte[] ReadBytes(int count) => reader.ReadBytes(count);

        public sbyte ReadSByte() => reader.ReadSByte();

        public short ReadInt16() => reader.ReadInt16();

        public ushort ReadUInt16() => reader.ReadUInt16();

        public int ReadInt32() => reader.ReadInt32();

        public uint ReadUInt32() => reader.ReadUInt32();

        public long ReadInt64() => reader.ReadInt64();

        public ulong ReadUInt64() => reader.ReadUInt64();

        public float ReadSingle() => reader.ReadSingle();

        public double ReadDouble() => reader.ReadDouble();

        public uint ReadCompressedUInt32() => reader.ReadCompressedUInt32();

        public int ReadCompressedInt32() => reader.ReadCompressedInt32();

        public uint ReadULeb128() => reader.ReadULeb128();

        public void Write(bool value) => writer.Write(value);

        public void Write(byte value) => writer.Write(value);

        public void Write(sbyte value) => writer.Write(value);

        public void Write(short value) => writer.Write(value);

        public void Write(ushort value) => writer.Write(value);

        public void Write(int value) => writer.Write(value);

        public void Write(uint value) => writer.Write(value);

        public void Write(long value) => writer.Write(value);

        public void Write(ulong value) => writer.Write(value);

        public void Write(float value) => writer.Write(value);

        public void Write(double value) => writer.Write(value);

        public ulong Position
        {
            get => (ulong)stream.Position;
            set => stream.Position = (long)value;
        }

        public ulong Length => (ulong)stream.Length;

        private object ReadPrimitive(Type type)
        {
            return type.Name switch
            {
                "Int32" => ReadInt32(),
                "UInt32" => ReadUInt32(),
                "Int16" => ReadInt16(),
                "UInt16" => ReadUInt16(),
                "Byte" => ReadByte(),
                "Int64" => ReadIntPtr(),
                "UInt64" => ReadUIntPtr(),
                _ => throw new NotSupportedException()
            };
        }

        /// <summary>
        /// Reads a variable-width metadata index. Widths of 1 and 2 bytes use the
        /// all-ones value (0xFF / 0xFFFF) as the "invalid" (-1) sentinel, matching
        /// the il2cpp runtime. A width of 4 is a plain signed int32.
        /// </summary>
        public int ReadVariableIndex(byte width)
        {
            switch (width)
            {
                case 1:
                    var b = ReadByte();
                    return b == byte.MaxValue ? -1 : b;
                case 2:
                    var s = ReadUInt16();
                    return s == ushort.MaxValue ? -1 : s;
                case 4:
                    return ReadInt32();
                default:
                    throw new NotSupportedException($"Invalid variable index width: {width}");
            }
        }

        public T ReadClass<T>(ulong addr) where T : new()
        {
            Position = addr;
            return ReadClass<T>();
        }

        public T ReadClass<T>() where T : new()
        {
            var type = typeof(T);
            if (type.IsPrimitive)
            {
                return (T)ReadPrimitive(type);
            }
            else
            {
                var t = new T();
                foreach (var i in t.GetType().GetFields())
                {
                    if (!attributeCache.TryGetValue(i, out var versionAttributes))
                    {
                        if (Attribute.IsDefined(i, typeof(VersionAttribute)))
                        {
                            versionAttributes = i.GetCustomAttributes<VersionAttribute>().ToArray();
                            attributeCache.Add(i, versionAttributes);
                        }
                    }
                    if (versionAttributes?.Length > 0)
                    {
                        var read = false;
                        foreach (var versionAttribute in versionAttributes)
                        {
                            if (Version >= versionAttribute.Min && Version <= versionAttribute.Max)
                            {
                                read = true;
                                break;
                            }
                        }
                        if (!read)
                        {
                            continue;
                        }
                    }
                    var fieldType = i.FieldType;
                    if (fieldType.IsPrimitive)
                    {
                        // Metadata v38+: some int32 index fields are stored with a
                        // variable on-disk width derived from the table sizes.
                        if (Version >= 38)
                        {
                            if (!indexAttributeCache.TryGetValue(i, out var indexAttribute))
                            {
                                indexAttribute = i.GetCustomAttribute<IndexAttribute>();
                                indexAttributeCache.Add(i, indexAttribute);
                            }
                            if (indexAttribute != null && indexAttribute.Kind != IndexKind.None)
                            {
                                i.SetValue(t, ReadVariableIndex(IndexSizes.Get(indexAttribute.Kind)));
                                continue;
                            }
                        }
                        i.SetValue(t, ReadPrimitive(fieldType));
                    }
                    else if (fieldType.IsEnum)
                    {
                        var e = fieldType.GetField("value__").FieldType;
                        i.SetValue(t, ReadPrimitive(e));
                    }
                    else if (fieldType.IsArray)
                    {
                        var arrayLengthAttribute = i.GetCustomAttribute<ArrayLengthAttribute>();
                        if (!genericMethodCache.TryGetValue(fieldType, out var methodInfo))
                        {
                            methodInfo = readClassArray.MakeGenericMethod(fieldType.GetElementType());
                            genericMethodCache.Add(fieldType, methodInfo);
                        }
                        i.SetValue(t, methodInfo.Invoke(this, new object[] { arrayLengthAttribute.Length }));
                    }
                    else
                    {
                        if (!genericMethodCache.TryGetValue(fieldType, out var methodInfo))
                        {
                            methodInfo = readClass.MakeGenericMethod(fieldType);
                            genericMethodCache.Add(fieldType, methodInfo);
                        }
                        i.SetValue(t, methodInfo.Invoke(this, null));
                    }
                }
                return t;
            }
        }

        public T[] ReadClassArray<T>(long count) where T : new()
        {
            var t = new T[count];
            for (var i = 0; i < count; i++)
            {
                t[i] = ReadClass<T>();
            }
            return t;
        }

        public T[] ReadClassArray<T>(ulong addr, ulong count) where T : new()
        {
            return ReadClassArray<T>(addr, (long)count);
        }

        public T[] ReadClassArray<T>(ulong addr, long count) where T : new()
        {
            Position = addr;
            return ReadClassArray<T>(count);
        }

        public string ReadStringToNull(ulong addr)
        {
            Position = addr;
            var bytes = new List<byte>();
            byte b;
            while ((b = ReadByte()) != 0)
                bytes.Add(b);
            return Encoding.UTF8.GetString(bytes.ToArray());
        }

        public long ReadIntPtr()
        {
            return Is32Bit ? ReadInt32() : ReadInt64();
        }

        public virtual ulong ReadUIntPtr()
        {
            return Is32Bit ? ReadUInt32() : ReadUInt64();
        }

        public ulong PointerSize
        {
            get => Is32Bit ? 4ul : 8ul;
        }

        public BinaryReader Reader => reader;

        public BinaryWriter Writer => writer;

        protected virtual void Dispose(bool disposing)
        {
            if (disposing)
            {
                reader.Dispose();
                writer.Dispose();
                stream.Close();
            }
        }

        public void Dispose()
        {
            Dispose(true);
            GC.SuppressFinalize(this);
        }
    }
}
