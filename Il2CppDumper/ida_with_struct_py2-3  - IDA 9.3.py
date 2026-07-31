# -*- coding: utf-8 -*-
from __future__ import print_function, division
import json
import re
import sys
import idc
import idaapi
import ida_funcs

IS_PY3 = sys.version_info[0] >= 3

if IS_PY3:
    import ida_typeinf
    SN_NOWARN = idc.SN_NOWARN
    SN_NOCHECK = idc.SN_NOCHECK
    FUNCATTR_START = idc.FUNCATTR_START
else:
    SN_NOWARN = globals().get('SN_NOWARN', 2)
    SN_NOCHECK = globals().get('SN_NOCHECK', 4)
    FUNCATTR_START = globals().get('FUNCATTR_START', 0)

def compatibility_set_type(addr, clean_sig):
    if IS_PY3:
        return idc.SetType(addr, clean_sig) is True
    else:
        parse_decl_func = globals().get('parse_decl')
        apply_type_func = globals().get('apply_type')
        if parse_decl_func and apply_type_func:
            tp = parse_decl_func(clean_sig, 0)
            if tp is not None:
                return apply_type_func(addr, tp, 1) == True
        return False

processFields = [
    "ScriptMethod",
    "ScriptString",
    "ScriptMetadata",
    "ScriptMetadataMethod",
    "Addresses",
]

imageBase = idaapi.get_imagebase()

def get_addr(addr):
    return imageBase + addr

def set_name(addr, name):
    if IS_PY3 and isinstance(name, bytes):
        name = name.decode('utf-8')
    elif not IS_PY3 and isinstance(name, unicode):
        name = name.encode('utf-8')

    ret = idc.set_name(addr, name, SN_NOWARN | SN_NOCHECK)
    if ret == 0:
        new_name = str(name) + '_' + str(addr)
        ret = idc.set_name(addr, new_name, SN_NOWARN | SN_NOCHECK)

def make_function(start, end):
    next_func = idc.get_next_func(start)
    if next_func < end:
        end = next_func
    if idc.get_func_attr(start, FUNCATTR_START) == start:
        ida_funcs.del_func(start)
    ida_funcs.add_func(start, end)

def force_clean_types(signature):
    if not signature:
        return signature

    match = re.match(r'^([^(]+)\((.*)\)\s*;?$', signature.strip())
    if not match:
        return signature

    ret_and_name = match.group(1).strip()
    args_str = match.group(2).strip()

    built_in_whitelist = ['void', 'bool', 'int', 'int32_t', 'uint32_t', 'int64_t', 'uint64_t', 'float', 'double', 'char', 'short', 'int8_t', 'uint8_t', 'int16_t', 'uint16_t']

    ret_words = ret_and_name.split()
    if len(ret_words) > 1:
        ret_type = ret_words[0]
        if ret_type not in built_in_whitelist and not ret_type.endswith('*'):
            ret_text = "void*"
            for w in ret_words[1:]:
                 if "__" not in w:
                     ret_text += " " + w
            ret_and_name = "void* " + ret_words[-1]

    if not args_str or args_str.lower() == 'void':
        return f"{ret_and_name}(void);" if IS_PY3 else ret_and_name + "(void);"

    args = args_str.split(',')
    new_args = []
    for arg in args:
        arg = arg.strip()
        arg_parts = arg.split()
        if len(arg_parts) > 1:
            var_name = arg_parts[-1]
            new_args.append("void* " + var_name)
        else:
            new_args.append("void*")

    return f"{ret_and_name}({', '.join(new_args)});" if IS_PY3 else ret_and_name + "(" + ", ".join(new_args) + ");"

def apply_signature_9x(addr, signature):
    clean_sig = signature.strip()
    if not clean_sig.endswith(';'):
        clean_sig += ';'

    if compatibility_set_type(addr, clean_sig):
        return True

    safe_sig = force_clean_types(clean_sig)
    if compatibility_set_type(addr, safe_sig):
        return True

    return False

path = idaapi.ask_file(False, '*.json', 'script.json from Il2cppdumper')
hpath = idaapi.ask_file(False, '*.h', 'il2cpp.h from Il2cppdumper')

if hpath:
    with open(hpath, 'rb') as f:
        header_content = f.read()
        if IS_PY3:
            header_content = header_content.decode('utf-8', errors='ignore')

        print("[IDA Dual-Version] Filtering duplicate structures from il2cpp.h...")
        header_content = re.sub(r'struct\s+CGPoint\s*\{[^}]*\}\s*;', '/* struct CGPoint removed */', header_content)
        header_content = re.sub(r'struct\s+CGRect\s*\{[^}]*\}\s*;', '/* struct CGRect removed */', header_content)
        header_content = re.sub(r'struct\s+CGSize\s*\{[^}]*\}\s*;', '/* struct CGSize removed */', header_content)
        header_content = re.sub(r'struct\s+UIEdgeInsets\s*\{[^}]*\}\s*;', '/* struct UIEdgeInsets removed */', header_content)

        if IS_PY3:
            ida_typeinf.parse_decls(None, header_content, None, True)
        else:
            globals().get('parse_decls')(header_content, 0)

with open(path, 'rb') as f:
    json_raw = f.read()
    if IS_PY3:
        data = json.loads(json_raw.decode('utf-8'))
    else:
        data = json.loads(json_raw)

if "Addresses" in data and "Addresses" in processFields:
    addresses = data["Addresses"]
    for index in range(len(addresses) - 1):
        start = get_addr(addresses[index])
        end = get_addr(addresses[index + 1])
        make_function(start, end)

if "ScriptMethod" in data and "ScriptMethod" in processFields:
    scriptMethods = data["ScriptMethod"]
    for scriptMethod in scriptMethods:
        addr = get_addr(scriptMethod["Address"])
        name = scriptMethod["Name"]
        set_name(addr, name)
        signature = scriptMethod["Signature"]

        if not apply_signature_9x(addr, signature):
            if IS_PY3:
                print(f"[Type Error] Failed to apply type: {hex(addr)} -> {signature}")
            else:
                print("[Type Error] Failed to apply type:", hex(addr), "->", signature)

if "ScriptString" in data and "ScriptString" in processFields:
    index = 1
    scriptStrings = data["ScriptString"]
    for scriptString in scriptStrings:
        addr = get_addr(scriptString["Address"])
        value = scriptString["Value"]
        if not IS_PY3 and isinstance(value, unicode):
            value = value.encode('utf-8')

        name = "StringLiteral_" + str(index)
        idc.set_name(addr, name, SN_NOWARN)
        idc.set_cmt(addr, value, 1)
        index += 1

if "ScriptMetadata" in data and "ScriptMetadata" in processFields:
    scriptMetadatas = data["ScriptMetadata"]
    for scriptMetadata in scriptMetadatas:
        addr = get_addr(scriptMetadata["Address"])
        name = scriptMetadata["Name"]
        set_name(addr, name)

        cmt_name = name.encode('utf-8') if (not IS_PY3 and isinstance(name, unicode)) else name
        idc.set_cmt(addr, cmt_name, 1)

        if scriptMetadata["Signature"] is not None:
            signature = scriptMetadata["Signature"]
            if not apply_signature_9x(addr, signature):
                if IS_PY3:
                    print(f"[Metadata Error] Failed at: {hex(addr)}")
                else:
                    print("[Metadata Error] Failed at:", hex(addr))

if "ScriptMetadataMethod" in data and "ScriptMetadataMethod" in processFields:
    scriptMetadataMethods = data["ScriptMetadataMethod"]
    for scriptMetadataMethod in scriptMetadataMethods:
        addr = get_addr(scriptMetadataMethod["Address"])
        name = scriptMetadataMethod["Name"]
        methodAddr = get_addr(scriptMetadataMethod["MethodAddress"])
        set_name(addr, name)

        cmt_name = name.encode('utf-8') if (not IS_PY3 and isinstance(name, unicode)) else name
        idc.set_cmt(addr, cmt_name, 1)
        idc.set_cmt(addr, '{0:X}'.format(methodAddr), 0)

print('Script finished successfully!')
