# Kế hoạch & Kết quả sửa lỗi trích xuất stringliteral.json

## 1. Nguyên nhân gốc rễ (Root Cause)
- **Cấu trúc Play Together vs Honor of Kings (HoK)**:
  - Ở Play Together (và binary thông thường), Unity lưu mảng encoded tokens `(5 << 29) | (index << 1) + 1` trực tiếp trong section dữ liệu `__DATA.__data` trên đĩa. `StructGenerator.cs` quét section `Data` và trích xuất được toàn bộ 27,533 chuỗi.
  - Ở Honor of Kings (phiên bản Unity 2021+ với metadata bảo vệ / synthetic recovery), toàn bộ metadata usage slots cho string literals được cấp phát trong `__DATA.__bss` (`0x1036A000..0x113666E8` ở new dump và `0xFD48000..0x10CF0418` ở old dump). Trên file đĩa, section BSS có `offset = 0`, không chứa các token cố định ban đầu, dẫn đến việc quét section raw data thu được 0 string literal (`hits = 0`).
  - Hơn nữa, cờ `!il2Cpp.IsSyntheticRecovery` tại dòng 314 của `StructGenerator.cs` bỏ qua hoàn toàn luồng metadata usage khi chạy phục hồi tổng hợp, làm cho `json.ScriptString` luôn rỗng và xuất ra `stringliteral.json = []` (chỉ 2 byte).

## 2. Giải pháp thực hiện (Fix Implementation)
1. **Khám phá tự động địa chỉ bảng String Literal (`StringLiteralTableBase`)**:
   - Thêm thuộc tính `public ulong StringLiteralTableBase { get; set; }` vào [Il2Cpp.cs](file:///c:/Users/Tran%20Tuan%20Dung/Downloads/Il2CppDumper-master/Il2CppDumper-master/Il2CppDumper.Core/Il2Cpp/Il2Cpp.cs).
   - Trong [HoKEscherRecovery.cs](file:///c:/Users/Tran%20Tuan%20Dung/Downloads/Il2CppDumper-master/Il2CppDumper-master/Il2CppDumper.Core/Il2Cpp/HoKEscherRecovery.cs), sau khi khôi phục toàn bộ con trỏ phương thức, thuật toán `RecoverStringTableBase` tìm hàm anchor `RegisterAllNetMsgHandlers`, giải mã cặp lệnh ARM64 `ADRP + LDR` nạp chuỗi `LegacyNetMsgRegister.RegisterAllNetMsgHandlers,msgCount=` vào BSS, tính toán chính xác tuyệt đối:
     - New dump: Base = `0x104D9460` (khớp 100% với các chỉ số chuỗi trong code ARM64).
     - Old dump: Base = `0xFEB4868` (khớp 100% với các chỉ số chuỗi trong code ARM64).
2. **Tổng hợp đầy đủ chuỗi từ Metadata khi ScriptString rỗng**:
   - Trong [StructGenerator.cs](file:///c:/Users/Tran%20Tuan%20Dung/Downloads/Il2CppDumper-master/Il2CppDumper-master/Il2CppDumper.Core/Outputs/StructGenerator.cs), khi `json.ScriptString.Count == 0`, tự động duyệt qua toàn bộ `metadata.stringLiterals`, gán địa chỉ `StringLiteralTableBase + index * 8` và lấy giá trị qua `metadata.GetStringLiteralFromIndex(i)`.
   - Xuất đầy đủ cả [stringliteral.json](file:///C:/Users/Tran%20Tuan%20Dung/Desktop/Dump/Honor%20of%20Kings/dump/stringliteral.json) và mảng `ScriptString` trong [script.json](file:///C:/Users/Tran%20Tuan%20Dung/Desktop/Dump/Honor%20of%20Kings/dump/script.json), hoàn toàn tương thích và đồng bộ với script IDA Pro / Ghidra (`ida_with_struct_py3.py`).

## 3. Kết quả kiểm tra (Verification)
- **New Dump (`dump`)**:
  - `stringliteral.json`: **90,221** chuỗi (kích thước ~8.32 MB), địa chỉ khởi đầu `0x104D9460`.
  - Chuỗi #472 (`LegacyNetMsgRegister.RegisterAllNetMsgHandlers`): địa chỉ `0x104DA320` (khớp hoàn toàn lệnh nạp của hàm tại RVA `0x618CC24`).
- **Old Dump (`dump old`)**:
  - `stringliteral.json`: **87,093** chuỗi (kích thước ~7.89 MB), địa chỉ khởi đầu `0xFEB4868`.
  - Chuỗi #469 (`LegacyNetMsgRegister.RegisterAllNetMsgHandlers`): địa chỉ `0xFEB5710` (khớp hoàn toàn lệnh nạp của hàm tại RVA `0x5DBAA6C`).
- **Build**: Cả [Il2CppDumper.CLI](file:///c:/Users/Tran%20Tuan%20Dung/Downloads/Il2CppDumper-master/Il2CppDumper-master/Il2CppDumper.CLI/bin/Release/net10.0/Il2CppDumper.exe) và [Il2CppDumper.GUI](file:///c:/Users/Tran%20Tuan%20Dung/Downloads/Il2CppDumper-master/Il2CppDumper-master/Il2CppDumper.GUI/bin/Release/net10.0-windows/Il2CppDumper%20GUI.exe) đều đã được biên dịch Release thành công 0 error.
