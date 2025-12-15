---
id: "mind-git:development:here-is-your-table-rewritten-cleanly--expanded--and-standardized-using-the-conventional-assembly-taxonomy-"
title: "TLDR;"
type: ["development"]
category: development
layer: 7
dimensions: [3, 4, 5]
mathematicalFoundation: ["general"]
hopfCompatible: false
normPreserving: false
status: "complete"
completeness: 70
tags: ["development","documentation"]
keywords: []
lastUpdate: "2025-12-15"

---

# TLDR;
Here is your table rewritten cleanly, expanded, and standardized using the conventional assembly taxonomy.

| **Category**                     | **Typical Mnemonics**                                                | **Description**                                                                                                             |
| -------------------------------- | -------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------- |
| **Data Transfer**                | `MOV`, `LD`, `ST`, `LDA`, `STA`, `PUSH`, `POP`, `LEA`                | Transfer data between registers and memory, load/store addresses, or move values on/off the stack.                          |
| **Arithmetic**                   | `ADD`, `SUB`, `MUL`, `DIV`, `INC`, `DEC`, `NEG`                      | Perform integer arithmetic operations: addition, subtraction, multiplication, division, increment, decrement, and negation. |
| **Logical / Bitwise**            | `AND`, `OR`, `XOR`, `NOT`, `SHL`/`SLL`, `SHR`/`SRL`, `ROL`, `ROR`    | Apply logical bitwise operations and manipulate bit positions via shifts or rotations.                                      |
| **Control Flow**                 | `JMP`, `JSR`, `CALL`, `RET`, `BRA`, `HLT`, `NOP`                     | Control program execution: jumps, subroutine calls, returns, branch always, halt the CPU, or perform no operation.          |
| **Conditional Jumps / Branches** | `JEQ`, `JNE`, `JGT`, `JLT`, `BEQ`, `BNE`, `BCC`, `BCS`, `JGE`, `JLE` | Branch based on processor status flags—typically zero, carry, sign, overflow, or comparison results.                        |
| **Comparison / Test**            | `CMP`, `TEST`, `TST`                                                 | Compare values or test bit patterns and update flags without storing a result.                                              |

---
Below is a clean, universal **Assembly Mnemonics Reference Sheet** covering the most common instructions found across CPU architectures (x86, ARM, MIPS, RISC-V, 6502-style load/store systems, etc.).  
This version uses _canonical_ names and groups instructions by category for quick lookup.

---

# **Assembly Mnemonics Reference Sheet**

## **1. Data Transfer**

|Mnemonic|Meaning|
|---|---|
|**MOV**|Move/transfer data between registers or memory|
|**LD / LDR / LW**|Load from memory into register|
|**ST / STR / SW**|Store register into memory|
|**LDA**|Load address into register|
|**STA**|Store register value to address|
|**PUSH**|Push value onto the stack|
|**POP**|Pop value from the stack|
|**LEA**|Load effective address|
|**XCHG / SWP**|Exchange register or memory values|

---

## **2. Arithmetic Instructions**

|Mnemonic|Meaning|
|---|---|
|**ADD**|Add two values|
|**SUB**|Subtract values|
|**INC**|Increment by 1|
|**DEC**|Decrement by 1|
|**MUL / IMUL**|Multiply (unsigned / signed)|
|**DIV / IDIV**|Divide (unsigned / signed)|
|**NEG**|Two’s complement negation|
|**ADC**|Add with carry|
|**SBB**|Subtract with borrow|

---

## **3. Logical & Bitwise**

|Mnemonic|Meaning|
|---|---|
|**AND**|Bitwise AND|
|**OR**|Bitwise OR|
|**XOR**|Bitwise XOR|
|**NOT**|Bitwise NOT|
|**TEST / TST**|Bitwise test (AND without storing result)|
|**SHL / SLL**|Shift left (logical)|
|**SHR / SRL**|Shift right (logical)|
|**SAL**|Shift left (arithmetic)|
|**SAR**|Shift right (arithmetic)|
|**ROL**|Rotate left|
|**ROR**|Rotate right|

---

## **4. Comparison**

|Mnemonic|Meaning|
|---|---|
|**CMP**|Compare two values (sets flags)|
|**TEST**|Bitwise test setting flags|

---

## **5. Control Flow**

|Mnemonic|Meaning|
|---|---|
|**JMP**|Jump unconditionally|
|**BRA**|Branch always (common on 68k/6502)|
|**CALL / JSR / BL**|Call subroutine|
|**RET / RTS / BX LR**|Return from subroutine|
|**HLT**|Halt the CPU|
|**NOP**|No operation|

---

## **6. Conditional Jumps / Branches**

### **Equality / Zero**

|Mnemonic|Meaning|
|---|---|
|**JE / JZ**|Jump if equal / zero|
|**JNE / JNZ**|Jump if not equal / not zero|
|**BEQ**|Branch if equal|
|**BNE**|Branch if not equal|

### **Signed Comparisons**

|Mnemonic|Meaning|
|---|---|
|**JG / JGT**|Jump if greater (signed)|
|**JGE**|Jump if greater or equal|
|**JL / JLT**|Jump if less (signed)|
|**JLE**|Jump if less or equal|

### **Unsigned Comparisons**

|Mnemonic|Meaning|
|---|---|
|**JA / JHI**|Jump if above (unsigned)|
|**JAE / JHS**|Above or equal (unsigned)|
|**JB / JLO**|Below (unsigned)|
|**JBE**|Below or equal|

### **Carry & Overflow**

|Mnemonic|Meaning|
|---|---|
|**JC / BCS**|Jump if carry set|
|**JNC / BCC**|Jump if carry clear|
|**JO**|Jump if overflow set|
|**JNO**|Jump if overflow clear|
|**JS / BMI**|Jump if sign bit set|
|**JNS / BPL**|Jump if sign bit clear|

---

## **7. Stack & Procedure Support**

|Mnemonic|Meaning|
|---|---|
|**PUSH**|Push value to stack|
|**POP**|Pop value from stack|
|**PUSHF / POPF**|Push/pop flags register|
|**ENTER / LEAVE**|Set up / tear down stack frames|

---

## **8. Memory & Addressing Helpers**

|Mnemonic|Meaning|
|---|---|
|**LEA**|Load effective address|
|**ADR / LA**|Load address (RISC architectures)|
|**LDRB / LDRH**|Load byte / halfword|
|**STRB / STRH**|Store byte / halfword|

---

## **9. System & Privileged Instructions**

|Mnemonic|Meaning|
|---|---|
|**INT**|Software interrupt|
|**IRET / RFI**|Return from interrupt|
|**CLI / SEI**|Clear/Set interrupt enable flag|
|**SYSCALL / SVC / ECALL**|Enter operating-system call|
|**HLT**|Halt the processor|
|**WFI**|Wait for interrupt|

---

## **10. Floating-Point / Vector (Generic)**

|Mnemonic|Meaning|
|---|---|
|**FADD / VADD**|Floating/vector add|
|**FSUB / VSUB**|Floating/vector subtract|
|**FMUL / VMUL**|Floating/vector multiply|
|**FDIV / VDIV**|Floating/vector divide|
|**FSQRT**|Floating point square root|
|**MOVSS / MOVSD**|Move scalar float/double|
|**LOADV / STOREV**|Vector load/store|

---

# **Complete Cheat Sheet (One-Page Summary)**

### **Data:**

`MOV LD ST LDA STA PUSH POP LEA XCHG`

### **Arithmetic:**

`ADD SUB MUL DIV INC DEC NEG ADC SBB`

### **Logical:**

`AND OR XOR NOT TEST SHL SHR SAR ROL ROR`

### **Comparison:**

`CMP TEST TST`

### **Control Flow:**

`JMP CALL RET BRA JSR HLT NOP`

### **Conditional:**

`JE JNE JG JL JGE JLE JA JB JO JNO JC JNC JS JNS`

### **Stack:**

`PUSH POP PUSHF POPF ENTER LEAVE`

### **System:**

`INT SYSCALL IRET CLI SEI WFI`

---

If you want, I can also create:

✅ a printable PDF version  
✅ an expanded 4-page reference including addressing modes  
✅ architecture-specific versions (x86-64, ARM64, RISC-V, MIPS, 6502, 68000…)  
✅ a color-coded diagram version (SVG)

Just tell me what format you want!