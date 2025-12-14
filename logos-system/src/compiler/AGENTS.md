# 🤖 AGENTS.md - compiler

## 🎯 **Mission Scope**
**Layer**: 3 | **Category**: core-compiler | **Type**: compiler

---

## 🏗️ **Core Responsibilities**

### **Mathematical Foundation**
- [ ] **Polynomial Algebra**: Maintain F₂[x] operations
- [ ] **Identity Chain**: Preserve norm-preserving composition
- [ ] **Dimensional Constraints**: Respect Adams' theorem (1,2,4,8 dimensions)
- [ ] **Formal Verification**: Coq proofs for all operations

### **CanvasL Integration**
- [ ] **Pattern Recognition**: Extract CanvasL node types
- [ ] **AAL Transformation**: Convert to Assembly-Algebra Language
- [ ] **Spatial Processing**: Handle canvas coordinates and layout
- [ ] **AST Generation**: Create Abstract Syntax Trees

---

## 📁 **File Organization**

```
aal-compiler.ts
aal-integration.ts
ast/index.ts
canvas-compilation.test.ts
codegen/index.ts
index.ts
parser/index.ts
```

### **Key Files**
- **{{mainFile}}**: Main implementation
- **{{testFile}}**: Test suite
- **{{docFile}}**: Documentation

---

## 🧪 **Testing & Verification**

### **Unit Tests**
```bash
npm test {{testPattern}}
```

### **Mathematical Verification**
```bash
cd formal && make verify
```

### **Integration Tests**
```bash
npm run test:integration compiler
```

---

## 📊 **Status Matrix**

| Component | Status | Completeness | Verification |
|-----------|---------|--------------|--------------|
| **Core** | {{coreStatus}} | {{coreCompleteness}}% | {{coreVerification}} |
| **Tests** | {{testStatus}} | {{testCompleteness}}% | {{testVerification}} |

---

## 🔗 **Dependencies**

### **Input**
{{inputDependencies}}

### **Output**
{{outputDependencies}}

---

> **Last Updated**: 2025-12-14  
> **Status**: complete

---

*Auto-generated from metadata*