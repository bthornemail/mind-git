---
id: "mind-git:examples:readme"
title: "Advanced CanvasL Examples"
type: ["examples","tutorial"]
category: examples
layer: 4
dimensions: [0, 1, 9]
mathematicalFoundation: ["polynomial-algebra"]
hopfCompatible: false
normPreserving: false
status: "complete"
completeness: 80
tags: ["examples","canvasl","mathematics","compiler","ast","algebra"]
keywords: ["canvasl","aal","ast","compiler","algebra","javascript"]
lastUpdate: "2025-12-15"

---

# Advanced CanvasL Examples

This directory contains advanced examples demonstrating the enhanced dynamic node parsing capabilities of the CanvasL visual compiler.

## Enhanced Features

### Dynamic Node Classification
The compiler now automatically detects and classifies nodes based on their content patterns:

- **LOOP**: Detects `for`, `while`, `do` loops and iteration patterns
- **CONDITION**: Detects `if`, `else`, `switch`, case statements and comparison operators
- **FUNCTION**: Detects function definitions using `function`, `const`, `let`, `var` with parameters
- **CALL**: Detects function calls and method invocations
- **RETURN**: Detects `return`, `yield`, `break`, `continue` statements
- **PARAMETER**: Detects parameter and argument declarations
- **VARIABLE**: Detects variable declarations with `let`, `var`
- **CONSTANT**: Detects constant declarations with `const`, `#define`, `final`

### Operand Extraction
The parser automatically extracts operands from nodes:
- Function names and parameters
- Function call targets and arguments  
- Variables in conditional expressions
- Variable names and assigned values
- Loop variables and conditions

## Examples

### 1. loops.json
Demonstrates loop structures with feedback edges for iteration.
- **Nodes**: 6 (observer, initializer, condition, loop body, increment, terminator)
- **Edges**: 5 (control flow, feedback loop)
- **Features**: BackPropagate node for condition, feedback edge for loop iteration

### 2. conditionals.json  
Shows conditional branching with true/false paths.
- **Nodes**: 7 (observer, start, input, condition, true branch, false branch, merge)
- **Edges**: 6 (control flow, conditional branching)
- **Features**: Condition node with comparison, parallel branches, merge point

### 3. functions.json
Illustrates function definitions and calls with parameters.
- **Nodes**: 8 (observer, function definition, parameters, function body, main, call, output)
- **Edges**: 6 (function structure, parameter passing, invocation)
- **Features**: Function definition with parameters, function call with arguments

## Usage

Compile any example with the CLI tool:
```bash
npx mind-git compile examples/advanced/loops.json
npx mind-git compile examples/advanced/conditionals.json  
npx mind-git compile examples/advanced/functions.json
```

## Technical Details

### Enhanced Parser Logic
The parser uses regex patterns and content analysis to dynamically classify nodes:

```javascript
// Loop detection
if (/for\s*\(/.test(content) || /while\s*\(/.test(content)) {
  return NodeClassification.LOOP;
}

// Function detection  
if (/function\s+\w+\s*\(/.test(content)) {
  return NodeClassification.FUNCTION;
}

// Condition detection
if (/if\s*\(/.test(content) || content.includes('<') || content.includes('>')) {
  return NodeClassification.CONDITION;
}
```

### Dimensional Mapping
Dynamic nodes are mapped to appropriate mathematical dimensions:
- LOOP → D5_Concurrency (loops involve concurrency)
- CONDITION → D3_MemoryModel (conditions affect memory flow)
- FUNCTION → D4_ControlStack (functions use call stack)
- CALL → D4_ControlStack (function calls use stack)
- VARIABLE → D1_Functional (variables are functional)
- CONSTANT → D0_PureAlgebra (constants are pure)

### Operand Extraction
The parser extracts meaningful operands from node content for use in code generation and dependency analysis.

## Integration with CanvasL

These examples work seamlessly with the existing CanvasL compiler pipeline:
1. **Canvas JSON** → Enhanced Parser → **AST** → AAL → **Executable Code**
2. Dynamic classifications complement existing CanvasL node types
3. Operand extraction improves dependency analysis
4. Dimensional mapping maintains mathematical integrity

The enhanced parser maintains full backward compatibility with existing CanvasL examples while adding powerful new dynamic parsing capabilities.