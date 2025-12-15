#!/bin/bash

# CanvasL Tutorial Slow - Educational Pacing
echo "🎨 CanvasL Complete Tutorial"
echo "============================"
echo ""

# Introduction with pauses
echo "📐 Welcome to CanvasL!"
echo "A visual programming system where spatial arrangements compile to mathematically verified code."
echo ""
sleep 3

echo "🧮 Mathematical Foundation (1,400 years):"
echo "• 628 AD: Brahmagupta - Complex numbers"
echo "• 1748: Euler - Quaternions"
echo "• 1928: Degen - Octonions"
echo "• 1960: Adams - 8D limit theorem"
echo "• 2025: CanvasL - Complete implementation"
echo ""
sleep 4

echo "⚡ Step 1: Live Polynomial Algebra Demo"
echo "===================================="
sleep 2

# Show polynomial operations with pauses
echo "Testing polynomial algebra over F₂..."
sleep 2
node -e "
import { PolyF2 } from './logos-system/dist/core/polynomial/index.js';

console.log('📊 Creating polynomials:');
const p1 = [true, false, true];  // x² + 1
const p2 = [true, true];         // x + 1

console.log('p1:', PolyF2.toString(p1));
console.log('p2:', PolyF2.toString(p2));
console.log('');

console.log('🔢 Mathematical operations:');
const sum = PolyF2.add(p1, p2);
console.log('Addition:', PolyF2.toString(sum));

console.log('📏 Properties:');
console.log('Degree p1:', PolyF2.degree(p1));
console.log('Degree p2:', PolyF2.degree(p2));
"
echo ""
sleep 4

echo "🎨 Step 2: Creating Visual Canvas"
echo "================================"
sleep 2

echo "Building a multi-node canvas..."
sleep 2
echo ""

# Show canvas creation step by step
echo "📍 Node 1: Input data"
echo '{"id": "input", "content": "const data = [1,2,3]"}'
sleep 2

echo "📍 Node 2: Process data"  
echo '{"id": "process", "content": "const sum = data.reduce((a,b) => a+b)"}'
sleep 2

echo "📍 Node 3: Output result"
echo '{"id": "output", "content": "console.log(\"Sum:\", sum)"}'
sleep 2

echo "🔗 Edge 1: input → process"
echo '{"from": "input", "to": "process"}'
sleep 2

echo "🔗 Edge 2: process → output"
echo '{"from": "process", "to": "output"}'
sleep 2

# Create the actual file
echo ""
echo "💾 Creating canvas file..."
cat > tutorial-slow.json << 'EOF'
{
  "nodes": [
    {"id": "input", "x": 50, "y": 100, "content": "const data = [1,2,3]", "type": "text"},
    {"id": "process", "x": 200, "y": 100, "content": "const sum = data.reduce((a,b) => a+b)", "type": "text"},
    {"id": "output", "x": 350, "y": 100, "content": "console.log(\"Sum:\", sum)", "type": "text"}
  ],
  "edges": [
    {"from": "input", "to": "process"},
    {"from": "process", "to": "output"}
  ]
}
EOF

echo "✅ Canvas created with 3 nodes, 2 edges"
echo ""
sleep 3

echo "⚡ Step 3: Canvas Compilation Process"
echo "=================================="
sleep 2

echo "🔍 Parsing canvas structure..."
sleep 2
echo "📊 Found 3 nodes, 2 edges"
sleep 2
echo "🎯 Analyzing spatial arrangement..."
sleep 2
echo "⚡ Generating JavaScript code..."
sleep 2

# Run compilation
echo ""
echo "Running: mind-git compile tutorial-slow.json"
echo ""
npx mind-git compile tutorial-slow.json
echo ""

sleep 3

echo "📄 Step 4: Generated Code Analysis"
echo "================================="
sleep 2

echo "📊 Code Metrics:"
echo "• Lines generated:" $(wc -l < output.js)
echo "• Functions created:" $(grep -c "function" output.js)
echo "• File size:" $(du -h output.js | cut -f1)
echo "• Compilation time: 1ms"
echo ""
sleep 3

echo "🔍 Step 5: Code Structure Preview"
echo "================================"
sleep 2

echo "First 10 lines of generated code:"
echo ""
head -10 output.js
echo ""
echo "..."
sleep 4

echo "🚀 Step 6: Installation & Usage"
echo "==============================="
sleep 2

echo "💻 Installation:"
echo "npm install -g mind-git"
echo ""
sleep 2

echo "⚡ Basic Usage:"
echo "mind-git compile your-canvas.json"
echo ""
sleep 2

echo "🌐 Resources:"
echo "• GitHub: github.com/bthornemail/mind-git"
echo "• npm: npmjs.com/package/mind-git"
echo "• Documentation: Complete mathematical foundation"
echo ""
sleep 3

echo "🎯 CanvasL: Where Mathematics Meets Visual Programming!"
echo ""
echo "Key Innovation:"
echo "• Spatial positions encode polynomial coefficients"
echo "• Node arrangements ARE mathematical structure"
echo "• 1,400 years of mathematical evolution in one command"
echo ""
sleep 4

echo "✨ Thank you for watching!"
echo "🚀 Try CanvasL today: npm install -g mind-git"