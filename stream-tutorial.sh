#!/bin/bash
echo "🎬 Starting CanvasL Tutorial Stream"
echo "Title: CanvasL Tutorial: Complete Visual Programming System"
echo "Duration: ~10 minutes"
echo ""

echo "🎨 CanvasL Complete Tutorial"
echo "==========================="
echo ""

echo "📐 Mathematical Foundation (1,400 years):"
echo "• 628 AD: Brahmagupta - Complex numbers"
echo "• 1748: Euler - Quaternions"
echo "• 1928: Degen - Octonions"
echo "• 1960: Adams - 8D limit theorem"
echo "• 2025: CanvasL - Complete implementation"
echo ""

echo "⚡ Live Demo: Polynomial Algebra"
node -e "
import { PolyF2 } from './logos-system/dist/core/polynomial/index.js';
const p1 = [true, false, true];
const p2 = [true, true];
console.log('p1:', PolyF2.toString(p1));
console.log('p2:', PolyF2.toString(p2));
console.log('Addition:', PolyF2.toString(PolyF2.add(p1, p2)));
"
echo ""

echo "🎨 Visual Canvas Creation"
cat > tutorial.json << 'INNER'
{
  "nodes": [
    {"id": "input", "content": "const data = [1,2,3]"},
    {"id": "process", "content": "const sum = data.reduce((a,b) => a+b)"},
    {"id": "output", "content": "console.log('Sum:', sum)"}
  ],
  "edges": [
    {"from": "input", "to": "process"},
    {"from": "process", "to": "output"}
  ]
}
INNER

echo "✅ Canvas created with 3 nodes, 2 edges"
echo ""

echo "⚡ Compilation Process"
npx mind-git compile tutorial.json
echo ""

echo "📄 Generated Code Analysis"
echo "Lines:" $(wc -l < output.js)
echo "Functions:" $(grep -c "function" output.js)
echo ""

echo "🚀 Installation & Usage"
echo "npm install -g mind-git"
echo "mind-git compile canvas.json"
echo ""

echo "🎯 CanvasL: Where Mathematics Meets Visual Programming!"
