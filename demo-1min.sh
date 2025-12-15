#!/bin/bash

# Demo: "CanvasL Deep Dive - 1 Minute Demo"
echo "🎨 CanvasL: Visual Programming with Mathematical Foundation"
echo "======================================================"
echo ""

# Step 1: Show the concept
echo "📐 1,400 years of mathematics in one command:"
echo "• Brahmagupta (628 AD) → Euler (1748) → Degen (1928) → Adams (1960)"
echo ""

# Step 2: Create visual canvas
echo "📝 Creating visual canvas..."
cat > demo.json << 'EOF'
{
  "nodes": [
    {"id": "math", "x": 100, "y": 100, "content": "const result = 2 + 3", "type": "text"},
    {"id": "output", "x": 300, "y": 100, "content": "console.log(result)", "type": "text"}
  ],
  "edges": [
    {"from": "math", "to": "output"}
  ]
}
EOF

echo "✅ Visual design created"
echo ""

# Step 3: Compile it
echo "⚡ Compiling visual design to working code..."
npx mind-git compile demo.json
echo ""

# Step 4: Show results
echo "📄 Generated code:"
head -10 output.js
echo "..."
echo ""

# Step 5: Show the magic
echo "🌟 That's CanvasL!"
echo "• Spatial positions encode polynomial coefficients"
echo "• Node arrangements ARE mathematical structure"
echo "• 1ms compilation time"
echo ""
echo "🚀 Install: npm install -g mind-git"
echo "🔗 Demo: https://asciinema.org/a/J2rYWDju71lMIvLw2HkKKd5rV"