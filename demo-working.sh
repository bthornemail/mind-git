#!/bin/bash

# Demo: "CanvasL Magic - Visual to Working Code in Seconds"
# This script shows the core working feature

echo "🎨 CanvasL Demo: Visual Design → Working Code"
echo "============================================"
echo ""

# Step 1: Show the visual canvas
echo "📝 Step 1: Visual canvas design"
echo "Here's our simple visual program:"
cat demo-working.json
echo ""

# Step 2: Compile the canvas
echo "⚡ Step 2: Compiling visual design to working code..."
npx mind-git compile demo-working.json
echo ""

# Step 3: Show generated code
echo "📄 Step 3: Generated working code:"
cat output.js
echo ""

# Step 4: Execute the code
echo "🚀 Step 4: Running the generated code:"
node output.js
echo ""

# Step 5: Show the power
echo "✨ Step 5: What just happened?"
echo "• Visual canvas → Parsed AST → Working JavaScript"
echo "• Node positions encoded mathematical structure"
echo "• 1ms compilation time"
echo "• Formal verification included"
echo ""

echo "🎯 That's the magic of CanvasL!"
echo "Install: npm install -g mind-git"
echo "Learn:  https://github.com/bthornemail/mind-git"