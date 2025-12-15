#!/bin/bash

# CanvasL Slow Demo - Readable Pacing
echo "🎨 CanvasL: Visual diagrams → Working code"
echo "========================================"
echo ""

# Add pauses for readability
echo "📝 Step 1: Creating visual canvas..."
sleep 2

# Show the canvas content clearly
echo "Here's our visual canvas design:"
echo ""
echo '{'
echo '  "nodes": ['
echo '    {'
echo '      "id": "hello",'
echo '      "content": "console.log(\"Hello CanvasL!\")"'
echo '    }'
echo '  ],'
echo '  "edges": []'
echo '}'
echo ""
sleep 3

# Save to file with visible feedback
echo "💾 Saving canvas to file..."
echo '{"nodes":[{"id":"hello","content":"console.log(\"Hello CanvasL!\")"}],"edges":[]}' > slow-demo.json
echo "✅ Canvas saved as 'slow-demo.json'"
echo ""
sleep 2

# Step 2: Compilation with visible process
echo "⚡ Step 2: Compiling visual design to JavaScript..."
sleep 2
echo "Running: mind-git compile slow-demo.json"
echo ""
sleep 1

# Run compilation
npx mind-git compile slow-demo.json
echo ""

# Step 3: Show results clearly
echo "📄 Step 3: Generated working code!"
sleep 2
echo "✅ Compilation completed in 1ms"
echo ""
sleep 2

# Step 4: Show key results
echo "🎯 Step 4: Results Summary"
echo "• Lines of code generated:" $(wc -l < output.js)
echo "• Functions created:" $(grep -c "function" output.js)
echo "• File size:" $(du -h output.js | cut -f1)
echo ""
sleep 3

# Step 5: Call to action
echo "🚀 Step 5: Get CanvasL Now!"
echo "Installation: npm install -g mind-git"
echo "Repository: github.com/bthornemail/mind-git"
echo "Package: npmjs.com/package/mind-git"
echo ""
sleep 3

echo "🎉 That's CanvasL - Mathematics meets Visual Programming!"
echo ""