#!/bin/bash

# Demo: "CanvasL Magic - 30 Second Twitter Demo"
echo "🎨 CanvasL: Visual diagrams → Working code"
echo "========================================"
echo ""

# Quick canvas creation
echo "📝 Creating visual canvas..."
cat > quick.json << 'EOF'
{
  "nodes": [
    {"id": "hello", "content": "console.log('Hello CanvasL!')"}
  ],
  "edges": []
}
EOF

# Instant compilation
echo "⚡ Compiling to JavaScript..."
npx mind-git compile quick.json

# Show the magic
echo "✅ Generated working code!"
echo "🚀 npm install -g mind-git"
echo "🔗 github.com/bthornemail/mind-git"