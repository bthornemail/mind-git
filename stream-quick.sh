#!/bin/bash
echo "🎬 Starting CanvasL Quick Demo Stream"
echo "Title: CanvasL Magic: Visual to Code in 1ms"
echo "Duration: ~30 seconds"
echo ""

# Quick demo script
echo "🎨 CanvasL: Visual diagrams → Working code"
echo "========================================"
echo ""

# Create and compile canvas
echo '{"nodes":[{"id":"demo","content":"console.log(\"Hello CanvasL!\")"}],"edges":[]}' > quick.json
npx mind-git compile quick.json
echo "✅ Generated working code!"
echo "🚀 Install: npm install -g mind-git"
echo "🔗 github.com/bthornemail/mind-git"
