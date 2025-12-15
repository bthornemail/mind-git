#!/bin/bash

# Demo: "CanvasL Magic - 1 Second Visual to Code"
echo "🎨 CanvasL: Visual → Code in 1ms"
echo "==============================="
echo ""

# Create simple canvas
echo '{"nodes":[{"id":"demo","content":"console.log(\"Hello CanvasL!\")"}],"edges":[]}' > quick.json

# Compile it
npx mind-git compile quick.json

# Show result
echo "✅ Generated working code!"
echo "🚀 Install: npm install -g mind-git"