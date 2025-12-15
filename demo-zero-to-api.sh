#!/bin/bash

# Demo: "From Zero to API in 60 Seconds"
# This script creates a complete working API from a visual canvas

echo "🚀 mind-git Demo: From Zero to API in 60 Seconds"
echo "================================================"
echo ""

# Step 1: Show the visual canvas
echo "📝 Step 1: Creating visual API design..."
cat demo-zero-to-api.json
echo ""

# Step 2: Compile the canvas to working code
echo "⚡ Step 2: Compiling visual design to working code..."
npx mind-git compile demo-zero-to-api.json
echo ""

# Step 3: Show the generated code
echo "📄 Step 3: Generated working code:"
cat output.js
echo ""

# Step 4: Start the server
echo "🌐 Step 4: Starting the server..."
node output.js &
SERVER_PID=$!
sleep 2
echo ""

# Step 5: Test the API
echo "🔍 Step 5: Testing the API..."
echo "Request: curl http://localhost:3000/users"
echo "Response:"
curl http://localhost:3000/users
echo ""

# Step 6: Clean up
echo "🧹 Step 6: Cleaning up..."
kill $SERVER_PID
echo ""

echo "✅ Complete! From visual design to working API in seconds!"
echo "Install: npm install -g mind-git"
echo "Learn:  https://github.com/bthornemail/mind-git"