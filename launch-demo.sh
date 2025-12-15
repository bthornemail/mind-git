#!/bin/bash

# Launch script for mind-git 2.5D visualizer demo
# Automatically opens the visualizer in your browser

set -e

echo "======================================"
echo "mind-git 2.5D Visualizer"
echo "Interactive Spatial Programming Demo"
echo "======================================"
echo ""

# Check if we're in the right directory
if [ ! -d "mind-git-demo" ]; then
  echo "Error: mind-git-demo directory not found!"
  echo "Please run this script from the mind-git root directory."
  exit 1
fi

cd mind-git-demo

# Check if node_modules exists
if [ ! -d "node_modules" ]; then
  echo "📦 Installing dependencies..."
  npm install
  echo ""
fi

echo "🚀 Launching visualizer..."
echo ""
echo "The demo will open at http://localhost:3000"
echo ""
echo "Features:"
echo "  • Interactive 3D node visualization"
echo "  • Drag, zoom, rotate controls"
echo "  • Real-time canvas compilation"
echo "  • Multi-language code generation"
echo ""
echo "Press Ctrl+C to stop the server"
echo ""
echo "======================================"
echo ""

# Start the dev server
npm start
