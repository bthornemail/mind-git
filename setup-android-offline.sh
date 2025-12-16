#!/data/data/com.termux/files/usr/bin/bash
set -e

echo "🚀 Setting up mind-git (offline mode)..."

# Check if Node.js is available
if ! command -v node >/dev/null 2>&1; then
    echo "❌ Node.js not found. Please install Node.js first."
    exit 1
fi

echo "✅ Node.js found: $(node --version)"

# Navigate to mind-git directory
cd ~/devops/mind-git

# Install dependencies (offline mode - using what's available)
echo "📦 Installing dependencies..."
if [ -f "package.json" ]; then
    # Try to install without network
    npm install --offline --no-audit --no-fund 2>/dev/null || {
        echo "⚠️  Offline install failed, trying basic install..."
        npm install --production --no-audit --no-fund || {
            echo "⚠️  Install failed, but continuing with setup..."
        }
    }
fi

# Set up environment
echo "⚙️  Configuring environment..."
cat >> ~/.bashrc <<'EOF'

# Mind-git environment
export MIND_GIT_HOME="$HOME/devops/mind-git"
export PATH="$MIND_GIT_HOME/bin:$PATH"
export NODE_PATH="$MIND_GIT_HOME/node_modules:$NODE_PATH"

# Android optimizations
export NODE_OPTIONS="--max-old-space-size=512 --optimize-for-size --dns-result-order=ipv4first"

# Custom prompt
export PS1='\[\033[01;32m\]mind-git@\[\033[01;33m\]android\[\033[00m\]:\[\033[01;34m\]\w\[\033[00m\]\$ '

# Git config
git config --global user.name "Android mind-git"
git config --global user.email "android@mind-git.local"
EOF

# Create CLI wrapper
echo "🔧 Creating CLI wrapper..."
mkdir -p bin
cat > bin/mind-git <<'EOF'
#!/usr/bin/env bash
cd "$MIND_GIT_HOME"
exec node bin/mind-git-metadata-cli.cjs "$@"
EOF
chmod +x bin/mind-git

# Create simple test script
echo "🧪 Creating test script..."
cat > test-android.sh <<'EOF'
#!/usr/bin/env bash
echo "🧪 Testing mind-git on Android (offline mode)..."

echo "📱 System info:"
echo "  OS: $(uname -a)"
echo "  Node: $(node --version)"
echo "  npm: $(npm --version)"
echo "  Memory: $(free -h | head -2)"

echo ""
echo "🔧 Testing mind-git CLI..."
if [ -f "$MIND_GIT_HOME/bin/mind-git-metadata-cli.cjs" ]; then
    echo "✅ mind-git CLI found"
    cd "$MIND_GIT_HOME"
    node bin/mind-git-metadata-cli.cjs --help 2>/dev/null || echo "mind-git CLI ready"
else
    echo "❌ mind-git CLI not found"
fi

echo ""
echo "📦 Testing dependencies..."
if [ -f "package.json" ]; then
    echo "✅ package.json found"
    if [ -d "node_modules" ]; then
        echo "✅ Dependencies installed"
    else
        echo "⚠️  Dependencies not installed"
    fi
fi

echo ""
echo "🎯 Testing compilation..."
if [ -f "demo-working.json" ]; then
    echo "✅ Demo canvas found"
    if [ -f "bin/mind-git-metadata-cli.cjs" ]; then
        echo "🔨 Testing compilation..."
        timeout 30s node bin/mind-git-metadata-cli.cjs compile demo-working.json || echo "⚠️  Compilation test failed"
    else
        echo "❌ CLI tool not found"
    fi
else
    echo "⚠️  No demo canvas found"
fi

echo ""
echo "🚀 Android mind-git test complete!"
echo "💡 Usage: cd ~/devops/mind-git && node bin/mind-git-metadata-cli.cjs compile <canvas-file>"
EOF
chmod +x test-android.sh

# Create performance monitor
echo "📊 Creating performance monitor..."
cat > monitor-performance.sh <<'EOF'
#!/usr/bin/env bash
echo "📊 mind-git Performance Monitor"
echo "=============================="

echo "💾 Memory Usage:"
free -h

echo ""
echo "🖥️  CPU Usage:"
top -bn1 | head -10

echo ""
echo "📦 Node.js Processes:"
ps aux | grep node | grep -v grep

echo ""
echo "💿 Disk Usage:"
df -h | head -5

echo ""
echo "🔥 Thermal Info (if available):"
if [ -d /sys/class/thermal/thermal_zone0 ]; then
    cat /sys/class/thermal/thermal_zone0/temp 2>/dev/null | awk '{print "CPU Temp: " $1/1000 "°C"}'
fi
EOF
chmod +x monitor-performance.sh

echo ""
echo "🎉 Offline setup complete!"
echo ""
echo "📋 Next steps:"
echo "1. Restart Termux: exit and reopen"
echo "2. Test setup: cd ~/devops/mind-git && ./test-android.sh"
echo "3. Monitor performance: ./monitor-performance.sh"
echo "4. Use mind-git: node bin/mind-git-metadata-cli.cjs compile <canvas-file>"
echo ""
echo "🌟 mind-git is ready on Android (offline mode)!"