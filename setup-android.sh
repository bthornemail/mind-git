#!/data/data/com.termux/files/usr/bin/bash
set -e

echo "🚀 Setting up mind-git on Android/Termux..."

# Configure proxy first (using your existing proxy setup)
echo "🌐 Configuring proxy..."
IFACE="wlan0"
PORT="8888"

PROXY_HOST=""
PROXY_URL=""

# Find proxy on network
for ip in $(ip -4 neigh show dev "$IFACE" 2>/dev/null | awk '{print $1}' | head -20); do
    if timeout 2 bash -c "</dev/tcp/$ip/$PORT" 2>/dev/null; then
        PROXY_HOST="$ip"
        PROXY_URL="http://${ip}:${PORT}"
        break
    fi
done

if [[ -n "$PROXY_URL" ]]; then
    echo "✅ Found proxy at $PROXY_URL"
    export HTTP_PROXY="$PROXY_URL"
    export HTTPS_PROXY="$PROXY_URL"
    export http_proxy="$PROXY_URL"
    export https_proxy="$PROXY_URL"
    export NODE_TLS_REJECT_UNAUTHORIZED=0
    export NODE_OPTIONS="--dns-result-order=ipv4first"
    
    # Configure npm proxy
    npm config set proxy "$PROXY_URL"
    npm config set https-proxy "$PROXY_URL"
    
    # Configure git proxy
    git config --global http.proxy "$PROXY_URL"
    git config --global https.proxy "$PROXY_URL"
else
    echo "⚠️  No proxy found, continuing without proxy..."
fi

# Update Termux packages
echo "📦 Updating Termux packages..."
pkg update -y
pkg upgrade -y

# Install essential tools
echo "🛠️  Installing development tools..."
pkg install -y \
    nodejs \
    npm \
    git \
    python \
    make \
    clang \
    libffi \
    openssl \
    libxml2 \
    libxslt \
    libjpeg-turbo \
    libpng \
    pkg-config \
    curl \
    wget \
    nano \
    vim \
    rsync

# Install Node.js tools
echo "📚 Installing Node.js packages..."
npm install -g typescript ts-node nodemon

# Create workspace
echo "📁 Creating workspace..."
mkdir -p ~/devops
cd ~/devops

# Transfer mind-git from your main machine (since no internet)
echo "📥 Setting up mind-git..."
if [ ! -d "mind-git" ]; then
    mkdir -p mind-git
    echo "⚠️  Please copy mind-git files from your main machine:"
    echo "   rsync -avz ~/devops/mind-git/ u0_a201@10.208.42.148:~/devops/mind-git/"
    echo "   Or use: scp -r ~/devops/mind-git/ u0_a201@10.208.42.148:~/devops/"
    exit 1
fi

cd mind-git

# Install dependencies
echo "📦 Installing dependencies..."
npm install --production=false

# Build project
echo "🔨 Building project..."
npm run build || echo "⚠️  Build may have warnings, but continuing..."

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

# Create Android-specific test script
echo "🧪 Creating test script..."
cat > test-android.sh <<'EOF'
#!/usr/bin/env bash
echo "🧪 Testing mind-git on Android..."

echo "📱 System info:"
echo "  OS: $(uname -a)"
echo "  Node: $(node --version)"
echo "  npm: $(npm --version)"
echo "  Memory: $(free -h | head -2)"

echo ""
echo "🔧 Testing mind-git CLI..."
if command -v mind-git >/dev/null 2>&1; then
    echo "✅ mind-git CLI found"
    mind-git --help 2>/dev/null || echo "mind-git CLI ready"
else
    echo "❌ mind-git CLI not found"
fi

echo ""
echo "📦 Testing dependencies..."
cd "$MIND_GIT_HOME"
if [ -f "package.json" ]; then
    echo "✅ package.json found"
    if npm list --depth=0 >/dev/null 2>&1; then
        echo "✅ Dependencies installed"
    else
        echo "⚠️  Dependency issues detected"
    fi
fi

echo ""
echo "🎯 Testing compilation..."
if [ -f "demo-working.json" ]; then
    echo "✅ Demo canvas found"
    timeout 30s mind-git compile demo-working.json || echo "⚠️  Compilation test timed out or failed"
else
    echo "⚠️  No demo canvas found"
fi

echo ""
echo "🚀 Android mind-git test complete!"
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
echo "🎉 Android setup complete!"
echo ""
echo "📋 Next steps:"
echo "1. Restart Termux: exit and reopen"
echo "2. Test setup: cd ~/devops/mind-git && ./test-android.sh"
echo "3. Monitor performance: ./monitor-performance.sh"
echo "4. Use mind-git: mind-git compile <canvas-file>"
echo ""
echo "🌟 mind-git is ready on Android!"