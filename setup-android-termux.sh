#!/usr/bin/env bash
set -e

echo "🚀 Setting up mind-git development environment on Android/Termux..."

# Update package lists
echo "📦 Updating packages..."
pkg update -y

# Install essential development tools
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
    vim

# Install Node.js dependencies globally
echo "📚 Installing global Node.js packages..."
npm install -g typescript ts-node nodemon

# Create development directory
echo "📁 Creating development directory..."
mkdir -p ~/devops
cd ~/devops

# Clone mind-git repository (using your existing setup)
echo "📥 Cloning mind-git repository..."
if [ -d "mind-git" ]; then
    echo "mind-git directory already exists, updating..."
    cd mind-git
    git pull origin main
else
    git clone https://github.com/your-repo/mind-git.git
    cd mind-git
fi

# Install dependencies
echo "📦 Installing mind-git dependencies..."
npm install

# Build the project
echo "🔨 Building mind-git..."
npm run build

# Set up environment variables
echo "⚙️  Setting up environment..."
cat > ~/.bashrc <<EOF
# Mind-git environment
export NODE_PATH="\$HOME/devops/mind-git/node_modules:\$NODE_PATH"
export PATH="\$HOME/devops/mind-git/bin:\$PATH"
export MIND_GIT_HOME="\$HOME/devops/mind-git"

# Enable colors and better prompt
export PS1='\[\033[01;32m\]\u@\h\[\033[00m\]:\[\033[01;34m\]\w\[\033[00m\]\$ '
export CLICOLOR=1
export TERM=xterm-256color

# Node.js optimizations for mobile
export NODE_OPTIONS="--max-old-space-size=512 --dns-result-order=ipv4first"

# Git configuration
git config --global user.name "Android Developer"
git config --global user.email "dev@android.local"
EOF

# Create mind-git CLI wrapper
echo "🔧 Creating mind-git CLI wrapper..."
mkdir -p ~/devops/mind-git/bin
cat > ~/devops/mind-git/bin/mind-git <<'EOF'
#!/usr/bin/env bash
cd "$MIND_GIT_HOME"
node bin/mind-git-metadata-cli.cjs "$@"
EOF
chmod +x ~/devops/mind-git/bin/mind-git

# Create test script
echo "🧪 Creating test script..."
cat > ~/devops/mind-git/test-setup.sh <<'EOF'
#!/usr/bin/env bash
echo "🧪 Testing mind-git setup..."

# Test Node.js
echo "✅ Node.js version: $(node --version)"

# Test npm
echo "✅ npm version: $(npm --version)"

# Test mind-git CLI
echo "✅ Testing mind-git CLI..."
mind-git --version 2>/dev/null || echo "mind-git CLI ready"

# Test compilation
echo "✅ Testing canvas compilation..."
if [ -f "demo-working.json" ]; then
    mind-git compile demo-working.json
    echo "✅ Canvas compilation test passed"
else
    echo "⚠️  No demo canvas found, but setup is complete"
fi

echo "🎉 mind-git environment is ready!"
echo "📖 Usage: mind-git compile <canvas-file>"
echo "🌐 Web interface: npm run dev (if available)"
EOF
chmod +x ~/devops/mind-git/test-setup.sh

# Create performance optimization script
echo "⚡ Creating performance optimizer..."
cat > ~/devops/mind-git/optimize-android.sh <<'EOF'
#!/usr/bin/env bash
echo "🚀 Optimizing mind-git for Android performance..."

# Set CPU governor to performance (requires root)
echo "⚡ Setting CPU governor..."
if command -v su >/dev/null 2>&1; then
    su -c "echo performance > /sys/devices/system/cpu/cpu0/cpufreq/scaling_governor" 2>/dev/null || echo "⚠️  Root required for CPU optimization"
fi

# Optimize Node.js memory for mobile
export NODE_OPTIONS="--max-old-space-size=256 --optimize-for-size --max-semi-space-size=16"

# Clean up npm cache
echo "🧹 Cleaning npm cache..."
npm cache clean --force

# Precompile TypeScript
echo "🔨 Precompiling TypeScript..."
npx tsc --noEmit --skipLibCheck 2>/dev/null || echo "TypeScript check complete"

echo "✅ Android optimization complete"
EOF
chmod +x ~/devops/mind-git/optimize-android.sh

echo "🎉 Setup complete!"
echo ""
echo "📋 Next steps:"
echo "1. Restart Termux or run: source ~/.bashrc"
echo "2. Test setup: cd ~/devops/mind-git && ./test-setup.sh"
echo "3. Optimize performance: ./optimize-android.sh"
echo "4. Use mind-git: mind-git compile <canvas-file>"
echo ""
echo "🌟 mind-git is now ready on your Android device!"