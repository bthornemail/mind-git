#!/usr/bin/env bash
set -e

echo "📱 Creating compressed mind-git package for Android..."

ANDROID_USER="u0_a201"
ANDROID_IP="10.208.42.148"
ANDROID_PORT="8022"

# Create minimal package
echo "📦 Creating minimal package..."
TEMP_DIR="/tmp/mind-git-minimal"
rm -rf "$TEMP_DIR"
mkdir -p "$TEMP_DIR"

# Essential files only
echo "📋 Copying essential files..."
cp package.json "$TEMP_DIR/"
cp package-lock.json "$TEMP_DIR/"
cp README.md "$TEMP_DIR/" 2>/dev/null || true
cp AGENTS.md "$TEMP_DIR/"
cp demo-working.json "$TEMP_DIR/" 2>/dev/null || true
cp simple-demo.json "$TEMP_DIR/" 2>/dev/null || true

# Source code (minimal)
mkdir -p "$TEMP_DIR/src"
cp -r src/* "$TEMP_DIR/src/"

# CLI tool
mkdir -p "$TEMP_DIR/bin"
cp -r bin/* "$TEMP_DIR/bin/" 2>/dev/null || true

# Create archive
echo "🗜️  Creating archive..."
cd /tmp
tar -czf mind-git-android.tar.gz -C mind-git-minimal .

# Transfer archive
echo "📤 Transferring archive..."
scp -P "$ANDROID_PORT" /tmp/mind-git-android.tar.gz "$ANDROID_USER@$ANDROID_IP:~/"

# Extract on Android
echo "📂 Extracting on Android..."
ssh -p "$ANDROID_PORT" "$ANDROID_USER@$ANDROID_IP" "
    cd ~/devops
    rm -rf mind-git
    mkdir -p mind-git
    cd mind-git
    tar -xzf ~/mind-git-android.tar.gz
    rm ~/mind-git-android.tar.gz
    echo '✅ mind-git extracted successfully'
"

# Transfer setup script
echo "📤 Transferring setup script..."
scp -P "$ANDROID_PORT" setup-android.sh "$ANDROID_USER@$ANDROID_IP:~/"

# Clean up
rm -rf "$TEMP_DIR" /tmp/mind-git-android.tar.gz

echo ""
echo "🎉 Transfer complete!"
echo ""
echo "📋 On Android device:"
echo "1. ssh -p $ANDROID_PORT $ANDROID_USER@$ANDROID_IP"
echo "2. bash ~/setup-android.sh"
echo "3. cd ~/devops/mind-git && ./test-android.sh"
echo ""
echo "🌟 mind-git ready for Android!"