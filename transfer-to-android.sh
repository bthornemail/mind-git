#!/usr/bin/env bash
set -e

echo "📱 Transferring mind-git to Android device..."

ANDROID_USER="u0_a201"
ANDROID_IP="10.208.42.148"
ANDROID_PORT="8022"
ANDROID_PATH="~/devops/mind-git"

# Check if Android device is reachable
echo "🔍 Checking connection to Android device..."
if ! ssh -p "$ANDROID_PORT" "$ANDROID_USER@$ANDROID_IP" "echo 'Connection successful'" 2>/dev/null; then
    echo "❌ Cannot connect to Android device at $ANDROID_IP:$ANDROID_PORT"
    echo "   Make sure SSH is running on Android and the device is accessible"
    exit 1
fi

echo "✅ Connection successful"

# Create mind-git directory on Android
echo "📁 Creating mind-git directory on Android..."
ssh -p "$ANDROID_PORT" "$ANDROID_USER@$ANDROID_IP" "mkdir -p ~/devops/mind-git"

# Transfer files (excluding node_modules and other large directories)
echo "📤 Transferring mind-git files..."

# Create a temporary directory with only essential files
TEMP_DIR="/tmp/mind-git-android"
rm -rf "$TEMP_DIR"
mkdir -p "$TEMP_DIR"

# Copy essential files (excluding large directories)
echo "📋 Preparing files for transfer..."
cp -r src "$TEMP_DIR/"
cp -r bin "$TEMP_DIR/" 2>/dev/null || true
cp -r logos-system "$TEMP_DIR/"
cp -r metadata "$TEMP_DIR/"
cp -r formal "$TEMP_DIR/" 2>/dev/null || true
cp -r docs "$TEMP_DIR/" 2>/dev/null || true
cp -r dev-docs "$TEMP_DIR/" 2>/dev/null || true
cp package*.json "$TEMP_DIR/"
cp README.md "$TEMP_DIR/" 2>/dev/null || true
cp LICENSE "$TEMP_DIR/" 2>/dev/null || true
cp AGENTS.md "$TEMP_DIR/"
cp ARCHITECTURE.md "$TEMP_DIR/" 2>/dev/null || true

# Create demo files (small ones only)
cp demo-working.json "$TEMP_DIR/" 2>/dev/null || true
cp simple-demo.json "$TEMP_DIR/" 2>/dev/null || true
cp quick.json "$TEMP_DIR/" 2>/dev/null || true

# Transfer the prepared directory
echo "📤 Transferring prepared files..."
scp -r -P "$ANDROID_PORT" "$TEMP_DIR"/* "$ANDROID_USER@$ANDROID_IP:$ANDROID_PATH/"

# Clean up
rm -rf "$TEMP_DIR"

# Transfer setup script
echo "📤 Transferring setup script..."
scp -P "$ANDROID_PORT" setup-android.sh "$ANDROID_USER@$ANDROID_IP:~/"

echo ""
echo "🎉 Transfer complete!"
echo ""
echo "📋 Next steps on Android device:"
echo "1. SSH to Android: ssh -p $ANDROID_PORT $ANDROID_USER@$ANDROID_IP"
echo "2. Run setup: bash setup-android.sh"
echo "3. Test: cd ~/devops/mind-git && ./test-android.sh"
echo ""
echo "🌟 mind-git will be ready on your Android device!"