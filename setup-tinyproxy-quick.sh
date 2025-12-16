#!/data/data/com.termux/files/usr/bin/bash
set -e

echo "🌐 Quick tinyproxy setup for Android..."

# Install tinyproxy only
echo "📦 Installing tinyproxy..."
pkg install -y tinyproxy

# Create simple config
echo "⚙️  Creating configuration..."
mkdir -p ~/.tinyproxy

cat > ~/.tinyproxy/tinyproxy.conf <<'EOF'
Listen 0.0.0.0
Port 8888
Allow 10.0.0.0/8
Allow 192.168.0.0/16
Allow 172.16.0.0/12
Allow 127.0.0.1
Timeout 600
LogLevel Info
MaxClients 50
StartServers 2
EOF

# Start tinyproxy
echo "🚀 Starting tinyproxy..."
pkill -f tinyproxy 2>/dev/null || true
tinyproxy -c ~/.tinyproxy/tinyproxy.conf

echo "✅ tinyproxy started!"
echo "🌐 Proxy URL: http://$(ip route get 1.1.1.1 2>/dev/null | awk '{print $7}' || echo '0.0.0.0'):8888"