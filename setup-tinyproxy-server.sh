#!/data/data/com.termux/files/usr/bin/bash
set -e

echo "🌐 Setting up tinyproxy on Android (Proxy Server)..."

# Check if we're on the correct device (should have internet)
echo "📱 Device info:"
echo "  IP: $(ip route get 1.1.1.1 2>/dev/null | awk '{print $7}' || echo 'No internet')"
echo "  Interface: $(ip route | grep default | awk '{print $5}' | head -1)"

# Update packages
echo "📦 Updating packages..."
pkg update -y
pkg upgrade -y

# Install tinyproxy
echo "🔧 Installing tinyproxy..."
pkg install -y tinyproxy

# Create tinyproxy configuration
echo "⚙️  Configuring tinyproxy..."
sudo mkdir -p /data/data/com.termux/files/usr/etc/tinyproxy 2>/dev/null || mkdir -p ~/.tinyproxy

# Create config file
cat > ~/.tinyproxy/tinyproxy.conf <<'EOF'
# tinyproxy configuration for Android
# Listen on all interfaces
Listen 0.0.0.0
Port 8888

# Allow connections from local network
Allow 10.0.0.0/8
Allow 192.168.0.0/16
Allow 172.16.0.0/12
Allow 127.0.0.1

# Basic settings
Timeout 600
DefaultErrorFile "/data/data/com.termux/files/usr/share/tinyproxy/default.html"
StatFile "/data/data/com.termux/files/usr/share/tinyproxy/stats.html"
Logfile "/data/data/com.termux/files/usr/tmp/tinyproxy.log"
LogLevel Info

# Performance settings for mobile
MaxClients 100
MinSpareServers 2
MaxSpareServers 5
StartServers 2

# Security
ViaProxy Yes
DisableViaHeader No
EOF

# If we can use sudo, install system-wide
if command -v sudo >/dev/null 2>&1; then
    echo "🔧 Installing system-wide configuration..."
    sudo cp ~/.tinyproxy/tinyproxy.conf /data/data/com.termux/files/usr/etc/tinyproxy/tinyproxy.conf
    CONFIG_FILE="/data/data/com.termux/files/usr/etc/tinyproxy/tinyproxy.conf"
else
    CONFIG_FILE="$HOME/.tinyproxy/tinyproxy.conf"
fi

# Create startup script
echo "🚀 Creating startup script..."
cat > ~/start-tinyproxy.sh <<'EOF'
#!/data/data/com.termux/files/usr/bin/bash
set -e

echo "🌐 Starting tinyproxy..."

# Kill any existing tinyproxy
pkill -f tinyproxy 2>/dev/null || true

# Start tinyproxy
if command -v sudo >/dev/null 2>&1; then
    sudo tinyproxy -c /data/data/com.termux/files/usr/etc/tinyproxy/tinyproxy.conf
else
    tinyproxy -c ~/.tinyproxy/tinyproxy.conf
fi

echo "✅ tinyproxy started on port 8888"
echo "📊 Status:"
ps aux | grep tinyproxy | grep -v grep || echo "❌ tinyproxy not running"

echo "🔍 Testing proxy..."
timeout 5 bash -c "</dev/tcp/0.0.0.0/8888" && echo "✅ Proxy is listening" || echo "❌ Proxy not accessible"

echo "🌐 Proxy ready for clients!"
echo "   Proxy URL: http://$(ip route get 1.1.1.1 2>/dev/null | awk '{print $7}' || ip route | grep default | awk '{print $7}'):8888"
EOF

chmod +x ~/start-tinyproxy.sh

# Create stop script
cat > ~/stop-tinyproxy.sh <<'EOF'
#!/data/data/com.termux/files/usr/bin/bash
echo "🛑 Stopping tinyproxy..."
pkill -f tinyproxy 2>/dev/null && echo "✅ tinyproxy stopped" || echo "⚠️  tinyproxy was not running"
EOF
chmod +x ~/stop-tinyproxy.sh

# Create status script
cat > ~/status-tinyproxy.sh <<'EOF'
#!/data/data/com.termux/files/usr/bin/bash
echo "📊 tinyproxy Status:"
echo "=================="

if pgrep -f tinyproxy >/dev/null; then
    echo "✅ tinyproxy is running"
    echo "📡 Process: $(pgrep -f tinyproxy)"
    echo "🌐 Port: 8888"
    echo "📍 IP: $(ip route get 1.1.1.1 2>/dev/null | awk '{print $7}' || ip route | grep default | awk '{print $7}')"
    
    if [ -f "/data/data/com.termux/files/usr/tmp/tinyproxy.log" ]; then
        echo "📝 Recent log entries:"
        tail -5 /data/data/com.termux/files/usr/tmp/tinyproxy.log 2>/dev/null || echo "No log file accessible"
    fi
else
    echo "❌ tinyproxy is not running"
    echo "🚀 Start with: ~/start-tinyproxy.sh"
fi
EOF
chmod +x ~/status-tinyproxy.sh

# Start tinyproxy
echo "🚀 Starting tinyproxy..."
~/start-tinyproxy.sh

echo ""
echo "🎉 tinyproxy setup complete!"
echo ""
echo "📋 Management commands:"
echo "  Start:   ~/start-tinyproxy.sh"
echo "  Stop:    ~/stop-tinyproxy.sh"
echo "  Status:  ~/status-tinyproxy.sh"
echo ""
echo "🌐 Proxy URL: http://$(ip route get 1.1.1.1 2>/dev/null | awk '{print $7}' || ip route | grep default | awk '{print $7}'):8888"
echo ""
echo "📱 Client devices can now use this proxy for internet access!"