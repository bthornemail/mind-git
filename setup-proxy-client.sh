#!/data/data/com.termux/files/usr/bin/bash
set -e

echo "🔍 Setting up proxy client on Android..."

# Network interface to scan
IFACE="wlan0"
PORT="8888"

echo "🌐 Scanning network for tinyproxy on $IFACE..."

PROXY_HOST=""
PROXY_URL=""

# Get network range
NETWORK_RANGE=$(ip route | grep "$IFACE" | grep -E '^[0-9]' | awk '{print $1}' | cut -d'.' -f1-3)
echo "📡 Network range: ${NETWORK_RANGE}.0/24"

# Scan for proxy on the network
echo "🔍 Scanning for proxy servers..."
for i in {1..254}; do
    IP="${NETWORK_RANGE}.${i}"
    if timeout 1 bash -c "</dev/tcp/$IP/$PORT" 2>/dev/null; then
        PROXY_HOST="$IP"
        PROXY_URL="http://${IP}:${PORT}"
        echo "✅ Found proxy at $PROXY_URL"
        break
    fi
done

# If not found in range, try known IPs
if [[ -z "$PROXY_URL" ]]; then
    echo "🔍 Trying known proxy servers..."
    KNOWN_IPS=("10.208.42.20" "10.208.42.5" "192.168.1.1" "192.168.0.1")
    
    for IP in "${KNOWN_IPS[@]}"; do
        if timeout 2 bash -c "</dev/tcp/$IP/$PORT" 2>/dev/null; then
            PROXY_HOST="$IP"
            PROXY_URL="http://${IP}:${PORT}"
            echo "✅ Found proxy at $PROXY_URL"
            break
        fi
    done
fi

if [[ -z "$PROXY_URL" ]]; then
    echo "❌ Could not find tinyproxy on port $PORT"
    echo "💡 Make sure:"
    echo "   1. Proxy server is running on another device"
    echo "   2. Both devices are on the same network"
    echo "   3. Port $PORT is not blocked by firewall"
    exit 1
fi

echo "🌐 Configuring proxy: $PROXY_URL"

# Create environment configuration
echo "⚙️  Setting up environment variables..."
cat > ~/.proxy-env.sh <<EOF
#!/data/data/com.termux/files/usr/bin/bash
export HTTP_PROXY="$PROXY_URL"
export HTTPS_PROXY="$PROXY_URL"
export http_proxy="$PROXY_URL"
export https_proxy="$PROXY_URL"
export FTP_PROXY="$PROXY_URL"
export ftp_proxy="$PROXY_URL"
export NO_PROXY="localhost,127.0.0.1,::1,10.0.0.0/8,192.168.0.0/16,172.16.0.0/12"
export no_proxy="\$NO_PROXY"
export NODE_TLS_REJECT_UNAUTHORIZED=0
export NODE_OPTIONS="--dns-result-order=ipv4first"

echo "🌐 Proxy configured: $PROXY_URL"
EOF

chmod +x ~/.proxy-env.sh

# Configure npm
echo "📦 Configuring npm..."
npm config set proxy "$PROXY_URL"
npm config set https-proxy "$PROXY_URL"
npm config set registry "http://registry.npmjs.org/"

# Configure git
echo "📥 Configuring git..."
git config --global http.proxy "$PROXY_URL"
git config --global https.proxy "$PROXY_URL"

# Configure wget
echo "🌐 Configuring wget..."
cat > ~/.wgetrc <<EOF
use_proxy = on
http_proxy = $PROXY_URL
https_proxy = $PROXY_URL
ftp_proxy = $PROXY_URL
no_proxy = localhost,127.0.0.1,::1
EOF

# Configure curl
echo "🌐 Configuring curl..."
cat > ~/.curlrc <<EOF
proxy = $PROXY_URL
noproxy = localhost,127.0.0.1,::1
insecure
EOF

# Add to bashrc
echo "📝 Adding to bashrc..."
if ! grep -q "proxy-env.sh" ~/.bashrc; then
    echo "" >> ~/.bashrc
    echo "# Auto-load proxy configuration" >> ~/.bashrc
    echo "if [ -f ~/.proxy-env.sh ]; then" >> ~/.bashrc
    echo "    source ~/.proxy-env.sh" >> ~/.bashrc
    echo "fi" >> ~/.bashrc
fi

# Create test script
echo "🧪 Creating test script..."
cat > ~/test-proxy.sh <<'EOF'
#!/data/data/com.termux/files/usr/bin/bash
echo "🧪 Testing proxy configuration..."

echo "📡 Proxy settings:"
echo "  HTTP_PROXY: $HTTP_PROXY"
echo "  HTTPS_PROXY: $HTTPS_PROXY"

echo ""
echo "🌐 Testing internet connectivity..."

# Test with curl
echo "📡 Testing with curl..."
if timeout 10 curl -s -I http://httpbin.org/ip >/dev/null 2>&1; then
    echo "✅ HTTP connection successful"
    echo "🌍 External IP: $(timeout 10 curl -s http://httpbin.org/ip 2>/dev/null || echo 'Failed to get IP')"
else
    echo "❌ HTTP connection failed"
fi

# Test with wget
echo "📥 Testing with wget..."
if timeout 10 wget -q --spider http://example.com 2>/dev/null; then
    echo "✅ wget connection successful"
else
    echo "❌ wget connection failed"
fi

# Test npm
echo "📦 Testing npm..."
if timeout 15 npm ping >/dev/null 2>&1; then
    echo "✅ npm registry accessible"
else
    echo "❌ npm registry not accessible"
fi

# Test git
echo "📥 Testing git..."
if timeout 10 git ls-remote https://github.com >/dev/null 2>&1; then
    echo "✅ git remote access successful"
else
    echo "❌ git remote access failed"
fi

echo ""
echo "🎉 Proxy test complete!"
EOF
chmod +x ~/test-proxy.sh

# Create enable/disable scripts
cat > ~/enable-proxy.sh <<'EOF'
#!/data/data/com.termux/files/usr/bin/bash
if [ -f ~/.proxy-env.sh ]; then
    source ~/.proxy-env.sh
    echo "✅ Proxy enabled"
else
    echo "❌ Proxy configuration not found"
fi
EOF
chmod +x ~/enable-proxy.sh

cat > ~/disable-proxy.sh <<'EOF'
#!/data/data/com.termux/files/usr/bin/bash
unset HTTP_PROXY HTTPS_PROXY http_proxy https_proxy FTP_PROXY ftp_proxy
echo "🛑 Proxy disabled"
EOF
chmod +x ~/disable-proxy.sh

# Load proxy configuration
source ~/.proxy-env.sh

echo ""
echo "🎉 Proxy client setup complete!"
echo ""
echo "🌐 Proxy URL: $PROXY_URL"
echo ""
echo "📋 Management commands:"
echo "  Enable:  ~/enable-proxy.sh"
echo "  Disable: ~/disable-proxy.sh"
echo "  Test:    ~/test-proxy.sh"
echo "  Status:  echo \$HTTP_PROXY"
echo ""
echo "🔄 Restart Termux or run: source ~/.bashrc"
echo "🧪 Test connectivity: ~/test-proxy.sh"
echo ""
echo "🌟 Internet access should now work through proxy!"