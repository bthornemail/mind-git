#!/usr/bin/env bash
set -e

echo "🚀 Deploying proxy setup to Android devices..."

# Device configurations
PROXY_SERVER_USER="u0_a315"
PROXY_SERVER_IP="10.208.42.20"
PROXY_SERVER_PORT="8022"

PROXY_CLIENT_USER="u0_a201"
PROXY_CLIENT_IP="10.208.42.148"
PROXY_CLIENT_PORT="8022"

echo "📱 Setting up proxy server on $PROXY_SERVER_IP..."

# Transfer and setup proxy server
echo "📤 Transferring server setup..."
scp -P "$PROXY_SERVER_PORT" setup-tinyproxy-server.sh "$PROXY_SERVER_USER@$PROXY_SERVER_IP:~/"

echo "🔧 Installing proxy server..."
ssh -p "$PROXY_SERVER_PORT" "$PROXY_SERVER_USER@$PROXY_SERVER_IP" "bash ~/setup-tinyproxy-server.sh"

echo ""
echo "📱 Setting up proxy client on $PROXY_CLIENT_IP..."

# Transfer and setup proxy client
echo "📤 Transferring client setup..."
scp -P "$PROXY_CLIENT_PORT" setup-proxy-client.sh "$PROXY_CLIENT_USER@$PROXY_CLIENT_IP:~/"

echo "🔧 Installing proxy client..."
ssh -p "$PROXY_CLIENT_PORT" "$PROXY_CLIENT_USER@$PROXY_CLIENT_IP" "bash ~/setup-proxy-client.sh"

echo ""
echo "🧪 Testing proxy connection..."

# Test proxy from client
echo "🌐 Testing proxy from client device..."
ssh -p "$PROXY_CLIENT_PORT" "$PROXY_CLIENT_USER@$PROXY_CLIENT_IP" "~/test-proxy.sh"

echo ""
echo "🎉 Proxy deployment complete!"
echo ""
echo "📋 Status:"
echo "  Proxy Server: $PROXY_SERVER_IP:8888"
echo "  Proxy Client: $PROXY_CLIENT_IP (configured to use server)"
echo ""
echo "🔧 Management:"
echo "  Server status: ssh -p $PROXY_SERVER_PORT $PROXY_SERVER_USER@$PROXY_SERVER_IP '~/status-tinyproxy.sh'"
echo "  Client test:   ssh -p $PROXY_CLIENT_PORT $PROXY_CLIENT_USER@$PROXY_CLIENT_IP '~/test-proxy.sh'"
echo ""
echo "🌟 Both Android devices now have internet access!"