#!/data/data/com.termux/files/usr/bin/bash
set -e

echo "🧠 Installing emergent capabilities (offline mode)..."

# Create emergent capabilities directory
echo "📁 Creating emergent capabilities..."
mkdir -p ~/emergent/{mqtt,webrtc,sensors,ai,automation}

# Install Node.js packages manually
echo "📦 Installing Node.js packages..."
cd ~
source ~/.proxy-env.sh

npm install -g mqtt ws 2>/dev/null || echo "⚠️  npm install failed, will create manual versions"

# Create simple MQTT broker using Node.js
cat > ~/emergent/mqtt/simple-mqtt-broker.js <<'EOF'
/**
 * Simple MQTT Broker for Android
 */

const net = require('net');
const EventEmitter = require('events');

class SimpleMQTTBroker extends EventEmitter {
    constructor(port = 1883) {
        super();
        this.port = port;
        this.clients = new Map();
        this.topics = new Map();
        this.server = null;
    }

    start() {
        this.server = net.createServer((socket) => {
            console.log('📡 New MQTT client connected');
            
            socket.on('data', (data) => {
                this.handleMessage(socket, data);
            });

            socket.on('close', () => {
                console.log('🔌 MQTT client disconnected');
                this.removeClient(socket);
            });

            socket.on('error', (err) => {
                console.error('❌ Socket error:', err.message);
            });
        });

        this.server.listen(this.port, '0.0.0.0', () => {
            console.log(`🌐 MQTT Broker listening on port ${this.port}`);
        });
    }

    handleMessage(socket, data) {
        try {
            // Simple MQTT-like protocol
            const message = data.toString().trim();
            if (message.startsWith('SUB:')) {
                const topic = message.substring(4);
                this.subscribe(socket, topic);
            } else if (message.startsWith('PUB:')) {
                const parts = message.substring(4).split(':', 2);
                if (parts.length === 2) {
                    this.publish(parts[0], parts[1]);
                }
            }
        } catch (error) {
            console.error('❌ Message handling error:', error.message);
        }
    }

    subscribe(socket, topic) {
        if (!this.clients.has(socket)) {
            this.clients.set(socket, []);
        }
        this.clients.get(socket).push(topic);
        socket.write(`SUBACK:${topic}\n`);
        console.log(`📨 Client subscribed to: ${topic}`);
    }

    publish(topic, message) {
        console.log(`📤 Publishing to ${topic}: ${message}`);
        
        // Store message
        if (!this.topics.has(topic)) {
            this.topics.set(topic, []);
        }
        this.topics.get(topic).push({
            message,
            timestamp: new Date().toISOString()
        });

        // Forward to subscribers
        this.clients.forEach((topics, client) => {
            if (topics.includes(topic) && client.writable) {
                client.write(`MSG:${topic}:${message}\n`);
            }
        });
    }

    removeClient(socket) {
        this.clients.delete(socket);
    }
}

// Start broker
const broker = new SimpleMQTTBroker(1883);
broker.start();

console.log('🧠 Simple MQTT Broker Started');
console.log('📡 Protocol: SUB:<topic>, PUB:<topic>:<message>');
EOF

chmod +x ~/emergent/mqtt/simple-mqtt-broker.js

# Create MQTT client for mind-git
cat > ~/emergent/mqtt/mind-git-client.js <<'EOF'
/**
 * MIND-GIT MQTT Client
 */

const net = require('net');
const fs = require('fs');
const { execSync } = require('child_process');

class MindGitMQTTClient {
    constructor(host = 'localhost', port = 1883) {
        this.host = host;
        this.port = port;
        this.socket = null;
        this.subscriptions = [];
        this.mindGitPath = process.env.MIND_GIT_HOME || '~/devops/mind-git';
    }

    connect() {
        this.socket = net.createConnection({ host: this.host, port: this.port }, () => {
            console.log('🧠 Connected to MQTT broker');
            this.subscribeToDefaultTopics();
        });

        this.socket.on('data', (data) => {
            this.handleData(data.toString());
        });

        this.socket.on('close', () => {
            console.log('🔌 Disconnected from MQTT broker');
        });

        this.socket.on('error', (err) => {
            console.error('❌ Connection error:', err.message);
        });
    }

    subscribeToDefaultTopics() {
        const topics = [
            'mind-git/compile',
            'mind-git/execute',
            'mind-git/status',
            'mind-git/sensors',
            'mind-git/emergency'
        ];

        topics.forEach(topic => this.subscribe(topic));
    }

    subscribe(topic) {
        if (this.socket && this.socket.writable) {
            this.socket.write(`SUB:${topic}\n`);
            this.subscriptions.push(topic);
            console.log(`📨 Subscribed to: ${topic}`);
        }
    }

    publish(topic, message) {
        if (this.socket && this.socket.writable) {
            this.socket.write(`PUB:${topic}:${message}\n`);
            console.log(`📤 Published to ${topic}: ${message}`);
        }
    }

    handleData(data) {
        const lines = data.trim().split('\n');
        lines.forEach(line => {
            if (line.startsWith('MSG:')) {
                const parts = line.substring(4).split(':', 2);
                if (parts.length === 2) {
                    this.handleMessage(parts[0], parts[1]);
                }
            }
        });
    }

    handleMessage(topic, message) {
        console.log(`📨 Received: ${topic} -> ${message}`);
        
        try {
            const data = JSON.parse(message);
            
            switch(topic) {
                case 'mind-git/compile':
                    this.handleCompile(data);
                    break;
                case 'mind-git/execute':
                    this.handleExecute(data);
                    break;
                case 'mind-git/status':
                    this.handleStatus();
                    break;
                case 'mind-git/sensors':
                    this.collectSensors();
                    break;
                case 'mind-git/emergency':
                    this.handleEmergency(data);
                    break;
            }
        } catch (error) {
            console.error('❌ Error parsing message:', error.message);
        }
    }

    handleCompile(data) {
        console.log('🔨 Compiling canvas...');
        try {
            const result = execSync(`cd ${this.mindGitPath} && node mind-git-simple-cli.cjs compile ${data.canvasFile}`, { encoding: 'utf8' });
            this.publish('mind-git/results/compile', JSON.stringify({
                success: true,
                output: result,
                timestamp: new Date().toISOString()
            }));
        } catch (error) {
            this.publish('mind-git/results/compile', JSON.stringify({
                success: false,
                error: error.message,
                timestamp: new Date().toISOString()
            }));
        }
    }

    handleExecute(data) {
        console.log('🚀 Executing canvas...');
        try {
            const result = execSync(`cd ${this.mindGitPath} && node ${data.jsFile}`, { encoding: 'utf8' });
            this.publish('mind-git/results/execute', JSON.stringify({
                success: true,
                output: result,
                timestamp: new Date().toISOString()
            }));
        } catch (error) {
            this.publish('mind-git/results/execute', JSON.stringify({
                success: false,
                error: error.message,
                timestamp: new Date().toISOString()
            }));
        }
    }

    handleStatus() {
        const status = {
            uptime: require('os').uptime(),
            memory: require('os').totalmem() - require('os').freemem(),
            nodeVersion: process.version,
            timestamp: new Date().toISOString()
        };
        
        this.publish('mind-git/results/status', JSON.stringify(status));
    }

    collectSensors() {
        const sensorData = this.collectBasicSensors();
        this.publish('mind-git/sensors/data', JSON.stringify(sensorData));
    }

    collectBasicSensors() {
        const data = {
            timestamp: new Date().toISOString()
        };

        // Basic system info
        try {
            data.uptime = require('os').uptime();
            data.memory = {
                total: require('os').totalmem(),
                free: require('os').freemem()
            };
        } catch (error) {
            console.error('Error getting system info:', error.message);
        }

        // Try to get battery info if available
        try {
            const battery = execSync('termux-battery-status 2>/dev/null || echo "{}"', { encoding: 'utf8' });
            data.battery = JSON.parse(battery);
        } catch (error) {
            data.battery = { percentage: 'unknown' };
        }

        return data;
    }

    handleEmergency(data) {
        console.log('🚨 Emergency protocol activated!');
        // Simple emergency response
        try {
            execSync('echo "EMERGENCY: ' + data.message + '" | logger');
        } catch (error) {
            console.error('Emergency logging failed:', error.message);
        }
    }
}

// Start client if run directly
if (require.main === module) {
    const client = new MindGitMQTTClient();
    client.connect();
    
    console.log('🧠 MIND-GIT MQTT Client Started');
    console.log('📡 Connected to localhost:1883');
    console.log('🎯 Ready for emergent behaviors');
}

module.exports = MindGitMQTTClient;
EOF

chmod +x ~/emergent/mqtt/mind-git-client.js

# Create WebRTC signaling server (simple version)
cat > ~/emergent/webrtc/simple-signaling.js <<'EOF'
/**
 * Simple WebRTC Signaling Server
 */

const http = require('http');
const url = require('url');

class SimpleSignaling {
    constructor(port = 8080) {
        this.port = port;
        this.rooms = new Map();
        this.setupServer();
    }

    setupServer() {
        this.server = http.createServer((req, res) => {
            this.handleRequest(req, res);
        });

        this.server.listen(this.port, '0.0.0.0', () => {
            console.log(`🌐 WebRTC Signaling Server on port ${this.port}`);
        });
    }

    handleRequest(req, res) {
        const parsedUrl = url.parse(req.url, true);
        
        // Enable CORS
        res.setHeader('Access-Control-Allow-Origin', '*');
        res.setHeader('Access-Control-Allow-Methods', 'GET, POST, OPTIONS');
        res.setHeader('Access-Control-Allow-Headers', 'Content-Type');

        if (req.method === 'OPTIONS') {
            res.writeHead(200);
            res.end();
            return;
        }

        if (req.method === 'POST' && parsedUrl.pathname === '/signal') {
            this.handleSignaling(req, res);
        } else if (req.method === 'GET' && parsedUrl.pathname === '/') {
            this.handleStatus(req, res);
        } else {
            res.writeHead(404);
            res.end('Not Found');
        }
    }

    handleSignaling(req, res) {
        let body = '';
        req.on('data', chunk => {
            body += chunk.toString();
        });

        req.on('end', () => {
            try {
                const data = JSON.parse(body);
                const roomId = data.room;
                
                if (!this.rooms.has(roomId)) {
                    this.rooms.set(roomId, []);
                }

                // Store signal
                this.rooms.get(roomId).push({
                    data: data,
                    timestamp: new Date().toISOString()
                });

                // Keep only last 10 signals
                if (this.rooms.get(roomId).length > 10) {
                    this.rooms.get(roomId).shift();
                }

                res.writeHead(200, {'Content-Type': 'application/json'});
                res.end(JSON.stringify({ success: true }));
                
                console.log(`📡 Signal stored for room: ${roomId}`);
                
            } catch (error) {
                res.writeHead(400, {'Content-Type': 'application/json'});
                res.end(JSON.stringify({ error: error.message }));
            }
        });
    }

    handleStatus(req, res) {
        const status = {
            service: 'MIND-GIT WebRTC Signaling',
            rooms: this.rooms.size,
            uptime: process.uptime(),
            timestamp: new Date().toISOString()
        };

        res.writeHead(200, {'Content-Type': 'application/json'});
        res.end(JSON.stringify(status));
    }
}

// Start signaling server
if (require.main === module) {
    new SimpleSignaling(8080);
}

module.exports = SimpleSignaling;
EOF

chmod +x ~/emergent/webrtc/simple-signaling.js

# Create AI decision engine (simple version)
cat > ~/emergent/ai/simple-ai.js <<'EOF'
/**
 * Simple AI Decision Engine
 */

const os = require('os');
const { execSync } = require('child_process');

class SimpleAI {
    constructor() {
        this.state = {
            energy: 100,
            network: 'unknown',
            lastDecision: null,
            learningHistory: []
        };
    }

    assessEnvironment() {
        const context = {};

        // System info
        context.uptime = os.uptime();
        context.memory = {
            total: os.totalmem(),
            free: os.freemem(),
            used: os.totalmem() - os.freemem()
        };

        // Try to get battery info
        try {
            const battery = execSync('termux-battery-status 2>/dev/null || echo "{}"', { encoding: 'utf8' });
            context.battery = JSON.parse(battery);
            this.state.energy = context.battery.percentage || 100;
        } catch (error) {
            context.battery = { percentage: 50 };
            this.state.energy = 50;
        }

        // Network assessment
        context.network = this.assessNetwork();
        this.state.network = context.network;

        return context;
    }

    assessNetwork() {
        try {
            // Simple ping test
            execSync('ping -c 1 -W 2 8.8.8.8 >/dev/null 2>&1');
            return 'excellent';
        } catch (error) {
            try {
                execSync('ping -c 1 -W 2 10.208.42.20 >/dev/null 2>&1');
                return 'good';
            } catch (error2) {
                return 'offline';
            }
        }
    }

    makeDecision(context) {
        const energy = this.state.energy;
        const network = this.state.network;

        // Decision logic
        if (energy < 20) {
            return {
                action: 'conserve_energy',
                priority: 'high',
                reason: 'Low battery',
                commands: ['reduce_activity', 'disable_nonessential']
            };
        } else if (network === 'offline') {
            return {
                action: 'offline_mode',
                priority: 'medium',
                reason: 'No network',
                commands: ['use_cache', 'defer_sync']
            };
        } else if (energy > 80 && network === 'excellent') {
            return {
                action: 'full_operation',
                priority: 'low',
                reason: 'Optimal conditions',
                commands: ['enable_all', 'sync_data']
            };
        } else {
            return {
                action: 'balanced_mode',
                priority: 'medium',
                reason: 'Normal operation',
                commands: ['adaptive']
            };
        }
    }

    executeDecision(decision) {
        console.log(`🤖 Executing: ${decision.action} - ${decision.reason}`);
        
        decision.commands.forEach(command => {
            switch(command) {
                case 'reduce_activity':
                    console('🔋 Reducing activity');
                    break;
                case 'disable_nonessential':
                    console('📴 Disabling nonessential services');
                    break;
                case 'use_cache':
                    console('💾 Using cache mode');
                    break;
                case 'defer_sync':
                    console('⏳ Deferring sync');
                    break;
                case 'enable_all':
                    console('🚀 Enabling all services');
                    break;
                case 'sync_data':
                    console('🔄 Syncing data');
                    break;
                case 'adaptive':
                    console('⚖️  Adaptive mode');
                    break;
            }
        });

        this.state.lastDecision = decision;
        this.state.learningHistory.push({
            decision,
            context: this.assessEnvironment(),
            timestamp: new Date().toISOString()
        });
    }

    run() {
        console.log('🧠 Simple AI Decision Engine Started');
        
        const decisionLoop = () => {
            try {
                const context = this.assessEnvironment();
                const decision = this.makeDecision(context);
                
                if (JSON.stringify(decision) !== JSON.stringify(this.state.lastDecision)) {
                    this.executeDecision(decision);
                }
                
                setTimeout(decisionLoop, 30000); // Check every 30 seconds
            } catch (error) {
                console.error('❌ AI loop error:', error.message);
                setTimeout(decisionLoop, 5000);
            }
        };

        decisionLoop();
    }
}

// Start AI if run directly
if (require.main === module) {
    const ai = new SimpleAI();
    ai.run();
}

module.exports = SimpleAI;
EOF

chmod +x ~/emergent/ai/simple-ai.js

# Create automation hub
cat > ~/emergent/automation/start-hub.sh <<'EOF'
#!/data/data/com.termux/files/usr/bin/bash
echo "🎯 Starting MIND-GIT Automation Hub..."

# Start MQTT broker
echo "📡 Starting MQTT broker..."
cd ~/emergent/mqtt
node simple-mqtt-broker.js &
MQTT_PID=$!
echo "  MQTT Broker PID: $MQTT_PID"

# Start WebRTC signaling server
echo "🌐 Starting WebRTC signaling..."
cd ~/emergent/webrtc
node simple-signaling.js &
WEBRTC_PID=$!
echo "  WebRTC Server PID: $WEBRTC_PID"

# Start AI decision engine
echo "🤖 Starting AI decision engine..."
cd ~/emergent/ai
node simple-ai.js &
AI_PID=$!
echo "  AI Engine PID: $AI_PID"

# Start MQTT client for mind-git integration
echo "🧠 Starting mind-git MQTT client..."
cd ~/emergent/mqtt
node mind-git-client.js &
CLIENT_PID=$!
echo "  MQTT Client PID: $CLIENT_PID"

# Save PIDs for management
echo "$MQTT_PID" > ~/emergent/mqtt.pid
echo "$WEBRTC_PID" > ~/emergent/webrtc.pid
echo "$AI_PID" > ~/emergent/ai.pid
echo "$CLIENT_PID" > ~/emergent/client.pid

echo ""
echo "✅ All emergent capabilities started!"
echo ""
echo "📊 Service Status:"
echo "  MQTT Broker: Running (PID: $MQTT_PID)"
echo "  WebRTC Server: Running (PID: $WEBRTC_PID)"
echo "  AI Engine: Running (PID: $AI_PID)"
echo "  MQTT Client: Running (PID: $CLIENT_PID)"
echo ""
echo "🌐 Available Services:"
echo "  MQTT Broker: mqtt://localhost:1883"
echo "  WebRTC Signaling: http://localhost:8080"
echo "  Mind-git Integration: Active"
echo ""
echo "🧠 Your Android phone is now intelligent!"
echo ""
echo "🛑 Stop all services: ~/emergent/automation/stop-hub.sh"
EOF

chmod +x ~/emergent/automation/start-hub.sh

# Create stop script
cat > ~/emergent/automation/stop-hub.sh <<'EOF'
#!/data/data/com.termux/files/usr/bin/bash
echo "🛑 Stopping MIND-GIT Automation Hub..."

# Stop all services using saved PIDs
for pidfile in ~/emergent/*.pid; do
    if [ -f "$pidfile" ]; then
        PID=$(cat "$pidfile")
        if kill -0 "$PID" 2>/dev/null; then
            echo "  Stopping PID: $PID"
            kill "$PID"
        fi
        rm "$pidfile"
    fi
done

# Also kill any remaining processes
pkill -f simple-mqtt-broker.js 2>/dev/null
pkill -f simple-signaling.js 2>/dev/null
pkill -f simple-ai.js 2>/dev/null
pkill -f mind-git-client.js 2>/dev/null

echo "✅ All emergent capabilities stopped"
EOF

chmod +x ~/emergent/automation/stop-hub.sh

# Create interactive demo script
cat > ~/emergent/demo-interactive.sh <<'EOF'
#!/data/data/com.termux/files/usr/bin/bash
echo "🎮 MIND-GIT Interactive Demo"
echo "=========================="

# Start services if not running
if ! pgrep -f simple-mqtt-broker.js >/dev/null; then
    echo "🚀 Starting services..."
    ~/emergent/automation/start-hub.sh
    sleep 3
fi

echo ""
echo "🎯 Available Commands:"
echo "  1) Compile canvas via MQTT"
echo "  2) Execute canvas via MQTT"
echo "  3) Get system status"
echo "  4) Collect sensor data"
echo "  5) Test emergency protocol"
echo "  6) Show AI decisions"
echo "  7) Exit"
echo ""

while true; do
    echo -n "🎮 Choose option (1-7): "
    read choice

    case $choice in
        1)
            echo -n "📝 Enter canvas file: "
            read canvas
            echo "PUB:mind-git/compile:{\"canvasFile\":\"$canvas\"}" | nc localhost 1883
            ;;
        2)
            echo -n "📝 Enter JS file: "
            read jsfile
            echo "PUB:mind-git/execute:{\"jsFile\":\"$jsfile\"}" | nc localhost 1883
            ;;
        3)
            echo "PUB:mind-git/status:{}" | nc localhost 1883
            ;;
        4)
            echo "PUB:mind-git:sensors:{}" | nc localhost 1883
            ;;
        5)
            echo -n "🚨 Enter emergency message: "
            read message
            echo "PUB:mind-git:emergency:{\"message\":\"$message\"}" | nc localhost 1883
            ;;
        6)
            echo "🤖 Recent AI decisions:"
            echo "  Energy Level: $(cat ~/emergent/ai/learning.json 2>/dev/null | jq '.[-1].context.battery.percentage' || echo 'Unknown')"
            echo "  Network Status: $(cat ~/emergent/ai/learning.json 2>/dev/null | jq '.[-1].context.network' || echo 'Unknown')"
            ;;
        7)
            echo "👋 Goodbye!"
            exit 0
            ;;
        *)
            echo "❌ Invalid option"
            ;;
    esac
    
    echo ""
    sleep 1
done
EOF

chmod +x ~/emergent/demo-interactive.sh

echo ""
echo "🎉 Emergent capabilities setup complete!"
echo ""
echo "🧠 New abilities for your Android phone:"
echo "  📡 MQTT broker and client"
echo "  🌐 WebRTC signaling server"
echo "  🤖 AI decision engine"
echo "  📊 Basic sensor collection"
echo "  🎮 Interactive demo"
echo ""
echo "🚀 Start emergent capabilities:"
echo "  ~/emergent/automation/start-hub.sh"
echo ""
echo "🎮 Try interactive demo:"
echo "  ~/emergent/demo-interactive.sh"
echo ""
echo "🛑 Stop all services:"
echo "  ~/emergent/automation/stop-hub.sh"
echo ""
echo "🌟 Your phone is now an intelligent, responsive system!"