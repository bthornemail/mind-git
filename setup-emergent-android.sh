#!/data/data/com.termux/files/usr/bin/bash
set -e

echo "🧠 Installing emergent capabilities for Android mind-git..."

# Update packages
echo "📦 Updating Termux packages..."
pkg update -y

# Install emergent capability packages
echo "🚀 Installing emergent tools..."
pkg install -y \
    mqtt-clients \
    mosquitto \
    python \
    python-pip \
    termux-api \
    termux-am \
    termux-bluetooth \
    termux-camera \
    termux-location \
    termux-microphone \
    termux-notification \
    termux-sms \
    termux-telephony \
    termux-wake-lock \
    termux-wifi \
    curl \
    jq \
    pv \
    ncurses-utils \
    htop \
    tree \
    rsync \
    unzip \
    zip \
    ffmpeg \
    imagemagick \
    sox

# Install Python packages for emergent behaviors
echo "🐍 Installing Python packages..."
pip install --upgrade pip
pip install \
    paho-mqtt \
    websockets \
    asyncio \
    numpy \
    opencv-python \
    flask \
    requests \
    pillow \
    pyaudio \
    speechrecognition \
    pyttsx3 \
    aiortc \
    aiofiles

# Create emergent capabilities directory
echo "📁 Creating emergent capabilities..."
mkdir -p ~/emergent/{mqtt,webrtc,sensors,ai,automation}

# Create MQTT broker setup
echo "📡 Setting up MQTT broker..."
cat > ~/emergent/mqtt/start-mqtt-broker.sh <<'EOF'
#!/data/data/com.termux/files/usr/bin/bash
echo "📡 Starting MQTT broker..."

# Kill existing broker
pkill mosquitto 2>/dev/null || true

# Start broker with mobile-friendly config
mosquitto -p 1883 -h 0.0.0.0 -c <(cat <<MOQ
# Mobile MQTT Configuration
listener 1883 0.0.0.0
allow_anonymous true
persistence false
max_connections 100
max_inflight_messages 20
max_queued_messages 100
message_size_limit 0
log_dest stdout
log_type error
log_type warning
log_type notice
log_type information
connection_messages true
log_timestamp true
MOQ
) &

echo "✅ MQTT broker started on port 1883"
echo "📊 Status: $(ps aux | grep mosquitto | grep -v grep)"
EOF
chmod +x ~/emergent/mqtt/start-mqtt-broker.sh

# Create MQTT client for mind-git integration
cat > ~/emergent/mqtt/mind-git-mqtt.js <<'EOF'
#!/usr/bin/env node

/**
 * MIND-GIT MQTT Integration - Emergent Communication
 */

const mqtt = require('mqtt');
const fs = require('fs');
const { execSync } = require('child_process');

class MindGitMQTT {
    constructor() {
        this.client = mqtt.connect('mqtt://localhost:1883');
        this.mindGitPath = process.env.MIND_GIT_HOME || '~/devops/mind-git';
        this.setupEventHandlers();
    }

    setupEventHandlers() {
        this.client.on('connect', () => {
            console.log('🧠 MIND-GIT MQTT Connected');
            this.subscribeToTopics();
        });

        this.client.on('message', (topic, message) => {
            this.handleMessage(topic, message.toString());
        });
    }

    subscribeToTopics() {
        const topics = [
            'mind-git/compile',
            'mind-git/execute',
            'mind-git/status',
            'mind-git/sensors',
            'mind-git/ai/decision',
            'mind-git/emergency'
        ];

        topics.forEach(topic => {
            this.client.subscribe(topic);
            console.log(`📡 Subscribed to: ${topic}`);
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
                    this.handleStatus(data);
                    break;
                case 'mind-git/sensors':
                    this.handleSensors(data);
                    break;
                case 'mind-git/ai/decision':
                    this.handleAIDecision(data);
                    break;
                case 'mind-git/emergency':
                    this.handleEmergency(data);
                    break;
            }
        } catch (error) {
            console.error(`❌ Error handling message: ${error.message}`);
        }
    }

    async handleCompile(data) {
        console.log('🔨 Compiling canvas via MQTT...');
        try {
            const result = execSync(`cd ${this.mindGitPath} && node mind-git-simple-cli.cjs compile ${data.canvasFile}`, { encoding: 'utf8' });
            this.publish('mind-git/results/compile', {
                success: true,
                output: result,
                timestamp: new Date().toISOString()
            });
        } catch (error) {
            this.publish('mind-git/results/compile', {
                success: false,
                error: error.message,
                timestamp: new Date().toISOString()
            });
        }
    }

    async handleExecute(data) {
        console.log('🚀 Executing canvas via MQTT...');
        try {
            const result = execSync(`cd ${this.mindGitPath} && node ${data.jsFile}`, { encoding: 'utf8' });
            this.publish('mind-git/results/execute', {
                success: true,
                output: result,
                timestamp: new Date().toISOString()
            });
        } catch (error) {
            this.publish('mind-git/results/execute', {
                success: false,
                error: error.message,
                timestamp: new Date().toISOString()
            });
        }
    }

    handleStatus(data) {
        const status = {
            uptime: require('os').uptime(),
            memory: require('os').totalmem() - require('os').freemem(),
            nodeVersion: process.version,
            mindGitPath: this.mindGitPath,
            timestamp: new Date().toISOString()
        };
        
        this.publish('mind-git/results/status', status);
    }

    handleSensors(data) {
        // Trigger sensor data collection
        execSync('~/emergent/sensors/collect-sensors.sh');
    }

    handleAIDecision(data) {
        console.log('🤖 AI Decision received:', data);
        // Implement AI decision logic
    }

    handleEmergency(data) {
        console.log('🚨 Emergency protocol activated!');
        // Implement emergency response
        this.triggerEmergencyResponse(data);
    }

    publish(topic, data) {
        this.client.publish(topic, JSON.stringify(data));
        console.log(`📤 Published: ${topic}`);
    }

    triggerEmergencyResponse(data) {
        // Use Termux API for emergency notifications
        try {
            execSync(`termux-notification --title "MIND-GIT Emergency" --content "${data.message}" --sound`);
            execSync('termux-vibrate -d 1000');
        } catch (error) {
            console.error('Emergency notification failed:', error.message);
        }
    }
}

// Start the MQTT client
const mindGitMQTT = new MindGitMQTT();

console.log('🧠 MIND-GIT MQTT Integration Started');
console.log('📡 Connected to mqtt://localhost:1883');
console.log('🎯 Ready for emergent behaviors');
EOF

# Create sensor data collection script
cat > ~/emergent/sensors/collect-sensors.sh <<'EOF'
#!/data/data/com.termux/files/usr/bin/bash
echo "📊 Collecting sensor data..."

SENSOR_DATA="{}"

# Get battery info
if command -v termux-battery-status >/dev/null 2>&1; then
    BATTERY=$(termux-battery-status 2>/dev/null || echo '{"percentage": "unknown"}')
    SENSOR_DATA=$(echo "$SENSOR_DATA" | jq --argjson battery "$BATTERY" '. + {battery: $battery}')
fi

# Get location info
if command -v termux-location >/dev/null 2>&1; then
    LOCATION=$(timeout 5s termux-location 2>/dev/null || echo '{"latitude": "unknown", "longitude": "unknown"}')
    SENSOR_DATA=$(echo "$SENSOR_DATA" | jq --argjson location "$LOCATION" '. + {location: $location}')
fi

# Get WiFi info
if command -v termux-wifi-connectioninfo >/dev/null 2>&1; then
    WIFI=$(termux-wifi-connectioninfo 2>/dev/null || echo '{"ssid": "unknown"}')
    SENSOR_DATA=$(echo "$SENSOR_DATA" | jq --argjson wifi "$WIFI" '. + {wifi: $wifi}')
fi

# Get system info
UPTIME=$(uptime | awk '{print $3,$4}' | cut -d',' -f1)
MEMORY=$(free -h | grep Mem | awk '{print $3"/"$2}')
SENSOR_DATA=$(echo "$SENSOR_DATA" | jq --arg uptime "$UPTIME" --arg memory "$MEMORY" '. + {system: {uptime: $uptime, memory: $memory}}')

# Add timestamp
SENSOR_DATA=$(echo "$SENSOR_DATA" | jq --arg timestamp "$(date -Iseconds)" '. + {timestamp: $timestamp}')

echo "$SENSOR_DATA"

# Publish to MQTT if available
if pgrep mosquitto >/dev/null; then
    echo "$SENSOR_DATA" | mosquitto_pub -h localhost -p 1883 -t mind-git/sensors/data
fi
EOF
chmod +x ~/emergent/sensors/collect-sensors.sh

# Create WebRTC signaling server
cat > ~/emergent/webrtc/signaling-server.js <<'EOF'
#!/usr/bin/env node

/**
 * WebRTC Signaling Server for P2P Communication
 */

const WebSocket = require('ws');
const http = require('http');
const fs = require('fs');

class WebRTCSignaling {
    constructor(port = 8080) {
        this.port = port;
        this.rooms = new Map();
        this.setupServer();
    }

    setupServer() {
        const server = http.createServer((req, res) => {
            res.writeHead(200, {'Content-Type': 'text/plain'});
            res.end('MIND-GIT WebRTC Signaling Server\n');
        });

        this.wss = new WebSocket.Server({ server });
        this.wss.on('connection', (ws) => this.handleConnection(ws));
        
        server.listen(this.port, () => {
            console.log(`🌐 WebRTC Signaling Server running on port ${this.port}`);
        });
    }

    handleConnection(ws) {
        console.log('🔗 New WebRTC connection');
        
        ws.on('message', (message) => {
            try {
                const data = JSON.parse(message);
                this.handleMessage(ws, data);
            } catch (error) {
                console.error('❌ Invalid message format:', error.message);
            }
        });

        ws.on('close', () => {
            console.log('🔌 WebRTC connection closed');
        });
    }

    handleMessage(ws, data) {
        switch(data.type) {
            case 'join':
                this.handleJoin(ws, data);
                break;
            case 'offer':
            case 'answer':
            case 'ice-candidate':
                this.relayMessage(ws, data);
                break;
        }
    }

    handleJoin(ws, data) {
        const roomId = data.room;
        
        if (!this.rooms.has(roomId)) {
            this.rooms.set(roomId, new Set());
        }
        
        this.rooms.get(roomId).add(ws);
        ws.room = roomId;
        
        console.log(`📱 Client joined room: ${roomId}`);
        
        // Notify room members
        this.broadcast(roomId, {
            type: 'peer-joined',
            peers: this.rooms.get(roomId).size - 1
        }, ws);
    }

    relayMessage(ws, data) {
        this.broadcast(ws.room, data, ws);
    }

    broadcast(roomId, message, exclude = null) {
        if (!this.rooms.has(roomId)) return;
        
        this.rooms.get(roomId).forEach(client => {
            if (client !== exclude && client.readyState === WebSocket.OPEN) {
                client.send(JSON.stringify(message));
            }
        });
    }
}

// Start the signaling server
new WebRTCSignaling(8080);
EOF

chmod +x ~/emergent/webrtc/signaling-server.js

# Create AI decision engine
cat > ~/emergent/ai/decision-engine.py <<'EOF'
#!/usr/bin/env python3
"""
MIND-GIT AI Decision Engine - Emergent Intelligence
"""

import json
import time
import random
import subprocess
from datetime import datetime

class AIDecisionEngine:
    def __init__(self):
        self.state = {
            'energy_level': 100,
            'network_quality': 'good',
            'current_task': None,
            'last_decision': None,
            'learning_history': []
        }
        
    def collect_context(self):
        """Collect environmental context"""
        context = {}
        
        # Battery level
        try:
            battery = subprocess.check_output(['termux-battery-status'], text=True)
            context['battery'] = json.loads(battery)
        except:
            context['battery'] = {'percentage': 50}
            
        # Network status
        context['network'] = self.assess_network()
        
        # System load
        try:
            uptime = subprocess.check_output(['uptime'], text=True)
            context['system'] = {'uptime': uptime.strip()}
        except:
            context['system'] = {'uptime': 'unknown'}
            
        return context
    
    def assess_network(self):
        """Assess network quality"""
        try:
            result = subprocess.run(['ping', '-c', '1', '8.8.8.8'], 
                                capture_output=True, text=True, timeout=5)
            if result.returncode == 0:
                return 'excellent'
            else:
                return 'poor'
        except:
            return 'offline'
    
    def make_decision(self, context):
        """Make intelligent decision based on context"""
        battery = context['battery'].get('percentage', 50)
        network = context['network']
        
        # Decision logic
        if battery < 20:
            return {
                'action': 'conserve_energy',
                'priority': 'high',
                'reason': 'Low battery',
                'commands': ['stop_nonessential_services', 'reduce_frequency']
            }
        elif network == 'offline':
            return {
                'action': 'offline_mode',
                'priority': 'medium',
                'reason': 'No network connectivity',
                'commands': ['use_local_cache', 'defer_sync']
            }
        elif battery > 80 and network == 'excellent':
            return {
                'action': 'full_operation',
                'priority': 'low',
                'reason': 'Optimal conditions',
                'commands': ['enable_all_features', 'sync_data']
            }
        else:
            return {
                'action': 'balanced_mode',
                'priority': 'medium',
                'reason': 'Normal operation',
                'commands': ['adaptive_performance']
            }
    
    def execute_decision(self, decision):
        """Execute the decision"""
        print(f"🤖 Executing decision: {decision['action']}")
        
        for command in decision['commands']:
            if command == 'conserve_energy':
                self.conserve_energy()
            elif command == 'offline_mode':
                self.enable_offline_mode()
            elif command == 'full_operation':
                self.enable_full_operation()
            elif command == 'balanced_mode':
                self.enable_balanced_mode()
    
    def conserve_energy(self):
        """Enable energy conservation"""
        print('🔋 Enabling energy conservation')
        # Stop MQTT broker if running
        subprocess.run(['pkill', 'mosquitto'], capture_output=True)
        
    def enable_offline_mode(self):
        """Enable offline mode"""
        print('📴 Enabling offline mode')
        # Disable proxy
        subprocess.run(['~/disable-proxy.sh'], shell=True, capture_output=True)
        
    def enable_full_operation(self):
        """Enable full operation"""
        print('🚀 Enabling full operation')
        # Start all services
        subprocess.run(['~/emergent/mqtt/start-mqtt-broker.sh'], shell=True)
        
    def enable_balanced_mode(self):
        """Enable balanced mode"""
        print('⚖️  Enabling balanced mode')
        
    def run(self):
        """Main decision loop"""
        print("🧠 MIND-GIT AI Decision Engine Started")
        
        while True:
            try:
                context = self.collect_context()
                decision = self.make_decision(context)
                
                if decision != self.state['last_decision']:
                    self.execute_decision(decision)
                    self.state['last_decision'] = decision
                    
                    # Publish decision to MQTT
                    try:
                        subprocess.run([
                            'mosquitto_pub', '-h', 'localhost', '-p', '1883',
                            '-t', 'mind-git/ai/decision',
                            '-m', json.dumps(decision)
                        ], capture_output=True)
                    except:
                        pass
                
                time.sleep(30)  # Check every 30 seconds
                
            except KeyboardInterrupt:
                print("🛑 AI Decision Engine stopped")
                break
            except Exception as e:
                print(f"❌ Error in decision loop: {e}")
                time.sleep(5)

if __name__ == "__main__":
    engine = AIDecisionEngine()
    engine.run()
EOF

chmod +x ~/emergent/ai/decision-engine.py

# Create automation hub
cat > ~/emergent/automation/hub.sh <<'EOF'
#!/data/data/com.termux/files/usr/bin/bash
echo "🎯 MIND-GIT Automation Hub"

# Start all emergent services
echo "🚀 Starting emergent capabilities..."

# Start MQTT broker
~/emergent/mqtt/start-mqtt-broker.sh

# Start WebRTC signaling server
cd ~/emergent/webrtc
node signaling-server.js &

# Start AI decision engine
cd ~/emergent/ai
python3 decision-engine.py &

# Start sensor monitoring
while true; do
    ~/emergent/sensors/collect-sensors.sh
    sleep 60
done &

echo "✅ All emergent capabilities started"
echo "🧠 MIND-GIT is now intelligent and responsive"

# Show status
echo ""
echo "📊 Service Status:"
echo "  MQTT Broker: $(pgrep mosquitto > /dev/null && echo 'Running' || echo 'Stopped')"
echo "  WebRTC Server: $(pgrep -f signaling-server.js > /dev/null && echo 'Running' || echo 'Stopped')"
echo "  AI Engine: $(pgrep -f decision-engine.py > /dev/null && echo 'Running' || echo 'Stopped')"
echo "  Sensor Monitor: Running"

echo ""
echo "🌐 Available endpoints:"
echo "  MQTT: mqtt://localhost:1883"
echo "  WebRTC: ws://localhost:8080"
echo "  Mind-git: ~/devops/mind-git"
EOF
chmod +x ~/emergent/automation/hub.sh

echo ""
echo "🎉 Emergent capabilities installed!"
echo ""
echo "🧠 New abilities for your Android phone:"
echo "  📡 MQTT communication and broker"
echo "  🌐 WebRTC P2P connections"
echo "  🤖 AI decision engine"
echo "  📊 Sensor data collection"
echo "  🔔 Termux API integration"
echo "  🎯 Automation hub"
echo ""
echo "🚀 Start emergent capabilities:"
echo "  ~/emergent/automation/hub.sh"
echo ""
echo "🌟 Your phone is now an intelligent, responsive system!"