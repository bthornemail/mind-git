# MQTT P2P Canvas System

A comprehensive MQTT-based peer-to-peer canvas synchronization system for real-time collaboration and distributed canvas sharing.

## 🚀 Quick Start

```bash
# Install dependencies
cd src/p2p
npm install

# Build the system
npm run build

# Run interactive demo
npm run demo

# Start MQTT broker server
npm run server

# Run integration tests
npm run test

# Start client demo
npm run client
```

## 📦 Installation

### Prerequisites
- Node.js 18+ 
- MQTT broker (Mosquitto, EMQX, or HiveMQ)
- Git repositories for canvas files

### Install from Source
```bash
git clone https://github.com/bthornemail/mind-git.git
cd mind-git/src/p2p
npm install
npm run build
```

### Install from NPM
```bash
npm install -g @mind-git/mqtt-p2p
mqtt-p2p --help
```

## 🎯 Features

### 🔄 Real-time Collaboration
- Live canvas updates across multiple repositories
- Instant synchronization of canvas changes
- Conflict detection and resolution
- Version control integration

### 🌐 P2P Network
- Direct peer-to-peer canvas sharing
- Automatic peer discovery
- Mesh network topology support
- Configurable sync intervals

### 📊 Performance
- Sub-millisecond message delivery
- Configurable message size limits
- Connection pooling and reuse
- Built-in metrics and monitoring

### 🔒 Security
- Username/password authentication
- Client ID randomization
- Optional TLS encryption
- Topic-based access control

## 🏗️ Architecture

### Core Components

1. **MQTT Broker** (`mqtt-broker.ts`)
   - Connection management
   - Topic-based routing
   - Message persistence
   - Client discovery

2. **Canvas Synchronizer** (`canvas-sync.ts`)
   - Local state management
   - Change detection
   - Conflict resolution
   - Version control

3. **Network Manager** (`network-manager.ts`)
   - Multi-repository support
   - Peer discovery
   - Health monitoring
   - Performance metrics

4. **Integration Service** (`mqtt-integration.ts`)
   - High-level API
   - Configuration management
   - Health checks
   - Testing utilities

## 📚 API Reference

### Basic Usage

```typescript
import { createP2PNetwork } from '@mind-git/mqtt-p2p';

// Create network manager
const network = createP2PNetwork({
  broker: { host: 'localhost', port: 1883 },
  repositories: ['repo1', 'repo2'],
  enableDiscovery: true,
  syncInterval: 30
});

// Initialize
await network.initialize();

// Create canvas
await network.createCanvas('repo1', 'my-canvas', canvasData, 'author');

// Share canvas
await network.shareCanvas('repo1', 'my-canvas', 'repo2');

// Sync repository
await network.syncRepository('repo1');
```

### Advanced Configuration

```typescript
const network = createP2PNetwork({
  broker: {
    host: 'broker.example.com',
    port: 8883,
    username: 'user',
    password: 'pass'
  },
  repositories: ['main-repo', 'backup-repo'],
  features: {
    realTimeCollaboration: true,
    autoSync: true,
    discovery: true,
    encryption: true
  },
  performance: {
    maxMessageSize: 1024 * 1024, // 1MB
    maxConnections: 1000,
    heartbeatInterval: 30
  }
});
```

## 🧪 Testing

### Unit Tests
```bash
cd src/p2p
npm test
```

### Integration Tests
```bash
npm run test:integration
```

### Performance Tests
```bash
npm run test:performance
```

### Load Tests
```bash
npm run test:load
```

## 📊 Monitoring

### Health Checks
```bash
mqtt-p2p health
```

### Performance Metrics
```bash
mqtt-p2p monitor
```

### Log Analysis
```bash
mqtt-p2p logs --level info --tail 100
```

## 🔧 Configuration

### Environment Variables
```bash
export MQTT_BROKER_HOST=localhost
export MQTT_BROKER_PORT=1883
export MQTT_USERNAME=mind-git
export MQTT_PASSWORD=your-password
export MQTT_REPOSITORIES=repo1,repo2,repo3
```

### Configuration File
```json
{
  "broker": {
    "host": "localhost",
    "port": 1883,
    "username": "mind-git",
    "password": "password"
  },
  "repositories": ["repo1", "repo2"],
  "features": {
    "realTimeCollaboration": true,
    "autoSync": true,
    "discovery": true,
    "encryption": false
  },
  "performance": {
    "maxMessageSize": 65536,
    "maxConnections": 100,
    "heartbeatInterval": 60
  }
}
```

## 🚀 Production Deployment

### Docker
```dockerfile
FROM node:18-alpine
WORKDIR /app
COPY package*.json ./
RUN npm ci --only=production
COPY dist/ ./dist/
EXPOSE 1883
CMD ["node", "dist/mqtt-cli.js", "server"]
```

### Docker Compose
```yaml
version: '3.8'
services:
  mqtt-broker:
    image: eclipse-mosquitto:2
    ports:
      - "1883:1883"
    environment:
      - MOSQUITTO_USERNAME=mind-git
      - MOSQUITTO_PASSWORD=password
    volumes:
      - ./data:/mosquitto/data
      - ./logs:/mosquitto/log

  mqtt-p2p:
    build: .
    depends_on:
      - mqtt-broker
    environment:
      - MQTT_BROKER_HOST=mqtt-broker
      - MQTT_BROKER_PORT=1883
```

### Kubernetes
```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: mqtt-p2p
spec:
  replicas: 3
  selector:
    matchLabels:
      app: mqtt-p2p
  template:
    metadata:
      labels:
        app: mqtt-p2p
    spec:
      containers:
      - name: mqtt-p2p
        image: mind-git/mqtt-p2p:latest
        ports:
          - containerPort: 3000
        env:
          - name: MQTT_BROKER_HOST
            value: "mqtt-broker"
          - name: MQTT_BROKER_PORT
            value: "1883"
```

## 🔍 Troubleshooting

### Common Issues

#### Connection Problems
```bash
# Check broker connectivity
telnet localhost 1883

# Test MQTT connection
mosquitto_pub -h localhost -p 1883 -t test -m "hello"

# Check logs
docker logs mqtt-broker
```

#### Sync Issues
```bash
# Check canvas file permissions
ls -la *.canvas

# Verify checksum
md5sum example.canvas

# Check network connectivity
ping broker-hostname
```

#### Performance Issues
```bash
# Monitor message queue
mqtt-p2p monitor --verbose

# Check broker load
mosquitto_sub -h localhost -p 1883 -t "$SYS/broker/load"

# Test network latency
ping -c 4 broker-hostname
```

## 📝 License

MIT License - see LICENSE file for details.

## 🤝 Contributing

1. Fork the repository
2. Create a feature branch
3. Implement your feature
4. Add tests
5. Submit a pull request

## 📞 Support

- GitHub Issues: https://github.com/bthornemail/mind-git/issues
- Documentation: https://github.com/bthornemail/mind-git/docs/mqtt-p2p
- Examples: https://github.com/bthornemail/mind-git/examples/mqtt-p2p