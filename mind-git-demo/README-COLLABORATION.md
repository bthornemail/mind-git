# 🚀 Mind-Git Demo - Enhanced with Real-time Collaboration

This demo showcases the CanvasL visual programming language with real-time collaboration features including WebRTC and MQTT integration.

## ✨ New Features

### ✅ Completed Features
- **Fixed React Hooks Error**: Resolved conditional hook calls in GLTFNode component
- **Fixed Model Updates**: Model selection now properly updates and re-renders
- **Scene Switcher**: Switch between different canvas examples with tags and search
- **WebRTC Integration**: Peer-to-peer real-time collaboration
- **MQTT Integration**: Message-based collaboration and canvas synchronization
- **Transform Controls**: Interactive 3D transformation (translate, rotate, scale) for selected nodes
- **Fly Controls**: First-person flying navigation mode for 3D space exploration

## 🛠️ Setup Instructions

### Prerequisites
```bash
# Install Node.js dependencies
npm install

# Install MQTT broker (Mosquitto)
sudo apt-get install mosquitto mosquitto-clients  # Ubuntu/Debian
brew install mosquitto                            # macOS
```

### Start the Development Server

1. **Start MQTT Broker** (in separate terminal):
```bash
# Start Mosquitto with WebSocket support
mosquitto -p 1883 -p 9001 -l /var/log/mosquitto.log

# Or with Docker
docker run -it -p 1883:1883 -p 9001:9001 eclipse-mosquitto
```

2. **Start WebRTC Signaling Server** (in separate terminal):
```bash
node signaling-server.js
```

3. **Start the React App**:
```bash
npm start
```

The app will be available at `http://localhost:3000`

## 🎮 Usage Guide

### Scene Switcher
- **Top Right Panel**: Browse and switch between different canvas examples
- **Filter by Tags**: Mathematical, Educational, Advanced, etc.
- **Search**: Find specific scenes by name or description
- **Preview**: See node count and complexity before switching

### WebRTC Collaboration
- **Bottom Left Panel**: WebRTC connection manager
- **Join Room**: Enter a room ID to collaborate with others
- **Real-time Sync**: Canvas changes are synchronized across peers
- **Peer Status**: See connected peers and connection status

### MQTT Integration
- **Top Left Panel**: MQTT message broker interface
- **Auto-connect**: Automatically connects to MQTT broker on startup
- **Publish Messages**: Send custom JSON messages
- **Canvas Sync**: Broadcast canvas changes to all subscribers
- **Topic Management**: Subscribe/unsubscribe from topics

### 3D Canvas Visualization
- **Camera Modes**:
  - **Orbit Mode**: Traditional 3D navigation (default)
    - Left click + drag: Rotate view
    - Right click + drag: Pan view  
    - Scroll: Zoom in/out
  - **Fly Mode**: First-person navigation
    - WASD/Arrow keys: Move forward/backward/strafe
    - Mouse: Look around
    - Q/E: Roll left/right
- **Node Interaction**: 
  - Click nodes to select them
  - Selected nodes show transform controls
  - Transform modes: Move, Rotate, Scale
- **Model Selection**: Assign 3D models to node types
- **Real-time Updates**: Changes sync across all connected clients

## 🔧 Technical Architecture

### WebRTC Implementation
- **Signaling Server**: WebSocket-based signaling for peer discovery
- **Data Channels**: RTCDataChannel for canvas synchronization
- **ICE Servers**: STUN servers for NAT traversal
- **Peer Management**: Dynamic peer connection handling

### MQTT Implementation
- **Broker**: Mosquitto with WebSocket support
- **Topics**: 
  - `mind-git/canvas/updates`: Canvas synchronization
  - `mind-git/canvas/presence`: User presence
  - `mind-git/canvas/commands`: System commands
- **Message Format**: JSON with timestamps and user IDs

### Scene Management
- **Scene Library**: Pre-defined canvas examples
- **Dynamic Loading**: Scenes load on demand
- **Metadata**: Tags, descriptions, complexity metrics
- **Search & Filter**: Find scenes by properties

## 📁 File Structure

```
src/
├── components/
│   ├── Canvas3D.tsx          # Main 3D canvas viewer
│   ├── Node3D.tsx            # 3D node component
│   ├── Edge3D.tsx            # 3D edge component
│   ├── NodeGeometry.tsx      # Node geometry (GLTF + procedural)
│   ├── TransformControls.tsx # 3D transform controls
│   ├── FlyControls.tsx       # First-person fly controls
│   ├── ModelSelector.tsx     # 3D model selection UI
│   ├── SceneSwitcher.tsx     # Scene switching interface
│   ├── WebRTCManager.tsx     # WebRTC collaboration
│   ├── MQTTManager.tsx       # MQTT integration
│   └── CompilerPanel.tsx     # Canvas compilation panel
├── scenes/
│   └── index.ts              # Scene library
├── services/
│   └── modelLibrary.ts       # 3D model management
├── types/
│   └── index.ts              # TypeScript definitions
├── App.tsx                   # Main application
└── exampleCanvas.ts          # Default canvas example

signaling-server.js           # WebRTC signaling server
mqtt-setup.js                 # MQTT testing utilities
package.json                  # Dependencies and scripts
```

## 🧪 Testing

### Test MQTT Connection
```bash
node mqtt-setup.js
```

### Test WebRTC Signaling
Open multiple browser tabs and join the same room ID to test peer connections.

### Test Scene Switching
Use the scene switcher panel to browse and switch between different canvas examples.

## 🐛 Troubleshooting

### Common Issues

1. **MQTT Connection Failed**
   - Ensure Mosquitto is running: `mosquitto -p 1883 -p 9001`
   - Check firewall settings for ports 1883 and 9001
   - Verify WebSocket support is enabled

2. **WebRTC Connection Failed**
   - Start signaling server: `node signaling-server.js`
   - Check browser console for ICE candidate errors
   - Ensure HTTPS for production (WebRTC requires secure context)

3. **3D Models Not Loading**
   - Check browser console for GLTF loading errors
   - Verify model paths in ModelSelector
   - Fallback to procedural geometry if models fail

4. **Scene Switcher Not Working**
   - Verify scenes/index.ts exports are correct
   - Check for TypeScript compilation errors
   - Ensure scene data structure matches Canvas type

5. **Transform Controls Not Visible**
   - Ensure a node is selected (click on it)
   - Check that transform mode is set correctly
   - Verify three.js TransformControls are imported

6. **Fly Controls Not Responding**
   - Click the "Fly Mode" button to activate
   - Ensure browser window has focus
   - Check that WASD/Arrow keys work for movement
   - Use mouse to look around

## 🚀 Production Deployment

### Environment Variables
```bash
REACT_APP_MQTT_BROKER_URL=wss://your-broker.com:9001
REACT_APP_SIGNALING_SERVER_URL=wss://your-server.com:8080
REACT_APP_DEFAULT_ROOM_ID=production-room
```

### Docker Deployment
```dockerfile
FROM node:18-alpine
WORKDIR /app
COPY package*.json ./
RUN npm ci --only=production
COPY . .
RUN npm run build
EXPOSE 3000
CMD ["npm", "start"]
```

## 🤝 Contributing

1. Fork the repository
2. Create a feature branch
3. Implement your changes
4. Add tests for new functionality
5. Submit a pull request

## 📄 License

This project is part of the mind-git mathematical foundation for self-evolving computational systems.

---

**🎯 Next Steps**: The foundation is complete. Keep building the distributed system architecture. Every polynomial brings the system integration closer.