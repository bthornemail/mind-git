/**
 * Simple WebSocket Signaling Server for WebRTC
 * Run with: node signaling-server.js
 */
const WebSocket = require('ws');

const PORT = 8080;
const wss = new WebSocket.Server({ port: PORT });

console.log(`🚀 Signaling server running on ws://localhost:${PORT}`);

// Store rooms and their participants
const rooms = new Map();
const clients = new Map();

// Handle WebSocket connections
wss.on('connection', (ws) => {
  console.log('New client connected');
  
  let clientId = null;
  let roomId = null;

  ws.on('message', (message) => {
    try {
      const data = JSON.parse(message.toString());
      
      switch (data.type) {
        case 'join-room':
          clientId = data.userId;
          roomId = data.roomId;
          
          // Store client info
          clients.set(clientId, { ws, roomId });
          
          // Create room if it doesn't exist
          if (!rooms.has(roomId)) {
            rooms.set(roomId, new Set());
          }
          
          const room = rooms.get(roomId);
          const existingPeers = Array.from(room).filter(id => id !== clientId);
          
          // Add client to room
          room.add(clientId);
          
          // Notify client they joined successfully
          ws.send(JSON.stringify({
            type: 'room-joined',
            roomId,
            isHost: room.size === 1,
            peers: existingPeers
          }));
          
          // Notify existing peers about new participant
          existingPeers.forEach(peerId => {
            const peerClient = clients.get(peerId);
            if (peerClient && peerClient.ws.readyState === WebSocket.OPEN) {
              peerClient.ws.send(JSON.stringify({
                type: 'peer-joined',
                peerId: clientId,
                roomId
              }));
            }
          });
          
          console.log(`Client ${clientId} joined room ${roomId}. Room size: ${room.size}`);
          break;

        case 'offer':
        case 'answer':
        case 'ice-candidate':
          // Relay signaling messages to target peer
          const targetClient = clients.get(data.to);
          if (targetClient && targetClient.ws.readyState === WebSocket.OPEN) {
            targetClient.ws.send(JSON.stringify(data));
            console.log(`Relayed ${data.type} from ${data.from} to ${data.to}`);
          }
          break;

        case 'canvas-update':
          // Broadcast canvas update to all peers in the room
          if (roomId && rooms.has(roomId)) {
            const room = rooms.get(roomId);
            room.forEach(peerId => {
              if (peerId !== clientId) {
                const peerClient = clients.get(peerId);
                if (peerClient && peerClient.ws.readyState === WebSocket.OPEN) {
                  peerClient.ws.send(JSON.stringify(data));
                }
              }
            });
          }
          break;

        default:
          console.log('Unknown message type:', data.type);
      }
    } catch (error) {
      console.error('Error processing message:', error);
    }
  });

  ws.on('close', () => {
    console.log(`Client ${clientId} disconnected`);
    
    // Remove client from room
    if (clientId && roomId && rooms.has(roomId)) {
      const room = rooms.get(roomId);
      room.delete(clientId);
      
      // Notify other peers
      room.forEach(peerId => {
        const peerClient = clients.get(peerId);
        if (peerClient && peerClient.ws.readyState === WebSocket.OPEN) {
          peerClient.ws.send(JSON.stringify({
            type: 'peer-left',
            peerId: clientId,
            roomId
          }));
        }
      });
      
      // Clean up empty rooms
      if (room.size === 0) {
        rooms.delete(roomId);
      }
    }
    
    // Remove client from clients map
    if (clientId) {
      clients.delete(clientId);
    }
  });

  ws.on('error', (error) => {
    console.error('WebSocket error:', error);
  });
});

// Graceful shutdown
process.on('SIGINT', () => {
  console.log('\n🛑 Shutting down signaling server...');
  wss.close(() => {
    console.log('✅ Server closed');
    process.exit(0);
  });
});

console.log('📡 Signaling server ready for WebRTC connections');