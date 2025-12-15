/**
 * WebRTC Integration Component
 * Enables peer-to-peer real-time collaboration for canvas editing
 */
import React, { useState, useEffect, useRef, useCallback } from 'react';
import { Canvas } from '../types';

interface WebRTCManagerProps {
  canvas: Canvas;
  onCanvasUpdate: (canvas: Canvas) => void;
  roomId: string;
  userId: string;
}

interface PeerConnection {
  peerId: string;
  connection: RTCPeerConnection;
  dataChannel: RTCDataChannel;
}

export const WebRTCManager: React.FC<WebRTCManagerProps> = ({
  canvas,
  onCanvasUpdate,
  roomId,
  userId
}) => {
  const [isConnected, setIsConnected] = useState(false);
  const [connectedPeers, setConnectedPeers] = useState<string[]>([]);
  const [isHost, setIsHost] = useState(false);
  const [roomIdInput, setRoomIdInput] = useState(roomId);
  const [status, setStatus] = useState<'idle' | 'connecting' | 'connected' | 'error'>('idle');
  
  const peerConnections = useRef<Map<string, PeerConnection>>(new Map());
  const localVideoRef = useRef<HTMLVideoElement>(null);
  const remoteVideosRef = useRef<Map<string, HTMLVideoElement>>(new Map());
  const signalingServerRef = useRef<WebSocket | null>(null);

  // WebRTC configuration
  const configuration = {
    iceServers: [
      { urls: 'stun:stun.l.google.com:19302' },
      { urls: 'stun:stun1.l.google.com:19302' }
    ]
  };

  // Initialize signaling server connection
  const connectToSignalingServer = useCallback(() => {
    try {
      const ws = new WebSocket('ws://localhost:8080'); // Replace with your signaling server
      signalingServerRef.current = ws;

      ws.onopen = () => {
        console.log('Connected to signaling server');
        setStatus('connecting');
        
        // Join room
        ws.send(JSON.stringify({
          type: 'join-room',
          roomId: roomIdInput,
          userId
        }));
      };

      ws.onmessage = async (event) => {
        const message = JSON.parse(event.data);
        await handleSignalingMessage(message);
      };

      ws.onerror = (error) => {
        console.error('WebSocket error:', error);
        setStatus('error');
      };

      ws.onclose = () => {
        console.log('Disconnected from signaling server');
        setStatus('idle');
      };
    } catch (error) {
      console.error('Failed to connect to signaling server:', error);
      setStatus('error');
    }
  }, [roomIdInput, userId]);

  // Handle signaling messages
  const handleSignalingMessage = async (message: any) => {
    switch (message.type) {
      case 'room-joined':
        setIsHost(message.isHost);
        setStatus('connected');
        if (message.peers) {
          // Connect to existing peers
          for (const peerId of message.peers) {
            await createPeerConnection(peerId, true);
          }
        }
        break;

      case 'peer-joined':
        await createPeerConnection(message.peerId, false);
        break;

      case 'peer-left':
        await removePeerConnection(message.peerId);
        break;

      case 'offer':
        await handleOffer(message.from, message.offer);
        break;

      case 'answer':
        await handleAnswer(message.from, message.answer);
        break;

      case 'ice-candidate':
        await handleIceCandidate(message.from, message.candidate);
        break;

      case 'canvas-update':
        onCanvasUpdate(message.canvas);
        break;
    }
  };

  // Create peer connection
  const createPeerConnection = async (peerId: string, isInitiator: boolean) => {
    try {
      const pc = new RTCPeerConnection(configuration);
      
      // Create data channel for canvas updates
      const dataChannel = pc.createDataChannel('canvas-updates', {
        ordered: true
      });

      dataChannel.onopen = () => {
        console.log(`Data channel opened with ${peerId}`);
        setConnectedPeers(prev => [...prev.filter(id => id !== peerId), peerId]);
      };

      dataChannel.onmessage = (event) => {
        const message = JSON.parse(event.data);
        if (message.type === 'canvas-update') {
          onCanvasUpdate(message.canvas);
        }
      };

      // Handle ICE candidates
      pc.onicecandidate = (event) => {
        if (event.candidate && signalingServerRef.current) {
          signalingServerRef.current.send(JSON.stringify({
            type: 'ice-candidate',
            to: peerId,
            from: userId,
            candidate: event.candidate
          }));
        }
      };

      // Handle connection state changes
      pc.onconnectionstatechange = () => {
        console.log(`Connection state with ${peerId}:`, pc.connectionState);
        if (pc.connectionState === 'connected') {
          setIsConnected(true);
        }
      };

      // Store peer connection
      peerConnections.current.set(peerId, {
        peerId,
        connection: pc,
        dataChannel
      });

      if (isInitiator) {
        // Create and send offer
        const offer = await pc.createOffer();
        await pc.setLocalDescription(offer);
        
        if (signalingServerRef.current) {
          signalingServerRef.current.send(JSON.stringify({
            type: 'offer',
            to: peerId,
            from: userId,
            offer
          }));
        }
      }

    } catch (error) {
      console.error('Failed to create peer connection:', error);
    }
  };

  // Handle WebRTC offer
  const handleOffer = async (from: string, offer: RTCSessionDescriptionInit) => {
    const peerConnection = peerConnections.current.get(from);
    if (!peerConnection) return;

    try {
      await peerConnection.connection.setRemoteDescription(new RTCSessionDescription(offer));
      const answer = await peerConnection.connection.createAnswer();
      await peerConnection.connection.setLocalDescription(answer);

      if (signalingServerRef.current) {
        signalingServerRef.current.send(JSON.stringify({
          type: 'answer',
          to: from,
          from: userId,
          answer
        }));
      }
    } catch (error) {
      console.error('Failed to handle offer:', error);
    }
  };

  // Handle WebRTC answer
  const handleAnswer = async (from: string, answer: RTCSessionDescriptionInit) => {
    const peerConnection = peerConnections.current.get(from);
    if (!peerConnection) return;

    try {
      await peerConnection.connection.setRemoteDescription(new RTCSessionDescription(answer));
    } catch (error) {
      console.error('Failed to handle answer:', error);
    }
  };

  // Handle ICE candidate
  const handleIceCandidate = async (from: string, candidate: RTCIceCandidateInit) => {
    const peerConnection = peerConnections.current.get(from);
    if (!peerConnection) return;

    try {
      await peerConnection.connection.addIceCandidate(new RTCIceCandidate(candidate));
    } catch (error) {
      console.error('Failed to add ICE candidate:', error);
    }
  };

  // Remove peer connection
  const removePeerConnection = async (peerId: string) => {
    const peerConnection = peerConnections.current.get(peerId);
    if (peerConnection) {
      peerConnection.connection.close();
      peerConnections.current.delete(peerId);
      setConnectedPeers(prev => prev.filter(id => id !== peerId));
    }
  };

  // Broadcast canvas update to all peers
  const broadcastCanvasUpdate = useCallback((updatedCanvas: Canvas) => {
    peerConnections.current.forEach((peerConnection) => {
      if (peerConnection.dataChannel.readyState === 'open') {
        peerConnection.dataChannel.send(JSON.stringify({
          type: 'canvas-update',
          canvas: updatedCanvas
        }));
      }
    });
  }, []);

  // Connect to room
  const handleConnect = () => {
    connectToSignalingServer();
  };

  // Disconnect from room
  const handleDisconnect = () => {
    peerConnections.current.forEach((peerConnection) => {
      peerConnection.connection.close();
    });
    peerConnections.current.clear();
    
    if (signalingServerRef.current) {
      signalingServerRef.current.close();
    }
    
    setConnectedPeers([]);
    setIsConnected(false);
    setStatus('idle');
  };

  // Cleanup on unmount
  useEffect(() => {
    return () => {
      handleDisconnect();
    };
  }, []);

  return (
    <div style={{
      position: 'absolute',
      bottom: 20,
      left: 20,
      backgroundColor: 'rgba(0, 0, 0, 0.8)',
      color: 'white',
      padding: '15px',
      borderRadius: '8px',
      fontFamily: 'monospace',
      fontSize: '12px',
      zIndex: 1000,
      minWidth: '250px'
    }}>
      <h3 style={{ margin: '0 0 10px 0', fontSize: '14px' }}>
        🌐 WebRTC Collaboration
      </h3>
      
      <div style={{ marginBottom: '10px' }}>
        <label style={{ display: 'block', marginBottom: '5px' }}>Room ID:</label>
        <input
          type="text"
          value={roomIdInput}
          onChange={(e) => setRoomIdInput(e.target.value)}
          style={{
            width: '100%',
            padding: '5px',
            backgroundColor: '#333',
            border: '1px solid #555',
            color: 'white',
            borderRadius: '3px'
          }}
          disabled={status !== 'idle'}
        />
      </div>

      <div style={{ marginBottom: '10px' }}>
        <div style={{ marginBottom: '5px' }}>
          Status: <span style={{
            color: status === 'connected' ? '#4CAF50' : 
                  status === 'connecting' ? '#FF9800' : 
                  status === 'error' ? '#F44336' : '#666'
          }}>{status.toUpperCase()}</span>
        </div>
        <div style={{ marginBottom: '5px' }}>
          Host: {isHost ? 'Yes' : 'No'}
        </div>
        <div style={{ marginBottom: '5px' }}>
          Connected Peers: {connectedPeers.length}
        </div>
      </div>

      <div style={{ display: 'flex', gap: '5px' }}>
        {status === 'idle' ? (
          <button
            onClick={handleConnect}
            style={{
              padding: '5px 10px',
              backgroundColor: '#4CAF50',
              color: 'white',
              border: 'none',
              borderRadius: '3px',
              cursor: 'pointer'
            }}
          >
            Connect
          </button>
        ) : (
          <button
            onClick={handleDisconnect}
            style={{
              padding: '5px 10px',
              backgroundColor: '#F44336',
              color: 'white',
              border: 'none',
              borderRadius: '3px',
              cursor: 'pointer'
            }}
          >
            Disconnect
          </button>
        )}
      </div>

      {connectedPeers.length > 0 && (
        <div style={{ marginTop: '10px' }}>
          <strong>Connected Peers:</strong>
          <ul style={{ margin: '5px 0', paddingLeft: '20px' }}>
            {connectedPeers.map(peerId => (
              <li key={peerId} style={{ fontSize: '11px' }}>{peerId}</li>
            ))}
          </ul>
        </div>
      )}
    </div>
  );
};