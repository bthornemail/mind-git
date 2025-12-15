/**
 * MQTT Integration Component
 * Enables MQTT-based real-time collaboration and canvas synchronization
 */
import React, { useState, useEffect, useRef, useCallback } from 'react';
import { Canvas } from '../types';

interface MQTTManagerProps {
  canvas: Canvas;
  onCanvasUpdate: (canvas: Canvas) => void;
  brokerUrl?: string;
  clientId?: string;
  topicPrefix?: string;
}

interface MQTTMessage {
  topic: string;
  payload: any;
  timestamp: number;
  userId: string;
}

export const MQTTManager: React.FC<MQTTManagerProps> = ({
  canvas,
  onCanvasUpdate,
  brokerUrl = 'ws://localhost:9001', // Default MQTT WebSocket broker
  clientId = `mind-git-${Math.random().toString(16).substr(2, 8)}`,
  topicPrefix = 'mind-git/canvas'
}) => {
  const [isConnected, setIsConnected] = useState(false);
  const [messages, setMessages] = useState<MQTTMessage[]>([]);
  const [subscribedTopics, setSubscribedTopics] = useState<string[]>([]);
  const [publishTopic, setPublishTopic] = useState(`${topicPrefix}/updates`);
  const [messageInput, setMessageInput] = useState('');
  const [status, setStatus] = useState<'disconnected' | 'connecting' | 'connected' | 'error'>('disconnected');
  
  const mqttClient = useRef<any>(null);
  const reconnectTimeoutRef = useRef<NodeJS.Timeout | null>(null);

  // Initialize MQTT client
  const connectMQTT = useCallback(() => {
    try {
      // Import mqtt dynamically to avoid SSR issues
      import('mqtt').then((mqtt) => {
        setStatus('connecting');
        
        const client = mqtt.connect(brokerUrl, {
          clientId,
          clean: true,
          connectTimeout: 30000,
          reconnectPeriod: 5000,
          username: '', // Add username if needed
          password: ''  // Add password if needed
        });

        mqttClient.current = client;

        // Connection event handlers
        client.on('connect', () => {
          console.log('Connected to MQTT broker');
          setIsConnected(true);
          setStatus('connected');
          
          // Subscribe to default topics
          subscribeToTopic(`${topicPrefix}/updates`);
          subscribeToTopic(`${topicPrefix}/presence`);
          subscribeToTopic(`${topicPrefix}/commands`);
        });

        client.on('message', handleMQTTMessage);

        client.on('error', (error: any) => {
          console.error('MQTT connection error:', error);
          setStatus('error');
        });

        client.on('close', () => {
          console.log('MQTT connection closed');
          setIsConnected(false);
          setStatus('disconnected');
        });

        client.on('offline', () => {
          console.log('MQTT client offline');
          setIsConnected(false);
          setStatus('disconnected');
        });

        client.on('reconnect', () => {
          console.log('MQTT client reconnecting');
          setStatus('connecting');
        });

      }).catch((error) => {
        console.error('Failed to import mqtt library:', error);
        setStatus('error');
      });

    } catch (error) {
      console.error('Failed to connect to MQTT broker:', error);
      setStatus('error');
    }
  }, [brokerUrl, clientId, topicPrefix]);

  // Handle incoming MQTT messages
  const handleMQTTMessage = useCallback((topic: string, payload: Buffer) => {
    try {
      const message = JSON.parse(payload.toString());
      const mqttMessage: MQTTMessage = {
        topic,
        payload: message,
        timestamp: Date.now(),
        userId: message.userId || 'unknown'
      };

      // Add to messages list (keep last 50)
      setMessages(prev => [mqttMessage, ...prev.slice(0, 49)]);

      // Handle specific message types
      if (topic.includes('updates') && message.canvas) {
        onCanvasUpdate(message.canvas);
      }

      if (topic.includes('presence')) {
        console.log('Presence update:', message);
      }

      if (topic.includes('commands')) {
        console.log('Command received:', message);
        // Handle commands like refresh, reset, etc.
      }

    } catch (error) {
      console.error('Failed to parse MQTT message:', error);
    }
  }, [onCanvasUpdate]);

  // Subscribe to topic
  const subscribeToTopic = useCallback((topic: string) => {
    if (mqttClient.current && isConnected) {
      mqttClient.current.subscribe(topic, (error: any) => {
        if (error) {
          console.error('Failed to subscribe to topic:', topic, error);
        } else {
          console.log('Subscribed to topic:', topic);
          setSubscribedTopics(prev => [...new Set([...prev, topic])]);
        }
      });
    }
  }, [isConnected]);

  // Unsubscribe from topic
  const unsubscribeFromTopic = useCallback((topic: string) => {
    if (mqttClient.current && isConnected) {
      mqttClient.current.unsubscribe(topic, (error: any) => {
        if (error) {
          console.error('Failed to unsubscribe from topic:', topic, error);
        } else {
          console.log('Unsubscribed from topic:', topic);
          setSubscribedTopics(prev => prev.filter(t => t !== topic));
        }
      });
    }
  }, [isConnected]);

  // Publish message
  const publishMessage = useCallback((topic: string, message: any) => {
    if (mqttClient.current && isConnected) {
      const payload = JSON.stringify({
        ...message,
        userId: clientId,
        timestamp: Date.now()
      });

      mqttClient.current.publish(topic, payload, (error: any) => {
        if (error) {
          console.error('Failed to publish message:', error);
        } else {
          console.log('Message published to:', topic);
        }
      });
    }
  }, [isConnected, clientId]);

  // Broadcast canvas update
  const broadcastCanvasUpdate = useCallback((updatedCanvas: Canvas) => {
    publishMessage(`${topicPrefix}/updates`, {
      type: 'canvas-update',
      canvas: updatedCanvas,
      nodeId: updatedCanvas.nodes.map(n => n.id),
      edgeCount: updatedCanvas.edges.length
    });
  }, [publishMessage, topicPrefix]);

  // Send presence update
  const sendPresenceUpdate = useCallback((status: string) => {
    publishMessage(`${topicPrefix}/presence`, {
      type: 'presence',
      status,
      userAgent: navigator.userAgent,
      timestamp: Date.now()
    });
  }, [publishMessage, topicPrefix]);

  // Send command
  const sendCommand = useCallback((command: string, data?: any) => {
    publishMessage(`${topicPrefix}/commands`, {
      type: 'command',
      command,
      data,
      timestamp: Date.now()
    });
  }, [publishMessage, topicPrefix]);

  // Connect/Disconnect handlers
  const handleConnect = () => {
    connectMQTT();
  };

  const handleDisconnect = () => {
    if (mqttClient.current) {
      mqttClient.current.end();
      mqttClient.current = null;
    }
    setIsConnected(false);
    setStatus('disconnected');
    setSubscribedTopics([]);
  };

  // Publish custom message
  const handlePublishMessage = () => {
    if (messageInput.trim()) {
      try {
        const payload = JSON.parse(messageInput);
        publishMessage(publishTopic, payload);
        setMessageInput('');
      } catch (error) {
        // If not JSON, send as string
        publishMessage(publishTopic, { message: messageInput });
        setMessageInput('');
      }
    }
  };

  // Auto-connect on mount
  useEffect(() => {
    handleConnect();
    return () => {
      handleDisconnect();
    };
  }, []);

  // Send presence updates periodically
  useEffect(() => {
    if (isConnected) {
      sendPresenceUpdate('online');
      const interval = setInterval(() => {
        sendPresenceUpdate('heartbeat');
      }, 30000); // Every 30 seconds

      return () => clearInterval(interval);
    }
  }, [isConnected, sendPresenceUpdate]);

  return (
    <div style={{
      position: 'absolute',
      top: 20,
      left: 340,
      backgroundColor: 'rgba(0, 0, 0, 0.8)',
      color: 'white',
      padding: '15px',
      borderRadius: '8px',
      fontFamily: 'monospace',
      fontSize: '12px',
      zIndex: 1000,
      minWidth: '300px',
      maxHeight: '400px',
      overflow: 'auto'
    }}>
      <h3 style={{ margin: '0 0 10px 0', fontSize: '14px' }}>
        📡 MQTT Collaboration
      </h3>
      
      <div style={{ marginBottom: '10px' }}>
        <div style={{ marginBottom: '5px' }}>
          Status: <span style={{
            color: status === 'connected' ? '#4CAF50' : 
                  status === 'connecting' ? '#FF9800' : 
                  status === 'error' ? '#F44336' : '#666'
          }}>{status.toUpperCase()}</span>
        </div>
        <div style={{ marginBottom: '5px' }}>
          Broker: {brokerUrl}
        </div>
        <div style={{ marginBottom: '5px' }}>
          Client ID: {clientId}
        </div>
      </div>

      <div style={{ marginBottom: '10px' }}>
        <div style={{ marginBottom: '5px' }}>
          <strong>Subscribed Topics ({subscribedTopics.length}):</strong>
        </div>
        <ul style={{ margin: '5px 0', paddingLeft: '20px', fontSize: '10px' }}>
          {subscribedTopics.map(topic => (
            <li key={topic} style={{ wordBreak: 'break-all' }}>{topic}</li>
          ))}
        </ul>
      </div>

      <div style={{ marginBottom: '10px' }}>
        <label style={{ display: 'block', marginBottom: '5px' }}>Publish Topic:</label>
        <input
          type="text"
          value={publishTopic}
          onChange={(e) => setPublishTopic(e.target.value)}
          style={{
            width: '100%',
            padding: '3px',
            backgroundColor: '#333',
            border: '1px solid #555',
            color: 'white',
            borderRadius: '3px',
            fontSize: '10px',
            marginBottom: '5px'
          }}
        />
      </div>

      <div style={{ marginBottom: '10px' }}>
        <label style={{ display: 'block', marginBottom: '5px' }}>Message (JSON):</label>
        <textarea
          value={messageInput}
          onChange={(e) => setMessageInput(e.target.value)}
          placeholder='{"type": "test", "data": "hello"}'
          style={{
            width: '100%',
            height: '60px',
            padding: '3px',
            backgroundColor: '#333',
            border: '1px solid #555',
            color: 'white',
            borderRadius: '3px',
            fontSize: '10px',
            resize: 'vertical'
          }}
        />
      </div>

      <div style={{ display: 'flex', gap: '5px', marginBottom: '10px' }}>
        <button
          onClick={handlePublishMessage}
          disabled={!isConnected || !messageInput.trim()}
          style={{
            padding: '5px 8px',
            backgroundColor: isConnected ? '#4CAF50' : '#666',
            color: 'white',
            border: 'none',
            borderRadius: '3px',
            cursor: isConnected ? 'pointer' : 'not-allowed',
            fontSize: '10px'
          }}
        >
          Publish
        </button>
        
        <button
          onClick={() => sendCommand('refresh')}
          disabled={!isConnected}
          style={{
            padding: '5px 8px',
            backgroundColor: isConnected ? '#2196F3' : '#666',
            color: 'white',
            border: 'none',
            borderRadius: '3px',
            cursor: isConnected ? 'pointer' : 'not-allowed',
            fontSize: '10px'
          }}
        >
          Refresh
        </button>
        
        <button
          onClick={() => broadcastCanvasUpdate(canvas)}
          disabled={!isConnected}
          style={{
            padding: '5px 8px',
            backgroundColor: isConnected ? '#FF9800' : '#666',
            color: 'white',
            border: 'none',
            borderRadius: '3px',
            cursor: isConnected ? 'pointer' : 'not-allowed',
            fontSize: '10px'
          }}
        >
          Sync Canvas
        </button>
      </div>

      <div style={{ display: 'flex', gap: '5px' }}>
        {status === 'disconnected' ? (
          <button
            onClick={handleConnect}
            style={{
              padding: '5px 10px',
              backgroundColor: '#4CAF50',
              color: 'white',
              border: 'none',
              borderRadius: '3px',
              cursor: 'pointer',
              fontSize: '10px'
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
              cursor: 'pointer',
              fontSize: '10px'
            }}
          >
            Disconnect
          </button>
        )}
      </div>

      {messages.length > 0 && (
        <div style={{ marginTop: '10px' }}>
          <strong>Recent Messages ({messages.length}):</strong>
          <div style={{ maxHeight: '150px', overflow: 'auto', marginTop: '5px' }}>
            {messages.slice(0, 5).map((msg, index) => (
              <div key={index} style={{
                backgroundColor: '#222',
                padding: '3px',
                margin: '2px 0',
                borderRadius: '3px',
                fontSize: '9px',
                wordBreak: 'break-all'
              }}>
                <div style={{ color: '#888', fontSize: '8px' }}>
                  {new Date(msg.timestamp).toLocaleTimeString()} - {msg.topic}
                </div>
                <div>{JSON.stringify(msg.payload, null, 2)}</div>
              </div>
            ))}
          </div>
        </div>
      )}
    </div>
  );
};