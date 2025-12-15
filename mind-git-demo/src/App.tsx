import React, { useState, useCallback } from 'react';
import './App.css';
import { Canvas3D } from './components/Canvas3D';
import { WebRTCManager } from './components/WebRTCManager';
import { MQTTManager } from './components/MQTTManager';
import { exampleCanvas } from './exampleCanvas';
import { Canvas } from './types';
import { SCENES } from './scenes';

function App() {
  const [currentCanvas, setCurrentCanvas] = useState<Canvas>(exampleCanvas);
  const [currentSceneId, setCurrentSceneId] = useState<string>('example');
  const [userId] = useState(() => `user-${Math.random().toString(16).substr(2, 8)}`);
  const [roomId] = useState(() => `room-${Math.random().toString(16).substr(2, 8)}`);

  const handleSceneChange = useCallback((sceneId: string) => {
    const scene = SCENES.find(s => s.id === sceneId);
    if (scene) {
      setCurrentCanvas(scene.canvas);
      setCurrentSceneId(sceneId);
    }
  }, []);

  const handleCanvasUpdate = useCallback((updatedCanvas: Canvas) => {
    setCurrentCanvas(updatedCanvas);
  }, []);

  return (
    <div className="App">
      <Canvas3D 
        canvas={currentCanvas} 
        onSceneChange={handleSceneChange}
        currentSceneId={currentSceneId}
      />
      
      {/* WebRTC Collaboration */}
      <WebRTCManager
        canvas={currentCanvas}
        onCanvasUpdate={handleCanvasUpdate}
        roomId={roomId}
        userId={userId}
      />
      
      {/* MQTT Integration */}
      <MQTTManager
        canvas={currentCanvas}
        onCanvasUpdate={handleCanvasUpdate}
        brokerUrl="ws://localhost:9001"
        clientId={userId}
        topicPrefix="mind-git/canvas"
      />
    </div>
  );
}

export default App;
