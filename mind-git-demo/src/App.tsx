import React from 'react';
import './App.css';
import { Canvas3D } from './components/Canvas3D';
import { exampleCanvas } from './exampleCanvas';

function App() {
  return (
    <div className="App">
      <Canvas3D canvas={exampleCanvas} />
    </div>
  );
}

export default App;
