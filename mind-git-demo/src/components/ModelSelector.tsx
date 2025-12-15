/**
 * Model Selector Button
 *
 * Floating button to open the model gallery and customize node appearances
 */

import React, { useState } from 'react';
import { NodeType } from '../types';
import { KhronosModel } from '../services/modelLibrary';
import { ModelGallery } from './ModelGallery';

interface ModelConfig {
  nodeType: NodeType;
  model: KhronosModel | null;
}

interface ModelSelectorProps {
  onModelChange: (nodeType: NodeType, model: KhronosModel) => void;
}

export const ModelSelector: React.FC<ModelSelectorProps> = ({ onModelChange }) => {
  const [showGallery, setShowGallery] = useState(false);
  const [showPanel, setShowPanel] = useState(false);
  const [selectedNodeType, setSelectedNodeType] = useState<NodeType | undefined>();
  const [modelConfigs, setModelConfigs] = useState<Map<NodeType, KhronosModel>>(
    new Map()
  );

  const handleOpenGallery = (nodeType?: NodeType) => {
    setSelectedNodeType(nodeType);
    setShowGallery(true);
  };

  const handleSelectModel = (model: KhronosModel) => {
    if (selectedNodeType) {
      setModelConfigs(new Map(modelConfigs.set(selectedNodeType, model)));
      onModelChange(selectedNodeType, model);
    }
  };

  const nodeTypes = Object.values(NodeType);

  return (
    <>
      {/* Main button */}
      <button
        onClick={() => setShowPanel(!showPanel)}
        style={{
          position: 'absolute',
          bottom: 20,
          left: 20,
          padding: '12px 20px',
          backgroundColor: '#AA96DA',
          color: 'white',
          border: 'none',
          borderRadius: '8px',
          cursor: 'pointer',
          fontFamily: 'monospace',
          fontSize: '14px',
          fontWeight: 'bold',
          zIndex: 1001,
          boxShadow: '0 4px 6px rgba(0, 0, 0, 0.3)',
        }}
      >
        {showPanel ? '✕ Close Models' : '🎨 Customize Models'}
      </button>

      {/* Model configuration panel */}
      {showPanel && (
        <div
          style={{
            position: 'absolute',
            bottom: 80,
            left: 20,
            width: '350px',
            maxHeight: '60vh',
            backgroundColor: 'rgba(0, 0, 0, 0.9)',
            color: 'white',
            fontFamily: 'monospace',
            borderRadius: '8px',
            padding: '20px',
            zIndex: 1000,
            overflowY: 'auto',
            boxShadow: '0 8px 16px rgba(0, 0, 0, 0.5)',
          }}
        >
          <h3 style={{ margin: '0 0 15px 0', fontSize: '16px', color: '#AA96DA' }}>
            Khronos Model Library
          </h3>

          <p style={{ margin: '0 0 15px 0', fontSize: '12px', color: '#aaa' }}>
            Select official glTF models from Khronos Group for each node type.
          </p>

          {/* Browse all button */}
          <button
            onClick={() => handleOpenGallery(undefined)}
            style={{
              width: '100%',
              padding: '12px',
              backgroundColor: '#4ECDC4',
              color: '#000',
              border: 'none',
              borderRadius: '6px',
              cursor: 'pointer',
              fontSize: '13px',
              fontWeight: 'bold',
              marginBottom: '20px',
            }}
          >
            📦 Browse All Models
          </button>

          {/* Node type list */}
          <div style={{ display: 'flex', flexDirection: 'column', gap: '10px' }}>
            {nodeTypes.map((nodeType) => {
              const currentModel = modelConfigs.get(nodeType);
              return (
                <div
                  key={nodeType}
                  style={{
                    padding: '12px',
                    backgroundColor: '#1a1a1a',
                    borderRadius: '6px',
                    border: '1px solid #333',
                  }}
                >
                  <div
                    style={{
                      display: 'flex',
                      justifyContent: 'space-between',
                      alignItems: 'center',
                      marginBottom: currentModel ? '8px' : 0,
                    }}
                  >
                    <span style={{ fontSize: '13px', fontWeight: 'bold' }}>
                      {nodeType}
                    </span>
                    <button
                      onClick={() => handleOpenGallery(nodeType)}
                      style={{
                        padding: '6px 12px',
                        backgroundColor: '#AA96DA',
                        color: 'white',
                        border: 'none',
                        borderRadius: '4px',
                        cursor: 'pointer',
                        fontSize: '11px',
                      }}
                    >
                      Select Model
                    </button>
                  </div>
                  {currentModel && (
                    <div style={{ fontSize: '11px', color: '#888' }}>
                      Current: {currentModel.name}
                    </div>
                  )}
                </div>
              );
            })}
          </div>

          {/* Info */}
          <div
            style={{
              marginTop: '20px',
              padding: '12px',
              backgroundColor: 'rgba(78, 205, 196, 0.1)',
              borderRadius: '6px',
              fontSize: '11px',
              color: '#aaa',
            }}
          >
            <p style={{ margin: 0 }}>
              Models are loaded from the official{' '}
              <a
                href="https://github.com/KhronosGroup/glTF-Sample-Models"
                target="_blank"
                rel="noopener noreferrer"
                style={{ color: '#4ECDC4' }}
              >
                Khronos glTF repository
              </a>
              .
            </p>
          </div>
        </div>
      )}

      {/* Model gallery */}
      {showGallery && (
        <ModelGallery
          nodeType={selectedNodeType}
          onSelectModel={handleSelectModel}
          onClose={() => setShowGallery(false)}
        />
      )}
    </>
  );
};
