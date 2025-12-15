/**
 * Scene Switcher Component
 * Allows users to switch between different example canvas scenes
 */

import React, { useState } from 'react';
import { SCENES, Scene, getAllSceneTags } from '../scenes';

interface SceneSwitcherProps {
  currentSceneId: string;
  onSceneChange: (scene: Scene) => void;
}

export const SceneSwitcher: React.FC<SceneSwitcherProps> = ({
  currentSceneId,
  onSceneChange,
}) => {
  const [showPanel, setShowPanel] = useState(false);
  const [selectedTag, setSelectedTag] = useState<string | null>(null);

  const allTags = getAllSceneTags();
  const currentScene = SCENES.find((s) => s.id === currentSceneId);

  // Filter scenes by tag
  const displayedScenes = selectedTag
    ? SCENES.filter((scene) => scene.tags.includes(selectedTag))
    : SCENES;

  const handleSceneSelect = (scene: Scene) => {
    onSceneChange(scene);
    setShowPanel(false);
  };

  return (
    <>
      {/* Main button */}
      <button
        onClick={() => setShowPanel(!showPanel)}
        style={{
          position: 'absolute',
          top: 80,
          right: 20,
          padding: '12px 20px',
          backgroundColor: '#95E1D3',
          color: '#000',
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
        {showPanel ? '✕ Close' : '🎬 Switch Scene'}
      </button>

      {/* Scene panel */}
      {showPanel && (
        <div
          style={{
            position: 'absolute',
            top: 140,
            right: 20,
            width: '400px',
            maxHeight: '70vh',
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
          <h3 style={{ margin: '0 0 10px 0', fontSize: '18px', color: '#95E1D3' }}>
            Select Scene
          </h3>

          {/* Current scene */}
          {currentScene && (
            <div
              style={{
                padding: '12px',
                backgroundColor: 'rgba(149, 225, 211, 0.1)',
                borderRadius: '6px',
                marginBottom: '15px',
                fontSize: '12px',
              }}
            >
              <p style={{ margin: 0, fontWeight: 'bold' }}>
                Current: {currentScene.name}
              </p>
              <p style={{ margin: '5px 0 0 0', color: '#aaa' }}>
                {currentScene.description}
              </p>
            </div>
          )}

          {/* Tag filters */}
          <div style={{ marginBottom: '15px' }}>
            <label style={{ display: 'block', marginBottom: '8px', fontSize: '12px' }}>
              🏷️ Filter by Tag
            </label>
            <div style={{ display: 'flex', flexWrap: 'wrap', gap: '6px' }}>
              <TagButton
                active={selectedTag === null}
                onClick={() => setSelectedTag(null)}
                label="All"
              />
              {allTags.map((tag) => (
                <TagButton
                  key={tag}
                  active={selectedTag === tag}
                  onClick={() => setSelectedTag(tag)}
                  label={tag}
                />
              ))}
            </div>
          </div>

          {/* Scene list */}
          <div style={{ display: 'flex', flexDirection: 'column', gap: '12px' }}>
            {displayedScenes.map((scene) => (
              <SceneCard
                key={scene.id}
                scene={scene}
                isCurrent={scene.id === currentSceneId}
                onClick={() => handleSceneSelect(scene)}
              />
            ))}
          </div>

          {/* Info */}
          <div
            style={{
              marginTop: '20px',
              padding: '12px',
              backgroundColor: 'rgba(255, 255, 255, 0.05)',
              borderRadius: '6px',
              fontSize: '11px',
              color: '#888',
            }}
          >
            <p style={{ margin: 0 }}>
              {displayedScenes.length} scene{displayedScenes.length !== 1 ? 's' : ''}{' '}
              available
            </p>
            <p style={{ margin: '5px 0 0 0' }}>
              Click any scene card to load it
            </p>
          </div>
        </div>
      )}
    </>
  );
};

// Helper components

const TagButton: React.FC<{
  active: boolean;
  onClick: () => void;
  label: string;
}> = ({ active, onClick, label }) => (
  <button
    onClick={onClick}
    style={{
      padding: '5px 10px',
      backgroundColor: active ? '#95E1D3' : '#1a1a1a',
      color: active ? '#000' : '#fff',
      border: '1px solid' + (active ? '#95E1D3' : '#444'),
      borderRadius: '4px',
      cursor: 'pointer',
      fontSize: '11px',
      fontWeight: active ? 'bold' : 'normal',
    }}
  >
    {label}
  </button>
);

const SceneCard: React.FC<{
  scene: Scene;
  isCurrent: boolean;
  onClick: () => void;
}> = ({ scene, isCurrent, onClick }) => (
  <div
    onClick={isCurrent ? undefined : onClick}
    style={{
      padding: '15px',
      backgroundColor: isCurrent ? 'rgba(149, 225, 211, 0.2)' : '#1a1a1a',
      border: `2px solid ${isCurrent ? '#95E1D3' : '#333'}`,
      borderRadius: '8px',
      cursor: isCurrent ? 'default' : 'pointer',
      transition: 'all 0.2s',
    }}
    onMouseEnter={(e) => {
      if (!isCurrent) {
        e.currentTarget.style.borderColor = '#95E1D3';
        e.currentTarget.style.backgroundColor = '#222';
      }
    }}
    onMouseLeave={(e) => {
      if (!isCurrent) {
        e.currentTarget.style.borderColor = '#333';
        e.currentTarget.style.backgroundColor = '#1a1a1a';
      }
    }}
  >
    {/* Header */}
    <div style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'start' }}>
      <h4 style={{ margin: '0 0 8px 0', fontSize: '15px', color: '#95E1D3' }}>
        {scene.name}
      </h4>
      {isCurrent && (
        <span
          style={{
            padding: '3px 8px',
            backgroundColor: '#95E1D3',
            color: '#000',
            fontSize: '10px',
            borderRadius: '3px',
            fontWeight: 'bold',
          }}
        >
          ACTIVE
        </span>
      )}
    </div>

    {/* Description */}
    <p style={{ margin: '0 0 10px 0', fontSize: '12px', color: '#ccc', lineHeight: '1.4' }}>
      {scene.description}
    </p>

    {/* Tags */}
    <div style={{ display: 'flex', flexWrap: 'wrap', gap: '4px' }}>
      {scene.tags.map((tag) => (
        <span
          key={tag}
          style={{
            padding: '3px 8px',
            backgroundColor: '#333',
            color: '#aaa',
            fontSize: '10px',
            borderRadius: '3px',
          }}
        >
          {tag}
        </span>
      ))}
    </div>

    {/* Stats */}
    <div
      style={{
        marginTop: '10px',
        paddingTop: '10px',
        borderTop: '1px solid #333',
        fontSize: '11px',
        color: '#666',
        display: 'flex',
        gap: '15px',
      }}
    >
      <span>📦 {scene.canvas.nodes.length} nodes</span>
      <span>🔗 {scene.canvas.edges.length} edges</span>
    </div>
  </div>
);
