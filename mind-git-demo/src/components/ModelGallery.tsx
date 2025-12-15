/**
 * Model Gallery Component
 *
 * Browse and select models from the Khronos glTF Sample Models library
 */

import React, { useState, useMemo } from 'react';
import { NodeType } from '../types';
import {
  KHRONOS_MODELS,
  KhronosModel,
  getModelsForNodeType,
  getSuggestedModels,
  getAllTags,
  searchModels,
  getAttribution,
} from '../services/modelLibrary';

interface ModelGalleryProps {
  nodeType?: NodeType;
  onSelectModel: (model: KhronosModel) => void;
  onClose: () => void;
}

export const ModelGallery: React.FC<ModelGalleryProps> = ({
  nodeType,
  onSelectModel,
  onClose,
}) => {
  const [searchQuery, setSearchQuery] = useState('');
  const [selectedTag, setSelectedTag] = useState<string | null>(null);
  const [viewMode, setViewMode] = useState<'all' | 'suitable' | 'suggested'>('suggested');

  const allTags = useMemo(() => getAllTags(), []);

  // Filter models based on view mode, search, and tag
  const displayedModels = useMemo(() => {
    let models: KhronosModel[] = [];

    // First filter by view mode
    switch (viewMode) {
      case 'suggested':
        models = nodeType ? getSuggestedModels(nodeType) : KHRONOS_MODELS;
        break;
      case 'suitable':
        models = nodeType ? getModelsForNodeType(nodeType) : KHRONOS_MODELS;
        break;
      case 'all':
      default:
        models = KHRONOS_MODELS;
    }

    // Then filter by search query
    if (searchQuery) {
      models = searchModels(searchQuery).filter((m) => models.includes(m));
    }

    // Finally filter by tag
    if (selectedTag) {
      models = models.filter((m) => m.tags.includes(selectedTag));
    }

    return models;
  }, [viewMode, searchQuery, selectedTag, nodeType]);

  const handleModelClick = (model: KhronosModel) => {
    onSelectModel(model);
    onClose();
  };

  return (
    <div
      style={{
        position: 'fixed',
        top: 0,
        left: 0,
        right: 0,
        bottom: 0,
        backgroundColor: 'rgba(0, 0, 0, 0.9)',
        zIndex: 2000,
        overflowY: 'auto',
        padding: '20px',
      }}
    >
      <div
        style={{
          maxWidth: '1200px',
          margin: '0 auto',
          color: 'white',
          fontFamily: 'monospace',
        }}
      >
        {/* Header */}
        <div
          style={{
            display: 'flex',
            justifyContent: 'space-between',
            alignItems: 'center',
            marginBottom: '20px',
          }}
        >
          <h1 style={{ margin: 0, fontSize: '24px', color: '#4ECDC4' }}>
            📦 Khronos glTF Model Library
          </h1>
          <button
            onClick={onClose}
            style={{
              padding: '10px 20px',
              backgroundColor: '#FF6B6B',
              color: 'white',
              border: 'none',
              borderRadius: '6px',
              cursor: 'pointer',
              fontSize: '14px',
              fontWeight: 'bold',
            }}
          >
            ✕ Close
          </button>
        </div>

        {/* Node type info */}
        {nodeType && (
          <div
            style={{
              padding: '15px',
              backgroundColor: 'rgba(78, 205, 196, 0.1)',
              borderRadius: '6px',
              marginBottom: '20px',
              fontSize: '14px',
            }}
          >
            <p style={{ margin: 0 }}>
              Selecting model for: <strong>{nodeType}</strong> node
            </p>
          </div>
        )}

        {/* Controls */}
        <div
          style={{
            display: 'grid',
            gridTemplateColumns: '1fr 1fr',
            gap: '15px',
            marginBottom: '20px',
          }}
        >
          {/* Search */}
          <div>
            <label style={{ display: 'block', marginBottom: '5px', fontSize: '12px' }}>
              🔍 Search Models
            </label>
            <input
              type="text"
              value={searchQuery}
              onChange={(e) => setSearchQuery(e.target.value)}
              placeholder="Search by name, description, or tag..."
              style={{
                width: '100%',
                padding: '10px',
                backgroundColor: '#1a1a1a',
                color: 'white',
                border: '1px solid #444',
                borderRadius: '6px',
                fontSize: '14px',
                fontFamily: 'monospace',
              }}
            />
          </div>

          {/* View Mode */}
          <div>
            <label style={{ display: 'block', marginBottom: '5px', fontSize: '12px' }}>
              👁️ View Mode
            </label>
            <div style={{ display: 'flex', gap: '5px' }}>
              <ViewModeButton
                active={viewMode === 'suggested'}
                onClick={() => setViewMode('suggested')}
                label="Suggested"
                disabled={!nodeType}
              />
              <ViewModeButton
                active={viewMode === 'suitable'}
                onClick={() => setViewMode('suitable')}
                label="Suitable"
                disabled={!nodeType}
              />
              <ViewModeButton
                active={viewMode === 'all'}
                onClick={() => setViewMode('all')}
                label="All"
              />
            </div>
          </div>
        </div>

        {/* Tags */}
        <div style={{ marginBottom: '20px' }}>
          <label style={{ display: 'block', marginBottom: '8px', fontSize: '12px' }}>
            🏷️ Filter by Tag
          </label>
          <div style={{ display: 'flex', flexWrap: 'wrap', gap: '8px' }}>
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

        {/* Results count */}
        <div style={{ marginBottom: '15px', fontSize: '12px', color: '#888' }}>
          Showing {displayedModels.length} model{displayedModels.length !== 1 ? 's' : ''}
        </div>

        {/* Model Grid */}
        <div
          style={{
            display: 'grid',
            gridTemplateColumns: 'repeat(auto-fill, minmax(250px, 1fr))',
            gap: '20px',
            marginBottom: '20px',
          }}
        >
          {displayedModels.map((model) => (
            <ModelCard
              key={model.name}
              model={model}
              onClick={() => handleModelClick(model)}
            />
          ))}
        </div>

        {/* No results */}
        {displayedModels.length === 0 && (
          <div
            style={{
              padding: '40px',
              textAlign: 'center',
              backgroundColor: 'rgba(255, 255, 255, 0.05)',
              borderRadius: '8px',
              fontSize: '14px',
              color: '#888',
            }}
          >
            <p style={{ margin: 0, marginBottom: '10px', fontSize: '48px' }}>🔍</p>
            <p style={{ margin: 0 }}>No models found</p>
            <p style={{ margin: '5px 0 0 0', fontSize: '12px' }}>
              Try adjusting your filters or search query
            </p>
          </div>
        )}

        {/* Attribution */}
        <div
          style={{
            marginTop: '30px',
            padding: '20px',
            backgroundColor: 'rgba(255, 255, 255, 0.05)',
            borderRadius: '8px',
            fontSize: '11px',
            color: '#888',
          }}
        >
          <p style={{ margin: '0 0 5px 0', fontWeight: 'bold' }}>
            Attribution & Licensing
          </p>
          <p style={{ margin: '0 0 5px 0' }}>
            Models from the{' '}
            <a
              href="https://github.com/KhronosGroup/glTF-Sample-Models"
              target="_blank"
              rel="noopener noreferrer"
              style={{ color: '#4ECDC4' }}
            >
              Khronos Group glTF Sample Models
            </a>{' '}
            repository.
          </p>
          <p style={{ margin: 0 }}>
            Each model has its own license (CC0, CC BY, CC BY-NC). See individual model
            details for specific licensing information.
          </p>
        </div>
      </div>
    </div>
  );
};

// Helper components

const ViewModeButton: React.FC<{
  active: boolean;
  onClick: () => void;
  label: string;
  disabled?: boolean;
}> = ({ active, onClick, label, disabled }) => (
  <button
    onClick={onClick}
    disabled={disabled}
    style={{
      flex: 1,
      padding: '10px',
      backgroundColor: active ? '#4ECDC4' : disabled ? '#333' : '#1a1a1a',
      color: active ? '#000' : disabled ? '#666' : '#fff',
      border: '1px solid' + (active ? '#4ECDC4' : '#444'),
      borderRadius: '6px',
      cursor: disabled ? 'not-allowed' : 'pointer',
      fontSize: '12px',
      fontWeight: active ? 'bold' : 'normal',
      opacity: disabled ? 0.5 : 1,
    }}
  >
    {label}
  </button>
);

const TagButton: React.FC<{
  active: boolean;
  onClick: () => void;
  label: string;
}> = ({ active, onClick, label }) => (
  <button
    onClick={onClick}
    style={{
      padding: '6px 12px',
      backgroundColor: active ? '#AA96DA' : '#1a1a1a',
      color: active ? '#000' : '#fff',
      border: '1px solid' + (active ? '#AA96DA' : '#444'),
      borderRadius: '4px',
      cursor: 'pointer',
      fontSize: '11px',
      fontWeight: active ? 'bold' : 'normal',
    }}
  >
    {label}
  </button>
);

const ModelCard: React.FC<{
  model: KhronosModel;
  onClick: () => void;
}> = ({ model, onClick }) => (
  <div
    onClick={onClick}
    style={{
      backgroundColor: '#1a1a1a',
      border: '2px solid #333',
      borderRadius: '8px',
      padding: '15px',
      cursor: 'pointer',
      transition: 'all 0.2s',
    }}
    onMouseEnter={(e) => {
      e.currentTarget.style.borderColor = '#4ECDC4';
      e.currentTarget.style.backgroundColor = '#222';
    }}
    onMouseLeave={(e) => {
      e.currentTarget.style.borderColor = '#333';
      e.currentTarget.style.backgroundColor = '#1a1a1a';
    }}
  >
    {/* Screenshot */}
    {model.screenshot && (
      <div
        style={{
          width: '100%',
          height: '150px',
          backgroundColor: '#000',
          borderRadius: '6px',
          marginBottom: '12px',
          overflow: 'hidden',
          display: 'flex',
          alignItems: 'center',
          justifyContent: 'center',
        }}
      >
        <img
          src={model.screenshot}
          alt={model.name}
          style={{
            maxWidth: '100%',
            maxHeight: '100%',
            objectFit: 'contain',
          }}
          onError={(e) => {
            e.currentTarget.style.display = 'none';
          }}
        />
      </div>
    )}

    {/* Name */}
    <h3
      style={{
        margin: '0 0 8px 0',
        fontSize: '16px',
        color: '#4ECDC4',
        fontWeight: 'bold',
      }}
    >
      {model.name}
    </h3>

    {/* Description */}
    <p
      style={{
        margin: '0 0 10px 0',
        fontSize: '12px',
        color: '#ccc',
        lineHeight: '1.4',
      }}
    >
      {model.description}
    </p>

    {/* Tags */}
    <div style={{ display: 'flex', flexWrap: 'wrap', gap: '4px', marginBottom: '10px' }}>
      {model.tags.slice(0, 3).map((tag) => (
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

    {/* License */}
    <div style={{ fontSize: '10px', color: '#666' }}>
      {model.license}
      {model.author && ` • ${model.author}`}
    </div>
  </div>
);
