import React, { useState, useEffect } from 'react';
import { Canvas } from '../types';
import { compileCanvas, validateCanvas, CompilationResult } from '../services/compiler';

interface CompilerPanelProps {
  canvas: Canvas;
}

export const CompilerPanel: React.FC<CompilerPanelProps> = ({ canvas }) => {
  const [compilationResult, setCompilationResult] = useState<CompilationResult | null>(null);
  const [isCompiling, setIsCompiling] = useState(false);
  const [selectedOutput, setSelectedOutput] = useState<'aal' | 'javascript' | 'ast'>('aal');
  const [showPanel, setShowPanel] = useState(false);

  const handleCompile = async () => {
    setIsCompiling(true);
    const result = await compileCanvas(canvas);
    setCompilationResult(result);
    setIsCompiling(false);
  };

  const validation = validateCanvas(canvas);

  return (
    <>
      {/* Floating compile button */}
      <button
        onClick={() => setShowPanel(!showPanel)}
        style={{
          position: 'absolute',
          top: 20,
          right: 20,
          padding: '12px 20px',
          backgroundColor: '#4ECDC4',
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
        {showPanel ? '✕ Close Compiler' : '⚡ Open Compiler'}
      </button>

      {/* Compiler panel */}
      {showPanel && (
        <div
          style={{
            position: 'absolute',
            top: 80,
            right: 20,
            width: '500px',
            maxHeight: '80vh',
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
          <h2 style={{ margin: '0 0 15px 0', fontSize: '18px', color: '#4ECDC4' }}>
            CanvasL Compiler
          </h2>

          {/* Validation section */}
          <div style={{ marginBottom: '20px' }}>
            <h3 style={{ margin: '0 0 10px 0', fontSize: '14px', color: '#95E1D3' }}>
              Validation
            </h3>
            <div
              style={{
                padding: '10px',
                backgroundColor: validation.valid
                  ? 'rgba(0, 255, 0, 0.1)'
                  : 'rgba(255, 255, 0, 0.1)',
                borderRadius: '4px',
                fontSize: '12px',
              }}
            >
              {validation.valid ? (
                <p style={{ margin: 0, color: '#4ECDC4' }}>✓ Canvas structure valid</p>
              ) : (
                <>
                  <p style={{ margin: '0 0 5px 0', color: '#FFD700' }}>
                    ⚠ Validation warnings:
                  </p>
                  {validation.errors.map((error, i) => (
                    <p key={i} style={{ margin: '3px 0 3px 15px', fontSize: '11px' }}>
                      • {error}
                    </p>
                  ))}
                </>
              )}
            </div>
          </div>

          {/* Compile button */}
          <button
            onClick={handleCompile}
            disabled={isCompiling}
            style={{
              width: '100%',
              padding: '12px',
              backgroundColor: isCompiling ? '#666' : '#AA96DA',
              color: 'white',
              border: 'none',
              borderRadius: '6px',
              cursor: isCompiling ? 'not-allowed' : 'pointer',
              fontSize: '14px',
              fontWeight: 'bold',
              marginBottom: '20px',
            }}
          >
            {isCompiling ? 'Compiling...' : '⚡ Compile Canvas'}
          </button>

          {/* Compilation results */}
          {compilationResult && (
            <>
              {compilationResult.success ? (
                <>
                  <div style={{ marginBottom: '15px' }}>
                    <h3 style={{ margin: '0 0 10px 0', fontSize: '14px', color: '#95E1D3' }}>
                      Output Format
                    </h3>
                    <div style={{ display: 'flex', gap: '8px' }}>
                      <OutputButton
                        label="AAL Assembly"
                        selected={selectedOutput === 'aal'}
                        onClick={() => setSelectedOutput('aal')}
                      />
                      <OutputButton
                        label="JavaScript"
                        selected={selectedOutput === 'javascript'}
                        onClick={() => setSelectedOutput('javascript')}
                      />
                      <OutputButton
                        label="AST"
                        selected={selectedOutput === 'ast'}
                        onClick={() => setSelectedOutput('ast')}
                      />
                    </div>
                  </div>

                  <div
                    style={{
                      backgroundColor: '#1a1a1a',
                      padding: '15px',
                      borderRadius: '6px',
                      fontSize: '11px',
                      lineHeight: '1.5',
                      overflowX: 'auto',
                      maxHeight: '400px',
                      overflowY: 'auto',
                    }}
                  >
                    <pre style={{ margin: 0, whiteSpace: 'pre-wrap' }}>
                      {selectedOutput === 'aal' && compilationResult.aal}
                      {selectedOutput === 'javascript' && compilationResult.javascript}
                      {selectedOutput === 'ast' &&
                        JSON.stringify(compilationResult.ast, null, 2)}
                    </pre>
                  </div>

                  <div style={{ marginTop: '15px', fontSize: '11px', color: '#888' }}>
                    <p style={{ margin: '5px 0' }}>
                      ℹ️ This is a mock compilation output. Full integration with logos-system
                      compiler coming soon.
                    </p>
                  </div>
                </>
              ) : (
                <div
                  style={{
                    padding: '15px',
                    backgroundColor: 'rgba(255, 0, 0, 0.1)',
                    borderRadius: '6px',
                    color: '#FF6B6B',
                  }}
                >
                  <p style={{ margin: '0 0 10px 0', fontWeight: 'bold' }}>
                    ❌ Compilation Failed
                  </p>
                  {compilationResult.errors?.map((error, i) => (
                    <p key={i} style={{ margin: '5px 0', fontSize: '12px' }}>
                      • {error}
                    </p>
                  ))}
                </div>
              )}
            </>
          )}

          {/* Integration info */}
          <div
            style={{
              marginTop: '20px',
              padding: '15px',
              backgroundColor: 'rgba(100, 100, 255, 0.1)',
              borderRadius: '6px',
              fontSize: '11px',
            }}
          >
            <h4 style={{ margin: '0 0 8px 0', fontSize: '12px', color: '#A8D8EA' }}>
              Integration Status
            </h4>
            <p style={{ margin: '3px 0' }}>
              📦 Logos System: <span style={{ color: '#FFD700' }}>Available</span>
            </p>
            <p style={{ margin: '3px 0' }}>
              🔧 AAL Compiler: <span style={{ color: '#FFD700' }}>Mock Mode</span>
            </p>
            <p style={{ margin: '3px 0' }}>
              ✓ Coq Verification: <span style={{ color: '#4ECDC4' }}>Ready</span>
            </p>
            <p style={{ margin: '3px 0' }}>
              🎯 Racket Backend: <span style={{ color: '#FFD700' }}>Available</span>
            </p>
          </div>
        </div>
      )}
    </>
  );
};

const OutputButton: React.FC<{
  label: string;
  selected: boolean;
  onClick: () => void;
}> = ({ label, selected, onClick }) => (
  <button
    onClick={onClick}
    style={{
      flex: 1,
      padding: '8px',
      backgroundColor: selected ? '#4ECDC4' : '#333',
      color: 'white',
      border: 'none',
      borderRadius: '4px',
      cursor: 'pointer',
      fontSize: '11px',
    }}
  >
    {label}
  </button>
);
