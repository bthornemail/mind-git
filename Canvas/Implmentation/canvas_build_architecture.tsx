import React, { useState } from 'react';
import { FileCode, GitBranch, Play, RefreshCw, Zap, Database, CheckCircle, AlertCircle } from 'lucide-react';

const CanvasBuildArchitecture = () => {
  const [activePhase, setActivePhase] = useState('design');
  
  const phases = [
    { id: 'design', name: 'Design', icon: FileCode, color: 'blue' },
    { id: 'generate', name: 'Generate', icon: GitBranch, color: 'green' },
    { id: 'compile', name: 'Compile', icon: Zap, color: 'yellow' },
    { id: 'execute', name: 'Execute', icon: Play, color: 'purple' },
    { id: 'feedback', name: 'Feedback', icon: RefreshCw, color: 'orange' }
  ];

  const layers = [
    {
      name: 'Visual Layer',
      component: 'Obsidian Canvas',
      description: 'Drag nodes, connect edges',
      output: 'canvas.json'
    },
    {
      name: 'AST Layer',
      component: 'canvas-state->logos-ast',
      description: 'Parse visual structure',
      output: 'Abstract Syntax Tree'
    },
    {
      name: 'AAL Layer',
      component: 'ast->aal-program',
      description: 'Compile to assembly-algebra',
      output: 'AAL Instructions'
    },
    {
      name: 'Execution Layer',
      component: '2AFA Engine',
      description: 'Run with δ transition',
      output: 'Results + Verification'
    },
    {
      name: 'Feedback Layer',
      component: 'results->canvas-update',
      description: 'Update visual state',
      output: 'Modified canvas.json'
    }
  ];

  const nodeTypes = [
    { type: '#Activate:', maps: 'JMP/CALL', dimension: '0D→1D', color: 'bg-blue-500' },
    { type: '#Integrate:', maps: 'ADD/SUB', dimension: '1D→2D', color: 'bg-green-500' },
    { type: '#Transform:', maps: 'MUL/DIV', dimension: '2D→3D', color: 'bg-yellow-500' },
    { type: '#Propagate:', maps: 'SHL/ROL', dimension: '3D→4D', color: 'bg-purple-500' },
    { type: '#Verify:', maps: 'CMP/TEST', dimension: '4D→5D', color: 'bg-pink-500' },
    { type: '#Store:', maps: 'MOV/ST', dimension: '5D→6D', color: 'bg-indigo-500' },
    { type: '#Observe:', maps: 'LD/GET', dimension: '6D→7D', color: 'bg-red-500' }
  ];

  return (
    <div className="w-full h-full bg-gradient-to-br from-slate-900 to-slate-800 text-white p-6 overflow-auto">
      {/* Header */}
      <div className="mb-8">
        <h1 className="text-3xl font-bold mb-2 bg-gradient-to-r from-blue-400 to-purple-400 bg-clip-text text-transparent">
          Canvas-Driven Development
        </h1>
        <p className="text-slate-400">
          Build the Logos system inside Obsidian Canvas
        </p>
      </div>

      {/* Build Pipeline */}
      <div className="mb-8 bg-slate-800/50 rounded-lg p-6">
        <h2 className="text-xl font-semibold mb-4 flex items-center gap-2">
          <Database className="w-5 h-5" />
          Build Pipeline
        </h2>
        
        <div className="flex items-center gap-4 mb-6 overflow-x-auto pb-2">
          {phases.map((phase, idx) => (
            <React.Fragment key={phase.id}>
              <button
                onClick={() => setActivePhase(phase.id)}
                className={`flex flex-col items-center gap-2 p-4 rounded-lg transition-all ${
                  activePhase === phase.id
                    ? 'bg-blue-600 scale-105'
                    : 'bg-slate-700 hover:bg-slate-600'
                }`}
              >
                <phase.icon className="w-6 h-6" />
                <span className="text-sm whitespace-nowrap">{phase.name}</span>
              </button>
              {idx < phases.length - 1 && (
                <div className="flex-shrink-0 w-8 h-0.5 bg-slate-600" />
              )}
            </React.Fragment>
          ))}
        </div>

        {/* Layer Details */}
        <div className="space-y-3">
          {layers.map((layer, idx) => (
            <div
              key={idx}
              className="bg-slate-700/50 rounded p-4 hover:bg-slate-700 transition-colors"
            >
              <div className="flex items-start justify-between mb-2">
                <div>
                  <h3 className="font-semibold text-blue-400">{layer.name}</h3>
                  <p className="text-sm text-slate-400">{layer.component}</p>
                </div>
                <CheckCircle className="w-5 h-5 text-green-400" />
              </div>
              <p className="text-sm text-slate-300 mb-2">{layer.description}</p>
              <div className="text-xs text-slate-500 font-mono">→ {layer.output}</div>
            </div>
          ))}
        </div>
      </div>

      {/* Node Type Mappings */}
      <div className="mb-8 bg-slate-800/50 rounded-lg p-6">
        <h2 className="text-xl font-semibold mb-4 flex items-center gap-2">
          <Zap className="w-5 h-5" />
          Canvas Node → Assembly Mappings
        </h2>
        
        <div className="grid grid-cols-1 md:grid-cols-2 gap-4">
          {nodeTypes.map((node, idx) => (
            <div
              key={idx}
              className="bg-slate-700/50 rounded-lg p-4 hover:scale-102 transition-transform"
            >
              <div className="flex items-center gap-3 mb-3">
                <div className={`w-3 h-3 rounded-full ${node.color}`} />
                <span className="font-mono text-sm font-semibold">{node.type}</span>
              </div>
              <div className="pl-6 space-y-1">
                <div className="text-sm">
                  <span className="text-slate-400">Assembly:</span>
                  <span className="ml-2 font-mono text-green-400">{node.maps}</span>
                </div>
                <div className="text-sm">
                  <span className="text-slate-400">Dimension:</span>
                  <span className="ml-2 font-mono text-purple-400">{node.dimension}</span>
                </div>
              </div>
            </div>
          ))}
        </div>
      </div>

      {/* Live Example */}
      <div className="bg-slate-800/50 rounded-lg p-6">
        <h2 className="text-xl font-semibold mb-4 flex items-center gap-2">
          <Play className="w-5 h-5" />
          Example: Building a Function
        </h2>
        
        <div className="space-y-4">
          <div className="bg-slate-900/50 rounded p-4 border border-slate-700">
            <div className="text-sm text-slate-400 mb-2">1. Canvas Design:</div>
            <div className="font-mono text-xs text-green-400 whitespace-pre">
{`Node 1: #Activate: main
Node 2: #Integrate: x y
Node 3: #Store: result
Edge: Node 1 → Node 2 → Node 3`}
            </div>
          </div>

          <div className="bg-slate-900/50 rounded p-4 border border-slate-700">
            <div className="text-sm text-slate-400 mb-2">2. Generated AST:</div>
            <div className="font-mono text-xs text-blue-400 whitespace-pre">
{`(ast-node 'activate ["main"] "node1")
(ast-node 'integrate ["x" "y"] "node2")
(ast-node 'store ["result"] "node3")`}
            </div>
          </div>

          <div className="bg-slate-900/50 rounded p-4 border border-slate-700">
            <div className="text-sm text-slate-400 mb-2">3. Compiled AAL:</div>
            <div className="font-mono text-xs text-yellow-400 whitespace-pre">
{`JMP main
ADD R1, x, y
ST [result], R1`}
            </div>
          </div>

          <div className="bg-slate-900/50 rounded p-4 border border-green-900">
            <div className="text-sm text-green-400 mb-2 flex items-center gap-2">
              <CheckCircle className="w-4 h-4" />
              4. Execution Result:
            </div>
            <div className="font-mono text-xs text-slate-300">
              result = x + y ✓ Verified via Hadamard-Pfister
            </div>
          </div>
        </div>
      </div>

      {/* Action Buttons */}
      <div className="mt-8 flex gap-4">
        <button className="flex-1 bg-blue-600 hover:bg-blue-700 py-3 px-6 rounded-lg font-semibold transition-colors flex items-center justify-center gap-2">
          <FileCode className="w-5 h-5" />
          Generate Template Canvas
        </button>
        <button className="flex-1 bg-green-600 hover:bg-green-700 py-3 px-6 rounded-lg font-semibold transition-colors flex items-center justify-center gap-2">
          <Play className="w-5 h-5" />
          Start Live Build
        </button>
      </div>
    </div>
  );
};

export default CanvasBuildArchitecture;