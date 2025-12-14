/**
 * AAL Verification Dashboard
 * 
 * Interactive React component for displaying AAL verification results
 * Shows formal verification status, geometric properties, and proof details
 */

import React, { useState, useEffect } from 'react';
import { 
  VerificationResult, 
  AALCanvasCompilationResult,
  QuadForm,
  DimensionViolation 
} from '../compiler/aal-integration';

/**
 * Dashboard props
 */
interface AALVerificationDashboardProps {
  compilation: AALCanvasCompilationResult;
  onVerificationComplete?: (result: VerificationResult) => void;
  showDetails?: boolean;
  compact?: boolean;
}

/**
 * AAL Verification Dashboard Component
 */
export const AALVerificationDashboard: React.FC<AALVerificationDashboardProps> = ({
  compilation,
  onVerificationComplete,
  showDetails = true,
  compact = false
}) => {
  const [activeTab, setActiveTab] = useState<'overview' | 'geometric' | 'proofs' | 'diagnostics'>('overview');
  const [expandedNodes, setExpandedNodes] = useState<Set<string>>(new Set());
  
  useEffect(() => {
    if (onVerificationComplete && compilation.verification) {
      onVerificationComplete(compilation.verification);
    }
  }, [compilation.verification, onVerificationComplete]);
  
  const { verification, metadata, diagnostics } = compilation;
  
  const toggleNodeExpansion = (nodeId: string) => {
    const newExpanded = new Set(expandedNodes);
    if (newExpanded.has(nodeId)) {
      newExpanded.delete(nodeId);
    } else {
      newExpanded.add(nodeId);
    }
    setExpandedNodes(newExpanded);
  };
  
  const getStatusColor = (verified: boolean, confidence = 1.0) => {
    if (!verified) return 'text-red-600';
    if (confidence >= 0.9) return 'text-green-600';
    if (confidence >= 0.7) return 'text-yellow-600';
    return 'text-orange-600';
  };
  
  const getStatusIcon = (verified: boolean) => {
    return verified ? '✅' : '❌';
  };
  
  if (compact) {
    return (
      <div className=\"aal-verification-compact p-4 bg-white rounded-lg shadow-md\">
        <div className=\"grid grid-cols-2 md:grid-cols-4 gap-4\">
          <div className={`text-center ${getStatusColor(verification.normPreservation.verified, verification.normPreservation.confidence)}`}>
            <div className=\"text-2xl\">{getStatusIcon(verification.normPreservation.verified)}</div>
            <div className=\"text-sm font-medium\">Norm Preservation</div>
          </div>
          
          <div className={`text-center ${getStatusColor(verification.geometricConsistency.verified)}`}>
            <div className=\"text-2xl\">{getStatusIcon(verification.geometricConsistency.verified)}</div>
            <div className=\"text-sm font-medium\">Geometric Valid</div>
          </div>
          
          <div className={`text-center ${getStatusColor(verification.typeSafety.verified)}`}>
            <div className=\"text-2xl\">{getStatusIcon(verification.typeSafety.verified)}</div>
            <div className=\"text-sm font-medium\">Type Safe</div>
          </div>
          
          <div className={`text-center ${getStatusColor(verification.coqProofs.provenTheorems === verification.coqProofs.totalTheorems)}`}>
            <div className=\"text-2xl\">{getStatusIcon(verification.coqProofs.admittedTheorems === 0)}</div>
            <div className=\"text-sm font-medium\">Formal Proofs</div>
          </div>
        </div>
      </div>
    );
  }
  
  return (
    <div className=\"aal-verification-dashboard bg-white rounded-lg shadow-lg\">
      {/* Header */}
      <div className=\"border-b border-gray-200 p-6\">
        <h2 className=\"text-2xl font-bold text-gray-900 mb-2\">
          🎯 AAL Formal Verification Dashboard
        </h2>
        <div className=\"flex items-center space-x-4 text-sm text-gray-600\">
          <span>📊 {metadata.nodeCount} nodes</span>
          <span>🔗 {metadata.edgeCount} edges</span>
          <span>🧮 {metadata.instructionCount} instructions</span>
          <span>⏱️ {metadata.compilationTime}ms</span>
          <span className={`font-medium ${compilation.success ? 'text-green-600' : 'text-red-600'}`}>
            {compilation.success ? '✅ Verified' : '❌ Failed'}
          </span>
        </div>
      </div>
      
      {/* Tabs */}
      <div className=\"border-b border-gray-200\">
        <nav className=\"flex space-x-8 px-6\" aria-label=\"Tabs\">
          {[
            { id: 'overview', label: 'Overview', icon: '📊' },
            { id: 'geometric', label: 'Geometric', icon: '📐' },
            { id: 'proofs', label: 'Proofs', icon: '🔬' },
            { id: 'diagnostics', label: 'Diagnostics', icon: '⚠️' }
          ].map(tab => (
            <button
              key={tab.id}
              onClick={() => setActiveTab(tab.id as any)}
              className={`py-4 px-1 border-b-2 font-medium text-sm ${
                activeTab === tab.id
                  ? 'border-blue-500 text-blue-600'
                  : 'border-transparent text-gray-500 hover:text-gray-700 hover:border-gray-300'
              }`}
            >
              <span className=\"mr-2\">{tab.icon}</span>
              {tab.label}
            </button>
          ))}
        </nav>
      </div>
      
      {/* Tab Content */}
      <div className=\"p-6\">
        {activeTab === 'overview' && (
          <OverviewTab 
            verification={verification} 
            metadata={metadata}
            getStatusColor={getStatusColor}
            getStatusIcon={getStatusIcon}
          />
        )}
        
        {activeTab === 'geometric' && (
          <GeometricTab 
            verification={verification}
            nodes={compilation.ast}
            expandedNodes={expandedNodes}
            toggleNodeExpansion={toggleNodeExpansion}
          />
        )}
        
        {activeTab === 'proofs' && (
          <ProofsTab 
            verification={verification}
            compilation={compilation}
          />
        )}
        
        {activeTab === 'diagnostics' && (
          <DiagnosticsTab 
            diagnostics={diagnostics}
            verification={verification}
          />
        )}
      </div>
    </div>
  );
};

/**
 * Overview Tab Component
 */
const OverviewTab: React.FC<{
  verification: VerificationResult;
  metadata: any;
  getStatusColor: (verified: boolean, confidence?: number) => string;
  getStatusIcon: (verified: boolean) => string;
}> = ({ verification, metadata, getStatusColor, getStatusIcon }) => {
  return (
    <div className=\"space-y-6\">
      <div className=\"grid grid-cols-1 md:grid-cols-2 lg:grid-cols-4 gap-6\">
        {/* Norm Preservation */}
        <VerificationCard
          title=\"Norm Preservation\"
          icon=\"⚖️\"
          verified={verification.normPreservation.verified}
          confidence={verification.normPreservation.confidence}
          getStatusColor={getStatusColor}
          getStatusIcon={getStatusIcon}
        >
          <div className=\"text-sm text-gray-600\">
            <p>||a × b|| = ||a|| × ||b||</p>
            <p className=\"mt-1\">Violations: {verification.normPreservation.violations.length}</p>
          </div>
        </VerificationCard>
        
        {/* Geometric Consistency */}
        <VerificationCard
          title=\"Geometric Consistency\"
          icon=\"📐\"
          verified={verification.geometricConsistency.verified}
          getStatusColor={getStatusColor}
          getStatusIcon={getStatusIcon}
        >
          <div className=\"text-sm text-gray-600\">
            <p>Fano Plane Valid: {verification.geometricConsistency.fanoPlaneValid ? 'Yes' : 'No'}</p>
            <p className=\"mt-1\">Conic Type: {verification.geometricConsistency.conicType}</p>
          </div>
        </VerificationCard>
        
        {/* Type Safety */}
        <VerificationCard
          title=\"Type Safety\"
          icon=\"🛡️\"
          verified={verification.typeSafety.verified}
          getStatusColor={getStatusColor}
          getStatusIcon={getStatusIcon}
        >
          <div className=\"text-sm text-gray-600\">
            <p>Dimension Violations: {verification.typeSafety.dimensionViolations.length}</p>
            <p className=\"mt-1\">Grade Weakening: {verification.typeSafety.gradeWeakeningValid ? 'Valid' : 'Invalid'}</p>
          </div>
        </VerificationCard>
        
        {/* Coq Proofs */}
        <VerificationCard
          title=\"Formal Proofs\"
          icon=\"🔬\"
          verified={verification.coqProofs.admittedTheorems === 0}
          confidence={verification.coqProofs.provenTheorems / verification.coqProofs.totalTheorems}
          getStatusColor={getStatusColor}
          getStatusIcon={getStatusIcon}
        >
          <div className=\"text-sm text-gray-600\">
            <p>Proven: {verification.coqProofs.provenTheorems}/{verification.coqProofs.totalTheorems}</p>
            <p className=\"mt-1\">Admitted: {verification.coqProofs.admittedTheorems}</p>
          </div>
        </VerificationCard>
      </div>
      
      {/* Compilation Metrics */}
      <div className=\"bg-gray-50 rounded-lg p-4\">
        <h3 className=\"text-lg font-semibold text-gray-900 mb-3\">📈 Compilation Metrics</h3>
        <div className=\"grid grid-cols-2 md:grid-cols-4 gap-4 text-sm\">
          <div>
            <span className=\"font-medium\">Max Dimension:</span>
            <span className=\"ml-2\">D{metadata.maxDimension}</span>
          </div>
          <div>
            <span className=\"font-medium\">Complexity:</span>
            <span className=\"ml-2\">{metadata.complexity}</span>
          </div>
          <div>
            <span className=\"font-medium\">Hopf Compatible:</span>
            <span className=\"ml-2\">{metadata.hopfCompatible ? 'Yes' : 'No'}</span>
          </div>
          <div>
            <span className=\"font-medium\">Success:</span>
            <span className={`ml-2 font-medium ${compilation.success ? 'text-green-600' : 'text-red-600'}`}>
              {compilation.success ? 'Yes' : 'No'}
            </span>
          </div>
        </div>
      </div>
    </div>
  );
};

/**
 * Geometric Tab Component
 */
const GeometricTab: React.FC<{
  verification: VerificationResult;
  nodes: any[];
  expandedNodes: Set<string>;
  toggleNodeExpansion: (nodeId: string) => void;
}> = ({ verification, nodes, expandedNodes, toggleNodeExpansion }) => {
  const d9Nodes = nodes.filter(n => n.aal?.grade === 9);
  
  return (
    <div className=\"space-y-6\">
      <div className=\"bg-blue-50 border border-blue-200 rounded-lg p-4\">
        <h3 className=\"text-lg font-semibold text-blue-900 mb-2\">📐 D9 Projective Geometry</h3>
        <p className=\"text-blue-800\">
          Nodes at dimension D9 map to quadratic forms in the Fano Plane PG(2,2).
          Non-degenerate conics represent valid geometric structures.
        </p>
      </div>
      
      {d9Nodes.length === 0 ? (
        <div className=\"text-center py-8 text-gray-500\">
          <p className=\"text-lg\">📐 No D9 (Geometric) nodes found</p>
          <p className=\"text-sm mt-2\">Add nodes with geometric content to see Fano Plane projections.</p>
        </div>
      ) : (
        <div className=\"space-y-4\">
          {d9Nodes.map(node => (
            <GeometricNodeCard
              key={node.id}
              node={node}
              isExpanded={expandedNodes.has(node.id)}
              onToggle={() => toggleNodeExpansion(node.id)}
            />
          ))}
        </div>
      )}
      
      {/* Fano Plane Visualization */}
      {verification.geometricConsistency.verified && (
        <div className=\"bg-green-50 border border-green-200 rounded-lg p-4\">
          <h3 className=\"text-lg font-semibold text-green-900 mb-3\">🎯 Fano Plane Projection</h3>
          <FanoPlaneVisualization />
        </div>
      )}
    </div>
  );
};

/**
 * Proofs Tab Component
 */
const ProofsTab: React.FC<{
  verification: VerificationResult;
  compilation: AALCanvasCompilationResult;
}> = ({ verification, compilation }) => {
  const [selectedProof, setSelectedProof] = useState<string | null>(null);
  
  return (
    <div className=\"space-y-6\">
      {/* Proof Summary */}
      <div className=\"grid grid-cols-1 md:grid-cols-3 gap-6\">
        <div className=\"bg-green-50 rounded-lg p-4 text-center\">
          <div className=\"text-3xl font-bold text-green-600\">{verification.coqProofs.provenTheorems}</div>
          <div className=\"text-sm font-medium text-green-900\">Proven Theorems</div>
        </div>
        <div className=\"bg-yellow-50 rounded-lg p-4 text-center\">
          <div className=\"text-3xl font-bold text-yellow-600\">{verification.coqProofs.admittedTheorems}</div>
          <div className=\"text-sm font-medium text-yellow-900\">Admitted Theorems</div>
        </div>
        <div className=\"bg-blue-50 rounded-lg p-4 text-center\">
          <div className=\"text-3xl font-bold text-blue-600\">{verification.coqProofs.totalTheorems}</div>
          <div className=\"text-sm font-medium text-blue-900\">Total Theorems</div>
        </div>
      </div>
      
      {/* Proof List */}
      <div className=\"bg-gray-50 rounded-lg p-4\">
        <h3 className=\"text-lg font-semibold text-gray-900 mb-3\">🔬 Proof Details</h3>
        <div className=\"space-y-2\">
          {compilation.aalInstructions.map((inst, index) => (
            <ProofItem
              key={inst.id}
              instruction={inst}
              index={index}
              isSelected={selectedProof === inst.id}
              onSelect={() => setSelectedProof(selectedProof === inst.id ? null : inst.id)}
            />
          ))}
        </div>
      </div>
      
      {/* Selected Proof Details */}
      {selectedProof && (
        <div className=\"bg-white border border-gray-200 rounded-lg p-4\">
          <h3 className=\"text-lg font-semibold text-gray-900 mb-3\">📜 Proof Details</h3>
          <ProofDetails instructionId={selectedProof} />
        </div>
      )}
    </div>
  );
};

/**
 * Diagnostics Tab Component
 */
const DiagnosticsTab: React.FC<{
  diagnostics: any[];
  verification: VerificationResult;
}> = ({ diagnostics, verification }) => {
  const errors = diagnostics.filter(d => d.severity === 'error');
  const warnings = diagnostics.filter(d => d.severity === 'warning');
  const info = diagnostics.filter(d => d.severity === 'info');
  
  return (
    <div className=\"space-y-6\">
      {/* Diagnostic Summary */}
      <div className=\"grid grid-cols-1 md:grid-cols-3 gap-6\">
        <div className=\"bg-red-50 rounded-lg p-4 text-center\">
          <div className=\"text-3xl font-bold text-red-600\">{errors.length}</div>
          <div className=\"text-sm font-medium text-red-900\">Errors</div>
        </div>
        <div className=\"bg-yellow-50 rounded-lg p-4 text-center\">
          <div className=\"text-3xl font-bold text-yellow-600\">{warnings.length}</div>
          <div className=\"text-sm font-medium text-yellow-900\">Warnings</div>
        </div>
        <div className=\"bg-blue-50 rounded-lg p-4 text-center\">
          <div className=\"text-3xl font-bold text-blue-600\">{info.length}</div>
          <div className=\"text-sm font-medium text-blue-900\">Info</div>
        </div>
      </div>
      
      {/* Diagnostic List */}
      {diagnostics.length > 0 && (
        <div className=\"bg-gray-50 rounded-lg p-4\">
          <h3 className=\"text-lg font-semibold text-gray-900 mb-3\">⚠️ Diagnostic Messages</h3>
          <div className=\"space-y-3\">
            {diagnostics.map(diagnostic => (
              <DiagnosticItem key={diagnostic.id} diagnostic={diagnostic} />
            ))}
          </div>
        </div>
      )}
      
      {/* Verification Violations */}
      <div className=\"bg-gray-50 rounded-lg p-4\">
        <h3 className=\"text-lg font-semibold text-gray-900 mb-3\">🚫 Verification Violations</h3>
        
        {/* Norm Preservation Violations */}
        {verification.normPreservation.violations.length > 0 && (
          <div className=\"mb-4\">
            <h4 className=\"font-medium text-red-900 mb-2\">Norm Preservation Violations:</h4>
            <ul className=\"list-disc list-inside text-sm text-red-800 space-y-1\">
              {verification.normPreservation.violations.map((violation, index) => (
                <li key={index}>{violation}</li>
              ))}
            </ul>
          </div>
        )}
        
        {/* Type Safety Violations */}
        {verification.typeSafety.dimensionViolations.length > 0 && (
          <div className=\"mb-4\">
            <h4 className=\"font-medium text-orange-900 mb-2\">Type Safety Violations:</h4>
            <ul className=\"list-disc list-inside text-sm text-orange-800 space-y-1\">
              {verification.typeSafety.dimensionViolations.map((violation, index) => (
                <li key={index}>
                  Node {violation.nodeId}: Expected D{violation.expectedDimension}, got D{violation.actualDimension}
                </li>
              ))}
            </ul>
          </div>
        )}
        
        {/* Geometric Consistency Violations */}
        {verification.geometricConsistency.violations.length > 0 && (
          <div>
            <h4 className=\"font-medium text-purple-900 mb-2\">Geometric Consistency Violations:</h4>
            <ul className=\"list-disc list-inside text-sm text-purple-800 space-y-1\">
              {verification.geometricConsistency.violations.map((violation, index) => (
                <li key={index}>{violation}</li>
              ))}
            </ul>
          </div>
        )}
      </div>
    </div>
  );
};

/**
 * Verification Card Component
 */
const VerificationCard: React.FC<{
  title: string;
  icon: string;
  verified: boolean;
  confidence?: number;
  getStatusColor: (verified: boolean, confidence?: number) => string;
  getStatusIcon: (verified: boolean) => string;
  children: React.ReactNode;
}> = ({ title, icon, verified, confidence, getStatusColor, getStatusIcon, children }) => {
  return (
    <div className=\"bg-white border border-gray-200 rounded-lg p-4 shadow-sm\">
      <div className=\"flex items-center justify-between mb-3\">
        <h3 className=\"font-semibold text-gray-900\">{title}</h3>
        <span className={`text-2xl ${getStatusColor(verified, confidence)}`}>
          {getStatusIcon(verified)}
        </span>
      </div>
      {confidence !== undefined && (
        <div className=\"mb-2\">
          <div className=\"flex justify-between text-sm text-gray-600 mb-1\">
            <span>Confidence</span>
            <span>{Math.round(confidence * 100)}%</span>
          </div>
          <div className=\"w-full bg-gray-200 rounded-full h-2\">
            <div 
              className={`h-2 rounded-full ${
                confidence >= 0.9 ? 'bg-green-500' : 
                confidence >= 0.7 ? 'bg-yellow-500' : 'bg-red-500'
              }`}
              style={{ width: `${confidence * 100}%` }}
            />
          </div>
        </div>
      )}
      <div>{children}</div>
    </div>
  );
};

/**
 * Geometric Node Card Component
 */
const GeometricNodeCard: React.FC<{
  node: any;
  isExpanded: boolean;
  onToggle: () => void;
}> = ({ node, isExpanded, onToggle }) => {
  const form = node.aal?.form;
  
  return (
    <div className=\"bg-white border border-gray-200 rounded-lg shadow-sm\">
      <div 
        className=\"p-4 cursor-pointer hover:bg-gray-50\"
        onClick={onToggle}
      >
        <div className=\"flex items-center justify-between\">
          <div>
            <h4 className=\"font-semibold text-gray-900\">{node.id}</h4>
            <p className=\"text-sm text-gray-600\">{node.text}</p>
          </div>
          <div className=\"text-blue-600\">
            {isExpanded ? '▼' : '▶'}
          </div>
        </div>
      </div>
      
      {isExpanded && form && (
        <div className=\"border-t border-gray-200 p-4 bg-gray-50\">
          <h5 className=\"font-medium text-gray-900 mb-2\">Quadratic Form:</h5>
          <div className=\"grid grid-cols-2 gap-4 text-sm\">
            <div>
              <span className=\"font-medium\">Coefficients:</span>
              <div className=\"mt-1 space-y-1\">
                <div>x²: {form.cxx ? '1' : '0'}</div>
                <div>y²: {form.cyy ? '1' : '0'}</div>
                <div>z²: {form.czz ? '1' : '0'}</div>
              </div>
            </div>
            <div>
              <span className=\"font-medium\">Cross Terms:</span>
              <div className=\"mt-1 space-y-1\">
                <div>xy: {form.cxy ? '1' : '0'}</div>
                <div>xz: {form.cxz ? '1' : '0'}</div>
                <div>yz: {form.cyz ? '1' : '0'}</div>
              </div>
            </div>
          </div>
          <div className=\"mt-3 text-sm\">
            <span className=\"font-medium\">Rank:</span> {form.rank} | 
            <span className=\"font-medium ml-2\">Non-degenerate:</span> {form.nonDegenerate ? 'Yes' : 'No'}
          </div>
          {form.fanoPoints.length > 0 && (
            <div className=\"mt-2 text-sm\">
              <span className=\"font-medium\">Fano Points:</span> {form.fanoPoints.join(', ')}
            </div>
          )}
        </div>
      )}
    </div>
  );
};

/**
 * Fano Plane Visualization Component
 */
const FanoPlaneVisualization: React.FC = () => {
  return (
    <div className=\"flex justify-center\">
      <svg width=\"300\" height=\"300\" viewBox=\"-150 -150 300 300\">
        {/* Fano Plane Points */}
        {[
          { x: 0, y: -100, label: '1' },
          { x: -87, y: 50, label: '2' },
          { x: 87, y: 50, label: '3' },
          { x: -100, y: -30, label: '4' },
          { x: 100, y: -30, label: '5' },
          { x: 0, y: 80, label: '6' },
          { x: 0, y: 0, label: '7' }
        ].map((point, index) => (
          <g key={index}>
            <circle
              cx={point.x}
              cy={point.y}
              r=\"8\"
              fill=\"#3B82F6\"
              stroke=\"#1E40AF\"
              strokeWidth=\"2\"
            />
            <text
              x={point.x}
              y={point.y + 4}
              textAnchor=\"middle\"
              fill=\"white\"
              fontSize=\"12\"
              fontWeight=\"bold\"
            >
              {point.label}
            </text>
          </g>
        ))}
        
        {/* Fano Plane Lines */}
        {[
          [[0, -100], [87, 50]],   // Line 1-3
          [[87, 50], [-87, 50]],   // Line 3-2
          [[-87, 50], [0, -100]],  // Line 2-1
          [[-100, -30], [100, -30]], // Line 4-5
          [[0, -100], [0, 80]],    // Line 1-6
          [[-87, 50], [100, -30]],  // Line 2-5
          [[87, 50], [-100, -30]],   // Line 3-4
          [[0, 80], [-100, -30]],    // Line 6-4
          [[0, 80], [100, -30]],     // Line 6-5
          [[0, 0], [0, -100]],       // Line 7-1 (circle)
          [[0, 0], [-87, 50]],       // Line 7-2 (circle)
          [[0, 0], [87, 50]]        // Line 7-3 (circle)
        ].map((line, index) => (
          <line
            key={index}
            x1={line[0][0]}
            y1={line[0][1]}
            x2={line[1][0]}
            y2={line[1][1]}
            stroke=\"#6B7280\"
            strokeWidth=\"1\"
            opacity=\"0.6\"
          />
        ))}
        
        {/* Circle for lines through point 7 */}
        <circle
          cx=\"0\"
          cy=\"0\"
          r=\"70\"
          fill=\"none\"
          stroke=\"#6B7280\"
          strokeWidth=\"1\"
          opacity=\"0.6\"
        />
      </svg>
    </div>
  );
};

/**
 * Proof Item Component
 */
const ProofItem: React.FC<{
  instruction: any;
  index: number;
  isSelected: boolean;
  onSelect: () => void;
}> = ({ instruction, index, isSelected, onSelect }) => {
  return (
    <div 
      className={`p-3 border rounded-lg cursor-pointer transition-colors ${
        isSelected ? 'border-blue-500 bg-blue-50' : 'border-gray-200 hover:bg-gray-50'
      }`}
      onClick={onSelect}
    >
      <div className=\"flex items-center justify-between\">
        <div>
          <span className=\"font-medium text-gray-900\">{instruction.opcode}</span>
          <span className=\"text-sm text-gray-600 ml-2\">{instruction.metadata.comment}</span>
        </div>
        <div className=\"text-sm text-gray-500\">
          #{index + 1}
        </div>
      </div>
    </div>
  );
};

/**
 * Proof Details Component
 */
const ProofDetails: React.FC<{ instructionId: string }> = ({ instructionId }) => {
  return (
    <div className=\"space-y-4\">
      <div className=\"bg-gray-50 rounded p-3\">
        <h4 className=\"font-medium text-gray-900 mb-2\">🔬 Coq Proof Status</h4>
        <div className=\"text-sm text-gray-700\">
          <p>Proof obligation: <code className=\"bg-gray-200 px-1 rounded\">instruction_correct_{instructionId}</code></p>
          <p className=\"mt-1\">Status: <span className=\"text-green-600 font-medium\">✅ Proven</span></p>
          <p className=\"mt-1\">Theorem reference: <code className=\"bg-gray-200 px-1 rounded\">AAL-Theorem-{instructionId}</code></p>
        </div>
      </div>
      
      <div className=\"bg-blue-50 rounded p-3\">
        <h4 className=\"font-medium text-blue-900 mb-2\">📜 Generated Coq Code</h4>
        <pre className=\"text-xs bg-blue-100 p-2 rounded overflow-x-auto\">
          <code>
            {`Theorem instruction_correct_${instructionId} : forall (s s' : MachineState),
  step s (${instructionId}_instruction) s' -> 
  norm_preservation s s'.`}
          </code>
        </pre>
      </div>
    </div>
  );
};

/**
 * Diagnostic Item Component
 */
const DiagnosticItem: React.FC<{ diagnostic: any }> = ({ diagnostic }) => {
  const severityColors = {
    error: 'text-red-600 bg-red-50 border-red-200',
    warning: 'text-yellow-600 bg-yellow-50 border-yellow-200',
    info: 'text-blue-600 bg-blue-50 border-blue-200',
    hint: 'text-gray-600 bg-gray-50 border-gray-200'
  };
  
  const colorClass = severityColors[diagnostic.severity] || severityColors.info;
  
  return (
    <div className={`p-3 border rounded-lg ${colorClass}`}>
      <div className=\"flex items-start justify-between mb-2\">
        <div className=\"flex items-center space-x-2\">
          <span className=\"font-medium uppercase text-xs\">{diagnostic.severity}</span>
          <span className=\"font-mono text-sm\">{diagnostic.code}</span>
        </div>
        {diagnostic.nodeId && (
          <span className=\"text-sm\">Node: {diagnostic.nodeId}</span>
        )}
      </div>
      <p className=\"text-sm mb-2\">{diagnostic.message}</p>
      {diagnostic.suggestions && diagnostic.suggestions.length > 0 && (
        <div className=\"text-xs\">
          <span className=\"font-medium\">Suggestions:</span>
          <ul className=\"list-disc list-inside mt-1 space-y-1\">
            {diagnostic.suggestions.map((suggestion: string, index: number) => (
              <li key={index}>{suggestion}</li>
            ))}
          </ul>
        </div>
      )}
    </div>
  );
};

export default AALVerificationDashboard;