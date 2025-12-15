import { computeH1, canvasToSimplicialComplex, detectCycles, getConnectedComponents } from './compute-h1';

describe('Computational Scheme Theory', () => {
  test('should compute H¹ Betti number for simple tree', () => {
    const canvas = {
      nodes: [
        { id: 'A' },
        { id: 'B' },
        { id: 'C' }
      ],
      edges: [
        { from: 'A', to: 'B' },
        { from: 'B', to: 'C' }
      ]
    };
    
    const h1 = computeH1(canvas);
    expect(h1).toBe(0); // Tree has no cycles
  });
  
  test('should detect single cycle', () => {
    const canvas = {
      nodes: [
        { id: 'A' },
        { id: 'B' },
        { id: 'C' }
      ],
      edges: [
        { from: 'A', to: 'B' },
        { from: 'B', to: 'C' },
        { from: 'C', to: 'A' }
      ]
    };
    
    const h1 = computeH1(canvas);
    expect(h1).toBe(1); // One cycle
  });
  
  test('should detect multiple cycles', () => {
    const canvas = {
      nodes: [
        { id: 'A' },
        { id: 'B' },
        { id: 'C' },
        { id: 'D' }
      ],
      edges: [
        { from: 'A', to: 'B' },
        { from: 'B', to: 'C' },
        { from: 'C', to: 'A' }, // First cycle
        { from: 'B', to: 'D' },
        { from: 'D', to: 'A' }  // Second cycle
      ]
    };
    
    const h1 = computeH1(canvas);
    expect(h1).toBe(2); // Two independent cycles
  });
  
  test('should handle disconnected components', () => {
    const canvas = {
      nodes: [
        { id: 'A' },
        { id: 'B' },
        { id: 'C' },
        { id: 'D' },
        { id: 'E' }
      ],
      edges: [
        { from: 'A', to: 'B' },
        { from: 'B', to: 'C' },
        { from: 'C', to: 'A' }, // Cycle in component 1
        { from: 'D', to: 'E' }  // Tree in component 2
      ]
    };
    
    const h1 = computeH1(canvas);
    expect(h1).toBe(1); // One cycle total across both components
  });
  
  test('should handle empty canvas', () => {
    const canvas = { nodes: [], edges: [] };
    
    const h1 = computeH1(canvas);
    expect(h1).toBe(0);
  });
  
  test('should detect cycles correctly', () => {
    const cycleCanvas = {
      nodes: [
        { id: 'A' },
        { id: 'B' },
        { id: 'C' }
      ],
      edges: [
        { from: 'A', to: 'B' },
        { from: 'B', to: 'C' },
        { from: 'C', to: 'A' }
      ]
    };
    
    const treeCanvas = {
      nodes: [
        { id: 'A' },
        { id: 'B' },
        { id: 'C' }
      ],
      edges: [
        { from: 'A', to: 'B' },
        { from: 'B', to: 'C' }
      ]
    };
    
    expect(detectCycles(cycleCanvas)).toBe(true);
    expect(detectCycles(treeCanvas)).toBe(false);
  });
  
  test('should identify connected components', () => {
    const canvas = {
      nodes: [
        { id: 'A' },
        { id: 'B' },
        { id: 'C' },
        { id: 'D' },
        { id: 'E' }
      ],
      edges: [
        { from: 'A', to: 'B' },
        { from: 'B', to: 'C' },
        { from: 'D', to: 'E' }
      ]
    };
    
    const components = getConnectedComponents(canvas);
    expect(components).toHaveLength(2);
    
    // Check that components contain correct nodes
    const component1 = components.find(c => c.includes('A'));
    const component2 = components.find(c => c.includes('D'));
    
    expect(component1).toEqual(expect.arrayContaining(['A', 'B', 'C']));
    expect(component2).toEqual(expect.arrayContaining(['D', 'E']));
  });
  
  test('should handle invalid edges gracefully', () => {
    const canvas = {
      nodes: [
        { id: 'A' },
        { id: 'B' }
      ],
      edges: [
        { from: 'A', to: 'B' },
        { from: 'A', to: 'C' }, // Invalid edge - C doesn't exist
        { from: 'D', to: 'B' }  // Invalid edge - D doesn't exist
      ]
    };
    
    const h1 = computeH1(canvas);
    expect(h1).toBe(0); // Only valid edge A-B counts
  });
});