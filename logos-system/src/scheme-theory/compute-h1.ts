// Computational Scheme Theory - H¹ Betti Numbers
// First critical component for formal verification

export interface SimplicialComplex {
  vertices: Array<{id: string, index: number, data: any}>;
  edges: Array<{vertices: number[], data: any}>;
}

export interface Canvas {
  nodes?: Array<{id: string, [key: string]: any}>;
  edges?: Array<{from: string, to: string, [key: string]: any}>;
}

export function computeH1(canvas: Canvas): number {
  // Convert canvas to simplicial complex
  const complex = canvasToSimplicialComplex(canvas);
  
  // Compute connected components (β₀)
  const components = countConnectedComponents(complex);
  
  // Compute edges, vertices
  const edges = complex.edges.length;
  const vertices = complex.vertices.length;
  
  // For connected graph: β₁ = E - V + 1
  // For general case: β₁ = E - V + C (where C = components)
  return edges - vertices + components;
}

export function canvasToSimplicialComplex(canvas: Canvas): SimplicialComplex {
  // Convert canvas nodes/edges to mathematical structure
  const vertices = (canvas.nodes || []).map((node, i) => ({
    id: node.id,
    index: i,
    data: node
  }));
  
  const edges = (canvas.edges || []).map(edge => {
    const fromIndex = vertices.findIndex(v => v.id === edge.from);
    const toIndex = vertices.findIndex(v => v.id === edge.to);
    
    return {
      vertices: [fromIndex, toIndex].filter(i => i !== -1),
      data: edge
    };
  }).filter(edge => edge.vertices.length === 2);
  
  return { vertices, edges };
}

function countConnectedComponents(complex: SimplicialComplex): number {
  if (complex.vertices.length === 0) return 0;
  
  // Union-Find algorithm for connected components
  const parent = new Array(complex.vertices.length).fill(0).map((_, i) => i);
  
  function find(i: number): number {
    if (parent[i] !== i) parent[i] = find(parent[i]);
    return parent[i];
  }
  
  function union(i: number, j: number) {
    const rootI = find(i);
    const rootJ = find(j);
    if (rootI !== rootJ) parent[rootI] = rootJ;
  }
  
  // Union all connected vertices
  complex.edges.forEach(edge => {
    if (edge.vertices.length === 2) {
      union(edge.vertices[0], edge.vertices[1]);
    }
  });
  
  // Count unique roots
  const roots = new Set(parent.map(find));
  return roots.size;
}

// Additional topological invariants
export function computeEulerCharacteristic(canvas: Canvas): number {
  const complex = canvasToSimplicialComplex(canvas);
  const vertices = complex.vertices.length;
  const edges = complex.edges.length;
  
  // For 1D complex: χ = V - E
  return vertices - edges;
}

export function computeCyclomaticNumber(canvas: Canvas): number {
  // Same as H¹ for connected graphs
  return computeH1(canvas);
}

export function detectCycles(canvas: Canvas): boolean {
  return computeH1(canvas) > 0;
}

export function getConnectedComponents(canvas: Canvas): Array<Array<string>> {
  const complex = canvasToSimplicialComplex(canvas);
  const components = countConnectedComponents(complex);
  
  if (components === 0) return [];
  if (components === 1) return [complex.vertices.map(v => v.id)];
  
  // Build adjacency list
  const adjacency = new Map<number, Set<number>>();
  complex.vertices.forEach(v => adjacency.set(v.index, new Set()));
  
  complex.edges.forEach(edge => {
    if (edge.vertices.length === 2) {
      adjacency.get(edge.vertices[0])?.add(edge.vertices[1]);
      adjacency.get(edge.vertices[1])?.add(edge.vertices[0]);
    }
  });
  
  // Find components using DFS
  const visited = new Set<number>();
  const result: Array<Array<string>> = [];
  
  function dfs(node: number, component: Array<string>) {
    visited.add(node);
    component.push(complex.vertices[node].id);
    
    for (const neighbor of adjacency.get(node) || []) {
      if (!visited.has(neighbor)) {
        dfs(neighbor, component);
      }
    }
  }
  
  for (let i = 0; i < complex.vertices.length; i++) {
    if (!visited.has(i)) {
      const component: Array<string> = [];
      dfs(i, component);
      result.push(component);
    }
  }
  
  return result;
}