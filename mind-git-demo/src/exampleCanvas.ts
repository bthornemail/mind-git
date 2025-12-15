import { Canvas } from './types';

/**
 * Example canvas demonstrating mind-git spatial programming
 * Implements a simple mathematical computation flow:
 * Observer (0,0) → Activate → Integrate → Transform → Verify
 *
 * This showcases the identity chain and polynomial algebra concepts
 */
export const exampleCanvas: Canvas = {
  nodes: [
    {
      id: 'observer',
      type: 'text',
      x: 0,
      y: 0,
      width: 200,
      height: 80,
      text: '#Observe: Identity Element\nP₀ = 1 (Observer at origin)',
      color: '#A8D8EA',
    },
    {
      id: 'activate-main',
      type: 'text',
      x: 300,
      y: -100,
      width: 220,
      height: 80,
      text: '#Activate: main\nEntry point - Linear transformation',
      color: '#FF6B6B',
    },
    {
      id: 'integrate-add',
      type: 'text',
      x: 600,
      y: -100,
      width: 240,
      height: 100,
      text: '#Integrate: polynomial_add\nP₁ + P₂ over F₂\nBinary field addition (XOR)',
      color: '#4ECDC4',
    },
    {
      id: 'transform-mul',
      type: 'text',
      x: 300,
      y: 100,
      width: 240,
      height: 100,
      text: '#Transform: polynomial_mul\n||a × b|| = ||a|| × ||b||\nNorm-preserving multiplication',
      color: '#AA96DA',
    },
    {
      id: 'verify-result',
      type: 'text',
      x: 600,
      y: 100,
      width: 220,
      height: 80,
      text: '#Verify: check_norm\nConsensus voting on result',
      color: '#FCBAD3',
    },
    {
      id: 'store-output',
      type: 'text',
      x: 900,
      y: 0,
      width: 200,
      height: 80,
      text: '#Store: result\nPush to memory stack',
      color: '#FFFFD2',
    },
    {
      id: 'propagate-shift',
      type: 'text',
      x: 300,
      y: -300,
      width: 220,
      height: 80,
      text: '#Propagate: degree_shift\nPolynomial degree adjustment',
      color: '#95E1D3',
    },
    {
      id: 'backprop-compare',
      type: 'text',
      x: 600,
      y: 300,
      width: 220,
      height: 80,
      text: '#BackPropagate: compare\nPolynomial comparison check',
      color: '#F38181',
    },
  ],
  edges: [
    {
      id: 'edge-1',
      fromNode: 'observer',
      toNode: 'activate-main',
      label: 'Initialize',
    },
    {
      id: 'edge-2',
      fromNode: 'activate-main',
      toNode: 'integrate-add',
      label: 'P₁',
    },
    {
      id: 'edge-3',
      fromNode: 'activate-main',
      toNode: 'transform-mul',
      label: 'P₂',
    },
    {
      id: 'edge-4',
      fromNode: 'activate-main',
      toNode: 'propagate-shift',
      label: 'Degree',
    },
    {
      id: 'edge-5',
      fromNode: 'integrate-add',
      toNode: 'verify-result',
      label: 'Sum',
    },
    {
      id: 'edge-6',
      fromNode: 'transform-mul',
      toNode: 'verify-result',
      label: 'Product',
    },
    {
      id: 'edge-7',
      fromNode: 'verify-result',
      toNode: 'store-output',
      label: 'Verified',
    },
    {
      id: 'edge-8',
      fromNode: 'transform-mul',
      toNode: 'backprop-compare',
      label: 'Check norm',
    },
    {
      id: 'edge-9',
      fromNode: 'backprop-compare',
      toNode: 'verify-result',
      label: 'Valid',
    },
  ],
};
