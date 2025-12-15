/**
 * Scene Library
 * Collection of example canvas scenes demonstrating different aspects of spatial programming
 */

import { Canvas } from '../types';
import { exampleCanvas } from '../exampleCanvas';

/**
 * Scene metadata
 */
export interface Scene {
  id: string;
  name: string;
  description: string;
  canvas: Canvas;
  tags: string[];
}

/**
 * Simple hello world scene
 */
const helloWorldCanvas: Canvas = {
  nodes: [
    {
      id: 'observer',
      type: 'text',
      x: 0,
      y: 0,
      width: 200,
      height: 80,
      text: '#Observe: Origin\nHello World!',
    },
    {
      id: 'hello',
      type: 'text',
      x: 300,
      y: 0,
      width: 200,
      height: 80,
      text: '#Activate: hello\nconsole.log("Hello, World!");',
    },
  ],
  edges: [
    {
      id: 'edge-1',
      fromNode: 'observer',
      toNode: 'hello',
      label: 'start',
    },
  ],
};

/**
 * Identity chain demonstration
 */
const identityChainCanvas: Canvas = {
  nodes: [
    {
      id: 'observer',
      type: 'text',
      x: 0,
      y: 0,
      width: 220,
      height: 80,
      text: '#Observe: Identity\nP₀ = 1',
    },
    {
      id: 'brahma-2d',
      type: 'text',
      x: 400,
      y: -200,
      width: 240,
      height: 100,
      text: '#Transform: brahmagupta\n2D Complex Numbers\n(628 AD)',
    },
    {
      id: 'euler-4d',
      type: 'text',
      x: 400,
      y: 0,
      width: 240,
      height: 100,
      text: '#Transform: euler\n4D Quaternions\n(1748)',
    },
    {
      id: 'degen-8d',
      type: 'text',
      x: 400,
      y: 200,
      width: 240,
      height: 100,
      text: '#Transform: degen\n8D Octonions\n(1818)',
    },
    {
      id: 'verify',
      type: 'text',
      x: 750,
      y: 0,
      width: 220,
      height: 80,
      text: '#Verify: adams\nAdams Theorem:\n8D limit proven',
    },
  ],
  edges: [
    { id: 'e1', fromNode: 'observer', toNode: 'brahma-2d', label: '2D' },
    { id: 'e2', fromNode: 'observer', toNode: 'euler-4d', label: '4D' },
    { id: 'e3', fromNode: 'observer', toNode: 'degen-8d', label: '8D' },
    { id: 'e4', fromNode: 'brahma-2d', toNode: 'verify', label: 'norms' },
    { id: 'e5', fromNode: 'euler-4d', toNode: 'verify', label: 'preserved' },
    { id: 'e6', fromNode: 'degen-8d', toNode: 'verify', label: 'exactly' },
  ],
};

/**
 * All node types demonstration
 */
const allNodesCanvas: Canvas = exampleCanvas;

/**
 * WebRTC demo scene
 */
const webrtcDemoCanvas: Canvas = {
  nodes: [
    {
      id: 'observer',
      type: 'text',
      x: 0,
      y: 0,
      width: 200,
      height: 80,
      text: '#Observe: WebRTC\nPeer-to-peer origin',
    },
    {
      id: 'init',
      type: 'text',
      x: 300,
      y: -150,
      width: 220,
      height: 80,
      text: '#Activate: initPeer\nInitialize RTC connection',
    },
    {
      id: 'offer',
      type: 'text',
      x: 300,
      y: 0,
      width: 220,
      height: 80,
      text: '#Propagate: sendOffer\nBroadcast SDP offer',
    },
    {
      id: 'answer',
      type: 'text',
      x: 300,
      y: 150,
      width: 220,
      height: 80,
      text: '#BackPropagate: receiveAnswer\nProcess SDP answer',
    },
    {
      id: 'integrate',
      type: 'text',
      x: 600,
      y: 0,
      width: 220,
      height: 80,
      text: '#Integrate: dataChannel\nMerge peer streams',
    },
    {
      id: 'verify',
      type: 'text',
      x: 900,
      y: 0,
      width: 220,
      height: 80,
      text: '#Verify: connection\nValidate peer state',
    },
  ],
  edges: [
    { id: 'e1', fromNode: 'observer', toNode: 'init', label: 'start' },
    { id: 'e2', fromNode: 'init', toNode: 'offer', label: 'SDP' },
    { id: 'e3', fromNode: 'offer', toNode: 'answer', label: 'negotiate' },
    { id: 'e4', fromNode: 'answer', toNode: 'integrate', label: 'channel' },
    { id: 'e5', fromNode: 'integrate', toNode: 'verify', label: 'test' },
  ],
};

/**
 * MQTT demo scene
 */
const mqttDemoCanvas: Canvas = {
  nodes: [
    {
      id: 'observer',
      type: 'text',
      x: 0,
      y: 0,
      width: 200,
      height: 80,
      text: '#Observe: MQTT\nMessage broker origin',
    },
    {
      id: 'connect',
      type: 'text',
      x: 300,
      y: -100,
      width: 220,
      height: 80,
      text: '#Activate: connect\nmqtt://broker',
    },
    {
      id: 'subscribe',
      type: 'text',
      x: 600,
      y: -100,
      width: 220,
      height: 80,
      text: '#Integrate: subscribe\ntopic/spatial/*',
    },
    {
      id: 'publish',
      type: 'text',
      x: 300,
      y: 100,
      width: 220,
      height: 80,
      text: '#Propagate: publish\nBroadcast messages',
    },
    {
      id: 'receive',
      type: 'text',
      x: 600,
      y: 100,
      width: 220,
      height: 80,
      text: '#BackPropagate: onMessage\nHandle incoming data',
    },
    {
      id: 'store',
      type: 'text',
      x: 900,
      y: 0,
      width: 220,
      height: 80,
      text: '#Store: buffer\nQueue messages',
    },
  ],
  edges: [
    { id: 'e1', fromNode: 'observer', toNode: 'connect', label: 'init' },
    { id: 'e2', fromNode: 'connect', toNode: 'subscribe', label: 'topics' },
    { id: 'e3', fromNode: 'connect', toNode: 'publish', label: 'send' },
    { id: 'e4', fromNode: 'subscribe', toNode: 'receive', label: 'messages' },
    { id: 'e5', fromNode: 'publish', toNode: 'receive', label: 'echo' },
    { id: 'e6', fromNode: 'receive', toNode: 'store', label: 'cache' },
  ],
};

/**
 * All available scenes
 */
export const SCENES: Scene[] = [
  {
    id: 'hello-world',
    name: 'Hello World',
    description: 'Simple introduction to spatial programming',
    canvas: helloWorldCanvas,
    tags: ['beginner', 'simple', 'tutorial'],
  },
  {
    id: 'identity-chain',
    name: 'Identity Chain',
    description: 'Mathematical journey from 2D to 8D',
    canvas: identityChainCanvas,
    tags: ['mathematical', 'educational', 'history'],
  },
  {
    id: 'all-nodes',
    name: 'All Node Types',
    description: 'Demonstration of all 8 mathematical node types',
    canvas: allNodesCanvas,
    tags: ['complete', 'reference', 'educational'],
  },
  {
    id: 'webrtc-demo',
    name: 'WebRTC Communication',
    description: 'Peer-to-peer real-time communication flow',
    canvas: webrtcDemoCanvas,
    tags: ['networking', 'realtime', 'webrtc'],
  },
  {
    id: 'mqtt-demo',
    name: 'MQTT Messaging',
    description: 'Publish-subscribe message broker pattern',
    canvas: mqttDemoCanvas,
    tags: ['networking', 'iot', 'mqtt'],
  },
];

/**
 * Get scene by ID
 */
export function getSceneById(id: string): Scene | undefined {
  return SCENES.find((scene) => scene.id === id);
}

/**
 * Get scenes by tag
 */
export function getScenesByTag(tag: string): Scene[] {
  return SCENES.filter((scene) => scene.tags.includes(tag));
}

/**
 * Get all unique tags
 */
export function getAllSceneTags(): string[] {
  const tags = new Set<string>();
  SCENES.forEach((scene) => scene.tags.forEach((tag) => tags.add(tag)));
  return Array.from(tags).sort();
}
