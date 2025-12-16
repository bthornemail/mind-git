import { EmergentIntelligence, NodeConfig } from './core/EmergentIntelligence';

export * from './core/EmergentIntelligence';
export * from './network/NetworkManager';
export * from './ai/AIDecisionEngine';
export * from './interfaces/TerminalInterface';
export * from './interfaces/WebInterface';

export { EmergentIntelligence as default };

export async function createEmergentNode(config: NodeConfig): Promise<EmergentIntelligence> {
  const node = new EmergentIntelligence(config);
  await node.initialize();
  return node;
}

export function getDefaultConfig(role: 'coordinator' | 'worker' | 'hybrid' = 'worker'): NodeConfig {
  return {
    id: `node-${Math.random().toString(36).substr(2, 9)}`,
    role,
    mqttBroker: 'localhost',
    mqttPort: 1883,
    webrtcPort: 8080,
    webPort: 3000,
    aiInterval: 30
  };
}