# 🎯 **PROPOSAL: MQTT DISCOVERY SERVICE FOR FEDERATED CANVASL KERNELS**

## **Status**: Proposal for Implementation Decision
**Domain**: DIGITAL (virtual federation system only)
**Scope**: SINGLE bounded feature - peer discovery only
**Existing System**: CanvasL Universal Metadata Kernel with WebRTC data transfer
**Dependency Check**: Uses existing Docker/Coturn infrastructure

---

## 1. PROBLEM STATEMENT

### Current Capabilities ✅
1. **Universal Metadata Kernel** analyzes any repository
2. **WebRTC connections** for data transfer between kernels
3. **Coturn/TURN server** in Docker for NAT traversal
4. **Multiple export formats** including federation manifests

### Missing Capability ❌
**No automatic peer discovery**: Kernels cannot find each other without manual configuration.

### Why This Matters
- Manual peer entry doesn't scale
- Cannot discover nearby kernels for collaboration
- Limits federation to pre-configured relationships
- Hinders emergent coordination patterns

---

## 2. PROPOSED SOLUTION: MQTT DISCOVERY SERVICE

### Single Bounded Feature
**Add MQTT-based peer discovery** to existing WebRTC data transfer layer.

### Architecture (Minimal Addition)
```
Existing: WebRTC Data Channel → Coturn/TURN → Kernel A ↔ Kernel B
New:      MQTT Discovery Topic → Mosquitto Broker → Peers discover each other
```

### Key Constraint
**Discovery only** - not replacing WebRTC for data transfer. MQTT finds peers, WebRTC connects them.

---

## 3. TECHNICAL SPECIFICATION

### 3.1 Module Structure
```
src/federation/
├── discovery/                    # NEW
│   ├── mqtt-discovery.ts        # MQTT client implementation
│   ├── discovery.interface.ts   # Abstract interface
│   └── index.ts                 # Export discovery service
├── connections/                  # EXISTING - WebRTC connections
│   ├── webrtc-connection.ts     # Already works
│   └── protocol-handlers.ts     # NEW - protocol registration
└── index.ts                     # Updated exports
```

### 3.2 Interface Design
```typescript
// src/federation/discovery/discovery.interface.ts
export interface DiscoveryService {
  /** Start discovery service */
  start(): Promise<void>;
  
  /** Stop discovery service */
  stop(): Promise<void>;
  
  /** Announce this kernel's presence */
  announceSelf(metadata: KernelMetadata): Promise<void>;
  
  /** Discover other kernels */
  discoverPeers(filter?: DiscoveryFilter): Promise<PeerInfo[]>;
  
  /** Subscribe to peer events */
  onPeerDiscovered(callback: (peer: PeerInfo) => void): UnsubscribeFunction;
  
  /** Get current peer list */
  getPeers(): PeerInfo[];
}

export interface PeerInfo {
  id: string;
  url: string;            // WebRTC signaling URL
  capabilities: string[]; // What this kernel can do
  metadata: KernelMetadata;
  lastSeen: Date;
  publicKey?: string;     // For WebAuthn/verification
}

export interface DiscoveryFilter {
  capabilities?: string[];  // Filter by capability
  minUptime?: number;      // Minimum uptime in seconds
  protocolVersion?: string; // Compatible protocol versions
}
```

### 3.3 MQTT Implementation
```typescript
// src/federation/discovery/mqtt-discovery.ts
export class MQTTDiscovery implements DiscoveryService {
  private client: mqtt.MqttClient;
  private brokerUrl: string;
  private topicPrefix: string = 'mindgit/kernels';
  private peers: Map<string, PeerInfo> = new Map();
  
  constructor(config: {
    brokerUrl?: string;  // Default: process.env.MQTT_BROKER or 'mqtt://localhost:1883'
    clientId?: string;   // Default: machine hostname + random suffix
    cleanSession?: boolean;
  }) {
    this.brokerUrl = config.brokerUrl || 'mqtt://localhost:1883';
  }
  
  async start(): Promise<void> {
    this.client = mqtt.connect(this.brokerUrl, {
      clientId: `${os.hostname()}-${Math.random().toString(36).substr(2, 9)}`,
      clean: true,
      // TLS options for WebAuthn compatibility
      rejectUnauthorized: process.env.NODE_ENV === 'production',
      // Keepalive: 60 seconds
      keepalive: 60,
    });
    
    // Listen for peer announcements
    await this.subscribeToDiscoveryTopics();
    
    // Announce self every 30 seconds
    this.startAnnouncementInterval();
  }
  
  private async subscribeToDiscoveryTopics(): Promise<void> {
    // Main discovery topic
    this.client.subscribe(`${this.topicPrefix}/+/announce`);
    
    // Capability-specific topics
    this.client.subscribe(`${this.topicPrefix}/+/capabilities/+`);
    
    // Handle incoming messages
    this.client.on('message', (topic, message) => {
      this.handleDiscoveryMessage(topic, message.toString());
    });
  }
  
  private handleDiscoveryMessage(topic: string, message: string): void {
    // Parse topic structure: mindgit/kernels/{peerId}/{messageType}
    const parts = topic.split('/');
    const peerId = parts[2];
    const messageType = parts[3];
    
    switch (messageType) {
      case 'announce':
        this.handlePeerAnnouncement(peerId, JSON.parse(message));
        break;
      case 'capabilities':
        this.handleCapabilityUpdate(peerId, JSON.parse(message));
        break;
      case 'goodbye':
        this.handlePeerDeparture(peerId);
        break;
    }
  }
}
```

---

## 4. PROTOCOL HANDLER REGISTRATION DECISION

### **DECISION NEEDED**: Should kernels register custom protocol handlers?

**Option A: Fixed Protocol Support** (Recommended - Simpler)
```typescript
// Pre-defined protocols only
export enum SupportedProtocols {
  WEBRTC_DATA = 'webrtc-data',      // Binary data transfer
  WEBRTC_STREAM = 'webrtc-stream',  // Media streams
  HTTP_REST = 'http-rest',          // REST API calls
  WS_JSONRPC = 'ws-jsonrpc',        // JSON-RPC over WebSocket
}

// Kernels announce which of these they support
```

**Option B: Dynamic Protocol Registration** (More Flexible)
```typescript
// Kernels can announce custom protocols
interface ProtocolHandler {
  protocol: string;           // e.g., 'mindgit-canvas-sync/v1'
  handler: (data: any) => Promise<any>;
  validator?: (data: any) => boolean;
  priority?: number;          // For protocol negotiation
}

// Registration system
class ProtocolRegistry {
  registerProtocol(handler: ProtocolHandler): void;
  negotiateProtocol(remoteCapabilities: string[]): string | null;
}
```

### **Recommendation: Option A (Fixed Protocols)**
**Why:**
1. **Security**: Known protocols = easier verification
2. **Interoperability**: All kernels speak same languages
3. **Simplicity**: No runtime protocol loading/validation
4. **Current need**: WebRTC data channel is sufficient for now

**Can evolve to Option B later** if dynamic protocols become necessary.

---

## 5. INTEGRATION WITH EXISTING SYSTEM

### 5.1 Modify Existing WebRTC Connection
```typescript
// src/federation/connections/webrtc-connection.ts - ADD
export class WebRTCConnection {
  // Add discovery dependency
  constructor(private discovery?: DiscoveryService) {}
  
  async connectToDiscoveredPeers(): Promise<void> {
    if (!this.discovery) return;
    
    const peers = await this.discovery.discoverPeers({
      capabilities: ['webrtc-data']  // Only peers supporting WebRTC
    });
    
    for (const peer of peers) {
      await this.connect(peer.url);
    }
  }
}
```

### 5.2 Update CLI Commands
```bash
# Existing: mind-git kernel:analyze [path]
# NEW: 
mind-git federation:discover [--broker mqtt://broker.example.com]
mind-git federation:announce [--interval 30]
mind-git federation:peers [--json]
```

### 5.3 Docker Compose Addition
```yaml
# docker-compose.federation.yml
services:
  # EXISTING
  coturn:
    image: coturn/coturn
    # ... existing config
  
  # NEW - Optional MQTT broker
  mosquitto:
    image: eclipse-mosquitto
    ports:
      - "1883:1883"    # MQTT
      - "9001:9001"    # WebSocket
    volumes:
      - ./config/mosquitto.conf:/mosquitto/config/mosquitto.conf
      - mosquitto-data:/mosquitto/data
    environment:
      - TZ=UTC
    restart: unless-stopped
```

---

## 6. IMPLEMENTATION PHASES

### **Phase 1: MQTT Discovery Only** (Week 1)
1. Implement `MQTTDiscovery` class
2. Add to federation exports
3. Basic tests: local broker discovery
4. **Deliverable**: Kernels can find each other via MQTT

### **Phase 2: Integration** (Week 2)
1. Connect discovery to existing WebRTC
2. Add CLI commands
3. Docker configuration
4. **Deliverable**: `mind-git federation:discover` works

### **Phase 3: Optional Enhancements** (Future)
1. Protocol negotiation
2. Multiple broker support
3. Discovery persistence
4. Security enhancements

---

## 7. TEST SPECIFICATION

### 7.1 Unit Tests
```typescript
// test/federation/discovery/mqtt-discovery.test.ts
describe('MQTTDiscovery', () => {
  let discovery: MQTTDiscovery;
  let broker: any; // Test MQTT broker
  
  beforeEach(async () => {
    broker = await startTestBroker();
    discovery = new MQTTDiscovery({ brokerUrl: 'mqtt://localhost:1884' });
  });
  
  test('discovers peers via MQTT', async () => {
    await discovery.start();
    
    // Simulate peer announcement
    publishTestAnnouncement('test-peer-1');
    
    // Should discover peer
    await waitFor(() => discovery.getPeers().length > 0);
    expect(discovery.getPeers()[0].id).toBe('test-peer-1');
  });
  
  test('announces self periodically', async () => {
    const announcementSpy = jest.spyOn(mqtt.Client.prototype, 'publish');
    await discovery.start();
    
    // Should announce within 30 seconds
    await waitFor(() => announcementSpy.mock.calls.length > 0);
    expect(announcementSpy).toHaveBeenCalledWith(
      expect.stringContaining('announce'),
      expect.any(String)
    );
  });
});
```

### 7.2 Integration Test
```typescript
// test/federation/integration/discovery-integration.test.ts
test('two kernels discover and connect via MQTT + WebRTC', async () => {
  // Start two kernel instances
  const kernel1 = await startTestKernel({ discovery: true });
  const kernel2 = await startTestKernel({ discovery: true });
  
  // Kernel1 should discover Kernel2 via MQTT
  const peers = await kernel1.discovery.discoverPeers();
  expect(peers).toHaveLength(1);
  expect(peers[0].url).toBe(kernel2.signalingUrl);
  
  // Should establish WebRTC connection
  await kernel1.connectToDiscoveredPeers();
  expect(kernel1.connections.size).toBe(1);
});
```

---

## 8. SECURITY CONSIDERATIONS

### **Authentication Options**
1. **MQTT TLS + Client Certificates** (Recommended)
   - Mutual TLS authentication
   - Works with WebAuthn infrastructure
   - Verified peer identity

2. **JWT Tokens in MQTT Messages**
   - Signed announcements
   - Expiry and revocation
   - Compatible with existing auth

3. **Simple at First, Secure Later**
   - Phase 1: No auth (local/dev)
   - Phase 2: TLS certificates
   - Phase 3: WebAuthn integration

### **Privacy**
- Announcement metadata minimal by default
- Opt-in detailed capability sharing
- Peer IDs not tied to real identity
- Local broker option for private networks

---

## 9. DEPLOYMENT OPTIONS

### **Broker Options (Flexible)**
1. **Local Broker** (Default)
   ```bash
   docker run -p 1883:1883 eclipse-mosquitto
   ```

2. **Cloud Broker** (Scalable)
   ```bash
   # AWS IoT Core, Azure IoT Hub, HiveMQ Cloud
   export MQTT_BROKER="ssl://your-broker.amazonaws.com:8883"
   ```

3. **Embedded Broker** (Self-contained)
   ```typescript
   // Option: Use aedes or mosquito embedded
   import { createServer } from 'aedes';
   const broker = createServer();
   ```

### **Discovery Modes**
```typescript
// Configurable based on environment
export enum DiscoveryMode {
  NONE = 'none',           // No discovery (current)
  LOCAL_MQTT = 'local',    // Local broker (Phase 1)
  FEDERATED = 'federated', // Multiple brokers (Future)
  HYBRID = 'hybrid',       // Local + cloud (Future)
}
```

---

## 10. DECISION CHECKLIST FOR CODING AGENT

### **Must Implement** ✅
- [ ] `MQTTDiscovery` class with basic announce/discover
- [ ] Integration with existing WebRTC connection
- [ ] CLI command: `federation:discover`
- [ ] Unit tests for discovery
- [ ] Docker Compose for Mosquitto

### **Defer for Later** ⏳  
- [ ] Dynamic protocol registration (Option B)
- [ ] Multiple broker federation
- [ ] Advanced security (TLS certs)
- [ ] Discovery persistence
- [ ] Protocol negotiation

### **Explicitly NOT Doing** ❌
- Replacing WebRTC with MQTT for data transfer
- Implementing IPv5/IPv8 networking
- Adding new Docker services beyond Mosquitto
- Changing existing Coturn/TURN setup

---

## 11. SUCCESS METRICS

### **Phase 1 Success Criteria**
1. Two kernels on same network discover each other
2. Discovery → WebRTC connection established automatically
3. All existing tests still pass (87+ tests)
4. CLI command provides peer list
5. Docker compose starts broker + kernel

### **Measurable Outcomes**
- Discovery latency: < 5 seconds on LAN
- Memory usage: < 50MB additional for MQTT client
- Connection success rate: > 95% for discovered peers
- No regression in existing functionality

---

## **APPROVAL REQUEST**

**To the coding agent**: Please review this proposal and:

1. **Assess feasibility** with current codebase
2. **Identify conflicts** with existing systems
3. **Estimate effort** for Phase 1
4. **Propose implementation order**
5. **Flag any safety protocol violations**

**Decision**: Should we proceed with Phase 1 (MQTT Discovery Only) as specified?

---

*This proposal follows RFC-LOGOS-AST-01 constraints:*
- ✅ SINGLE bounded feature (discovery only)
- ✅ DIGITAL domain only
- ✅ Builds on existing infrastructure
- ✅ Clear success criteria
- ✅ Measurable outcomes