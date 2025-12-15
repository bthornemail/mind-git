/**
 * MQTT Broker Setup Instructions
 * 
 * For the MQTT integration to work, you need an MQTT broker running.
 * Here are a few options:
 * 
 * 1. Mosquitto (Recommended for development):
 *    # Install Mosquitto
 *    sudo apt-get install mosquitto mosquitto-clients  # Ubuntu/Debian
 *    brew install mosquitto                            # macOS
 *    
 *    # Start Mosquitto with WebSocket support
 *    mosquitto -p 1883 -p 9001 -l /var/log/mosquitto.log
 *    
 * 2. Docker Mosquitto:
 *    docker run -it -p 1883:1883 -p 9001:9001 eclipse-mosquitto
 *    
 * 3. Cloud MQTT Brokers:
 *    - HiveMQ Cloud (free tier available)
 *    - EMQX Cloud
 *    - AWS IoT Core
 * 
 * Configuration for WebSocket support:
 * Add this to mosquitto.conf:
 * 
 * listener 9001
 * protocol websockets
 * allow_anonymous true
 * 
 * Testing the connection:
 * 
 * # Subscribe to topic
 * mosquitto_sub -h localhost -p 1883 -t "mind-git/canvas/updates"
 * 
 * # Publish message
 * mosquitto_pub -h localhost -p 1883 -t "mind-git/canvas/updates" -m '{"type":"test","data":"hello"}'
 * 
 * WebSocket testing:
 * Use browser WebSocket console:
 * 
 * const ws = new WebSocket('ws://localhost:9001');
 * ws.onopen = () => console.log('Connected');
 * ws.send('CONNECT {"clientId":"test"}\x00');
 * ws.send('SUBSCRIBE {"topics":[{"topic":"mind-git/canvas/updates"}]}\x00');
 */

// Simple MQTT broker verification script
const mqtt = require('mqtt');

async function testMQTTConnection() {
  console.log('🔍 Testing MQTT connection...');
  
  try {
    // Test connection to broker
    const client = mqtt.connect('mqtt://localhost:1883', {
      clientId: 'test-connection',
      clean: true,
      connectTimeout: 5000
    });

    client.on('connect', () => {
      console.log('✅ Connected to MQTT broker successfully');
      
      // Test subscription
      client.subscribe('mind-git/canvas/test', (err) => {
        if (err) {
          console.error('❌ Subscription failed:', err);
        } else {
          console.log('✅ Subscribed to test topic');
          
          // Test publish
          client.publish('mind-git/canvas/test', JSON.stringify({
            type: 'test',
            message: 'Hello from test script',
            timestamp: Date.now()
          }), (err) => {
            if (err) {
              console.error('❌ Publish failed:', err);
            } else {
              console.log('✅ Test message published');
            }
            
            setTimeout(() => {
              client.end();
              console.log('🔌 Disconnected from broker');
            }, 1000);
          });
        }
      });
    });

    client.on('message', (topic, message) => {
      console.log('📨 Received message:', topic, message.toString());
    });

    client.on('error', (err) => {
      console.error('❌ MQTT connection error:', err.message);
      console.log('\n💡 Make sure MQTT broker is running:');
      console.log('   sudo apt-get install mosquitto');
      console.log('   mosquitto -p 1883 -p 9001');
    });

  } catch (error) {
    console.error('❌ Failed to connect to MQTT broker:', error.message);
  }
}

// Run test if this script is executed directly
if (require.main === module) {
  testMQTTConnection();
}

module.exports = { testMQTTConnection };