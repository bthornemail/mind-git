# 🎥 mind-git Demo Video Script

## Video 1: Quick Start (60 seconds)

### Target Platforms
- Twitter/X (video post)
- LinkedIn (native video)
- YouTube Shorts
- TikTok (tech community)

### Script

**[0:00-0:05] Hook**
```
Visual: Dark terminal with mind-git logo animation
Voiceover: "What if your spatial diagrams... were executable code?"
Text overlay: "mind-git v1.1.0"
```

**[0:05-0:15] Installation**
```
Visual: Terminal typing animation
Command: npm install -g mind-git
Output: ✅ mind-git@1.1.0 installed
Voiceover: "Install with one command. Available now on npm."
```

**[0:15-0:30] Canvas Creation**
```
Visual: Split screen
  Left: Visual canvas with nodes and edges
  Right: JSON representation
Animation: Nodes appearing with labels
  - #Observe: main
  - #Activate: start
  - #Transform: compute
Voiceover: "Create spatial programs using simple node prefixes."
```

**[0:30-0:45] Compilation**
```
Visual: Terminal
Command: mind-git compile hello.json
Output animation:
  🎯 Compiling...
  ✅ Parsed 4 nodes, 2 edges
  📄 Generated JavaScript (1ms)
  💾 Saved to output.js
Voiceover: "Compile to verified JavaScript in milliseconds."
```

**[0:45-0:55] Execution**
```
Visual: Split screen
  Left: Generated code scrolling
  Right: Execution output
Animation: Code highlighting as it executes
Voiceover: "Your spatial diagram is now executable code."
```

**[0:55-1:00] Call to Action**
```
Visual: Clean slide with:
  npm install -g mind-git
  npmjs.com/package/mind-git
  github.com/bthornemail/mind-git
Voiceover: "Start spatial programming today."
```

---

## Video 2: Technical Deep Dive (5 minutes)

### Target Platforms
- YouTube (main channel)
- Dev.to embedded video
- Conference presentations

### Script

**[0:00-0:30] Introduction**
```
Title: "mind-git: 1,400 Years of Math in One Compiler"
Host on camera or screen recording
- What is spatial programming?
- Why mathematical verification matters
- Quick demo teaser
```

**[0:30-1:30] Mathematical Foundation**
```
Visual: Animated timeline
628 AD: Brahmagupta (2D complex numbers)
  Show: (a² + b²)(c² + d²) = ...

1748: Euler (4D quaternions)
  Show: Four-square identity

1928: Degen (8D octonions)
  Show: Eight-square identity

1960: Adams (8D limit proof)
  Show: Hopf invariant one theorem

Voiceover: "This isn't arbitrary. These are the only dimensions where
normed division algebras exist - a fundamental constraint of mathematical reality."
```

**[1:30-2:30] How It Works**
```
Visual: Animated flow diagram
1. Canvas JSON → Parser
   Show: Node classification by prefix

2. Parser → AST
   Show: Spatial positions become polynomial degrees

3. AST → AAL Assembly
   Show: 11-dimensional modal types

4. AAL → JavaScript/TypeScript/Racket
   Show: Multi-language output

5. Coq Verification
   Show: Formal proofs validating correctness
```

**[2:30-3:30] Live Coding Demo**
```
Screen recording: Build a simple API
1. Create canvas with nodes:
   - #Activate: createServer
   - #Transform: handleRequest
   - #Verify: authenticate
   - #Store: database

2. Connect edges showing flow

3. Compile: mind-git compile api.json

4. Show generated code

5. Execute: node output.js

6. Test: curl localhost:3000
```

**[3:30-4:15] Advanced Features**
```
Visual: Code + diagrams
- Norm preservation guarantees
- Hopf fibration optimizations (degrees 1,3,7)
- Polynomial degree reduction
- Dimensional analysis
- Complexity scoring

Show actual test output:
  "✅ 85+ tests passing"
  "✅ Coq proofs verified"
```

**[4:15-4:45] Comparison**
```
Split screen comparison:
Traditional Visual Programming | mind-git
- Metaphor for code          | Mathematical structure
- Manual verification        | Formal proofs
- Fixed dimensions           | Respects physical limits
- Single language            | Multi-language output
- No mathematical guarantees | 1,400 years of proofs
```

**[4:45-5:00] Call to Action**
```
Visual: Resources slide
- GitHub: github.com/bthornemail/mind-git
- npm: npmjs.com/package/mind-git
- Documentation: Full examples and API docs
- Contributing: Open source, MIT license

Voiceover: "Join us in building the future of spatial programming.
The mathematics doesn't lie - and now you can prove it."
```

---

## Video 3: Use Case Showcase (3 minutes)

### Target: Developers considering adoption

**[0:00-0:20] Problem Statement**
```
Voiceover: "Three common problems in software development..."
Visual: Screen showing:
1. Complex architecture diagrams that don't match code
2. Manual verification of system correctness
3. Code scattered across dozens of files
```

**[0:20-1:00] Solution: Spatial API Design**
```
Live demo: Building a REST API
Visual: Canvas showing:
- Authentication flow
- Request routing
- Database operations
- Response formatting

Compile → Show generated Express.js server
Run → Show working API
```

**[1:00-1:40] Solution: Mathematical Verification**
```
Live demo: Cryptographic system
Visual: Canvas showing:
- Key generation
- Encryption
- Decryption
- Signature verification

Show: Coq proofs validating correctness
Show: Test results with norm preservation
Voiceover: "Mathematical guarantee: ||encrypt(m)|| = ||m||"
```

**[1:40-2:20] Solution: Multi-language Output**
```
Same canvas, different outputs:
1. Compile to JavaScript → Node.js app
2. Compile to TypeScript → Type-safe API
3. Compile to Racket → Functional implementation
4. Compile to WebAssembly → Browser execution

Visual: Split screen showing same functionality in each language
```

**[2:20-3:00] Results**
```
Visual: Metrics and testimonials
- 10.6x compression via polynomial encoding
- 1ms compilation time
- 85+ tests, 100% core coverage
- Formal verification included
- 270kB package size

Call to action: Try it yourself
npm install -g mind-git
```

---

## Recording Tips

### For Terminal Recordings
```bash
# Use asciinema for best quality
asciinema rec demo.cast --overwrite

# Convert to GIF
npm install -g @asciinema/gif-generator
agg demo.cast demo.gif --speed 1.5

# Or convert to MP4
docker run --rm -v $PWD:/data asciinema/asciicast2mp4 demo.cast demo.mp4
```

### For Screen Recording
```bash
# Linux: Use OBS Studio or SimpleScreenRecorder
obs --startrecording --scene "Terminal"

# Set resolution: 1920x1080
# Frame rate: 60fps for smooth animations
# Audio: 44.1kHz mono for voiceover
```

### Visual Effects
- Use syntax highlighting: Dracula theme or Nord
- Terminal: iTerm2 with custom fonts (JetBrains Mono)
- Add subtle zoom-ins for important code
- Highlight changed lines with borders/arrows
- Use color-coded sections (input=blue, output=green, error=red)

### Music Suggestions (Royalty-Free)
- Upbeat tech background: Search "coding music no copyright"
- Keep volume low (-20dB) to not overpower voiceover
- Fade in/out at transitions

### Voiceover Tips
- Clear, confident tone
- Pace: 140-160 words per minute
- Emphasize key terms: "polynomial algebra", "formal verification", "1,400 years"
- End sentences definitively - avoid upspeak
- Record in quiet room with good mic (even phone is okay)

### Export Settings
**YouTube:**
- Resolution: 1920x1080 (1080p)
- Frame rate: 60fps
- Bitrate: 12 Mbps (VBR)
- Format: MP4 (H.264)

**Twitter:**
- Resolution: 1280x720 (720p) max
- Duration: 2:20 max
- Format: MP4
- Size: <512MB

**LinkedIn:**
- Resolution: 1920x1080
- Duration: 10 minutes max
- Format: MP4
- Size: <5GB

---

## B-Roll Footage Ideas

### Visual Elements to Capture
1. **Terminal animations**: Colorful compilation output
2. **Code scrolling**: Generated JavaScript with syntax highlighting
3. **Canvas diagrams**: Animated node connections
4. **Mathematical formulas**: LaTeX-rendered equations
5. **Test output**: Green checkmarks appearing
6. **Architecture diagrams**: Animated Mermaid charts
7. **Historical timeline**: Mathematician portraits with dates
8. **npm package page**: Live download stats

### Stock Footage Sources (Free)
- Pexels.com: Tech and coding footage
- Pixabay.com: Abstract mathematical animations
- Unsplash.com: Static images of mathematicians
- NASA Image Library: Space/dimensional imagery

---

## Thumbnail Designs

### Quick Start Video Thumbnail
```
Layout:
- Dark background (#0f172a)
- Left: Canvas diagram with glowing nodes
- Right: Terminal with green ✅
- Top text: "SPATIAL PROGRAMMING"
- Bottom text: "1,400 Years of Math"
- Corner: "1:00" duration badge
```

### Deep Dive Video Thumbnail
```
Layout:
- Split screen
- Left: Historical timeline (628 AD → 2025)
- Right: Modern code editor
- Center: Large "mind-git" logo
- Top text: "The Math Behind"
- Bottom text: "Visual Programming"
```

### Use Case Video Thumbnail
```
Layout:
- Canvas diagram as background (blurred)
- Center: "BUILD APIs SPATIALLY"
- Show: 3 small screenshots of output (JS, TS, Racket)
- Bottom right: npm logo with "v1.1.0"
```

### Tools for Thumbnails
- Canva.com (templates available)
- Figma (professional design)
- Photopea.com (free Photoshop alternative)
- GIMP (open source)

---

## Publishing Checklist

### Pre-recording
- [ ] Test all commands work
- [ ] Prepare clean terminal environment
- [ ] Set up screen recording software
- [ ] Test audio levels
- [ ] Prepare script/talking points

### Recording
- [ ] Record 3 takes minimum
- [ ] Capture B-roll footage
- [ ] Record voiceover separately if needed
- [ ] Get reaction shots if on camera

### Post-production
- [ ] Edit video (cuts, transitions)
- [ ] Add background music
- [ ] Add text overlays
- [ ] Color grade if needed
- [ ] Export in multiple formats

### Publishing
- [ ] Upload to YouTube (unlisted first)
- [ ] Create custom thumbnail
- [ ] Write description with links
- [ ] Add timestamps in description
- [ ] Set tags: spatial-programming, mathematics, compiler, visual-programming
- [ ] Add to playlists
- [ ] Share on social media
- [ ] Embed in README and blog posts

### Promotion
- [ ] Tweet with video link
- [ ] LinkedIn post with video
- [ ] Reddit r/programming
- [ ] Dev.to article with embedded video
- [ ] Hacker News (Show HN)
- [ ] Discord communities
- [ ] Email newsletter (if applicable)
