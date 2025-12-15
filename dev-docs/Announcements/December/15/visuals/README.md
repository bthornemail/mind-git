# 🎨 Visual Assets for mind-git v1.1.0 Launch

This folder contains all visual content generation materials for the npm release announcement.

## 📁 Contents

### 1. [terminal-demo.sh](./terminal-demo.sh)
**Ready-to-record terminal demonstration script**

Features:
- Complete workflow demonstration
- Color-coded output
- Timing delays for smooth recording
- 5-step process showcase

**Usage:**
```bash
# Make executable
chmod +x terminal-demo.sh

# Record with asciinema
asciinema rec mind-git-demo.cast -c ./terminal-demo.sh

# Convert to GIF
npm install -g @asciinema/gif-generator
agg mind-git-demo.cast demo.gif --speed 1.5

# Or convert to MP4
docker run --rm -v $PWD:/data asciinema/asciicast2mp4 \
  mind-git-demo.cast demo.mp4
```

**Output:** Terminal recording suitable for:
- Twitter/X video posts
- README.md embedded GIF
- Documentation tutorials
- Social media clips

---

### 2. [architecture-diagrams.md](./architecture-diagrams.md)
**6 Mermaid diagrams ready to render**

Diagrams included:
1. **Complete Compilation Pipeline** - End-to-end flow
2. **Mathematical Foundation Layers** - 8-layer architecture
3. **1,400-Year Timeline** - Historical development
4. **Node Classification System** - Prefix mapping
5. **Spatial to Code Transformation** - Visual explanation
6. **Package Structure** - npm package organization

**Usage:**
```bash
# Install Mermaid CLI
npm install -g @mermaid-js/mermaid-cli

# Render all diagrams to PNG
mmdc -i architecture-diagrams.md -o diagrams/ --outputFormat png

# Render individual diagram
mmdc -i architecture-diagrams.md -e png -o compilation-pipeline.png

# Use dark theme
mmdc -i architecture-diagrams.md -t dark -o diagrams/
```

**Output:** High-quality diagrams for:
- GitHub README
- Documentation
- Blog posts
- Presentations
- Social media (rendered as images)

**Online Editor:** https://mermaid.live
- Paste diagram code
- Customize theme
- Export PNG/SVG

---

### 3. [demo-video-script.md](./demo-video-script.md)
**3 complete video scripts with timing**

Videos included:
1. **Quick Start (60s)** - Social media short
2. **Technical Deep Dive (5min)** - YouTube main
3. **Use Case Showcase (3min)** - Developer adoption

Each script includes:
- Shot-by-shot breakdown
- Voiceover text
- Timing markers
- Visual descriptions
- B-roll suggestions

**Bonus content:**
- Recording setup tips
- Export settings for each platform
- Thumbnail design templates
- Publishing checklist
- Promotion strategy

---

### 4. [image-generation-prompts.md](./image-generation-prompts.md)
**10 AI image generation prompts**

Images for:
1. Launch Banner (Twitter/LinkedIn header)
2. npm Package Card (square social)
3. Mathematical Timeline Infographic
4. Architecture Diagram Illustration
5. Spatial Programming Concept Art
6. Compiler Pipeline Visualization
7. Mathematical Foundation Visualization
8. YouTube Thumbnail Template
9. GitHub Repository Social Card
10. Announcement Hero Image

**Supported AI tools:**
- DALL-E 3 (OpenAI)
- Stable Diffusion (Stability AI)
- Midjourney (Discord)

**Usage:**
```bash
# Using DALL-E 3
curl -X POST https://api.openai.com/v1/images/generations \
  -H "Authorization: Bearer $OPENAI_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"model": "dall-e-3", "prompt": "...", "size": "1792x1024"}'

# Or use web interfaces:
# - OpenAI Playground: platform.openai.com
# - Midjourney: midjourney.com
# - DreamStudio: beta.dreamstudio.ai
```

---

## 🚀 Quick Start Guide

### Immediate Actions (15 minutes)

**Step 1: Terminal Recording**
```bash
cd visuals/
chmod +x terminal-demo.sh
asciinema rec demo.cast -c ./terminal-demo.sh
# Upload to asciinema.org or convert to GIF
```

**Step 2: Render Diagrams**
```bash
npm install -g @mermaid-js/mermaid-cli
mmdc -i architecture-diagrams.md -t dark -o rendered/
# Upload rendered PNGs to announcements
```

**Step 3: Generate One Key Image**
- Go to https://openai.com/dall-e-3 or https://www.bing.com/create
- Copy "Launch Banner" prompt from image-generation-prompts.md
- Generate and download
- Use as Twitter/LinkedIn header

**Step 4: Quick Social Media Post**
```bash
# Use terminal recording GIF
# Add text: "mind-git v1.1.0 is now on npm! 🚀"
# Include: npm install -g mind-git
# Post to Twitter, LinkedIn, Reddit
```

---

## 📊 Priority Matrix

### High Priority (Create Today)
- ✅ Terminal demo GIF - Most engaging, shows actual product
- ✅ Architecture diagram PNG - Explains concept clearly
- ✅ Launch banner - Professional first impression

### Medium Priority (This Week)
- 📹 60-second quick start video - Social media reach
- 🎨 npm package card - Shareable image
- 📈 Timeline infographic - Educational value

### Low Priority (Next Week)
- 📹 5-minute deep dive - YouTube content
- 🎨 Full image set - Complete visual library
- 📹 Use case videos - Targeted marketing

---

## 🛠️ Required Tools

### Free Tools
- **asciinema**: Terminal recording
  ```bash
  pip install asciinema
  ```

- **Mermaid CLI**: Diagram rendering
  ```bash
  npm install -g @mermaid-js/mermaid-cli
  ```

- **OBS Studio**: Screen recording (free)
  - Download: https://obsproject.com

- **Figma**: Design and editing (free tier)
  - Web-based: https://figma.com

### Optional Paid Tools
- **DALL-E 3**: $20 for 115 images
- **Midjourney**: $10/month for unlimited
- **Camtasia**: Professional video editing ($249)

### Free Alternatives
- **Bing Image Creator**: Free DALL-E 3 access
- **DaVinci Resolve**: Free video editing
- **GIMP**: Free image editing

---

## 📏 Asset Specifications

### Social Media Sizes
| Platform | Size | Format | Notes |
|----------|------|--------|-------|
| Twitter Post | 1200x675px | PNG/MP4 | 16:9 aspect |
| Twitter Header | 1500x500px | PNG | 3:1 aspect |
| LinkedIn Post | 1200x627px | PNG/MP4 | ~2:1 aspect |
| LinkedIn Cover | 1128x191px | PNG | Personal profile |
| Instagram Post | 1080x1080px | PNG/MP4 | 1:1 square |
| GitHub Social | 1280x640px | PNG | <1MB size |
| YouTube Thumb | 1280x720px | PNG | 16:9 HD |
| YouTube Video | 1920x1080px | MP4 | 1080p 60fps |

### File Naming Convention
```
mindgit-[version]-[type]-[platform]-[size].[ext]

Examples:
mindgit-v1.1.0-banner-twitter-1200x675.png
mindgit-v1.1.0-demo-youtube-1920x1080.mp4
mindgit-v1.1.0-diagram-github-1280x640.png
```

---

## ✅ Quality Checklist

Before publishing any visual asset:

**Technical Quality**
- [ ] Correct dimensions for platform
- [ ] File size optimized (<1MB for images, <50MB for videos)
- [ ] High resolution (2x for retina displays)
- [ ] Compressed but not degraded

**Content Quality**
- [ ] Text is readable at thumbnail size
- [ ] Branding is consistent (colors, fonts, logo)
- [ ] No typos or errors
- [ ] Key message is clear in <3 seconds

**Accessibility**
- [ ] High contrast (WCAG AA minimum)
- [ ] Alt text written
- [ ] Subtitles/captions for videos
- [ ] Color-blind friendly palette

**Legal**
- [ ] No copyrighted material used
- [ ] AI-generated images rights verified
- [ ] Proper attribution if needed
- [ ] npm/GitHub logos used correctly

---

## 🎯 Success Metrics

Track these metrics for each visual:

### Engagement
- Views/impressions
- Likes/reactions
- Shares/retweets
- Comments
- Click-through rate

### Conversion
- npm downloads spike
- GitHub stars increase
- README views
- Documentation visits

### Best Performers (Update as data comes in)
- **Terminal GIF**: ___ views, ___ shares
- **Architecture Diagram**: ___ clicks
- **60s Video**: ___ watch time

Use this data to guide future visual content creation.

---

## 🤝 Contributing Visuals

If you create additional visual assets:

1. **Follow naming convention** above
2. **Document specifications** (size, format, purpose)
3. **Add to appropriate folder**
4. **Update this README**
5. **Submit PR** with preview image

---

## 📞 Support

**Issues with tools?**
- Mermaid rendering: https://github.com/mermaid-js/mermaid-cli/issues
- asciinema: https://github.com/asciinema/asciinema/issues
- General questions: Open issue on main repo

**Need custom visuals?**
- Describe requirement in GitHub issue
- Include dimensions and platform
- Tag with "visuals" label

---

## 🔗 Quick Links

- Main announcement: [../release-announcement.md](../release-announcement.md)
- Press release: [../press-release.md](../press-release.md)
- npm package: https://www.npmjs.com/package/mind-git
- GitHub repo: https://github.com/bthornemail/mind-git

---

**Ready to create visuals?** Start with the terminal demo - it's the quickest win! 🚀
