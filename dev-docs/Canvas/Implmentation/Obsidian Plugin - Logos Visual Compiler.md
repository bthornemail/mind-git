# **Obsidian Plugin: Logos Visual Compiler**

## 🎯 **Core Concept**
A visual development environment inside Obsidian that turns your notes and code into an interactive, self-organizing knowledge graph that can compile, run, and evolve itself.

## 📱 **Platform Strategy**
- **Mobile**: Touch-optimized canvas with voice commands
- **Desktop**: Full keyboard shortcuts + multi-window views
- **Cloud Sync**: Real-time collaboration across devices

## 🏗️ **Plugin Architecture**

```
logos-visual-compiler/
├── manifest.json          # Obsidian plugin manifest
├── main.ts               # Core plugin logic
├── styles.css            # Styling
├── components/           # React components
│   ├── CanvasLView.tsx   # Main canvas interface
│   ├── CodeNode.tsx      # Code block visual node
│   ├── DependencyGraph.tsx # Live dependency viewer
│   └── CompileButton.tsx # One-click compilation
├── services/             # Background services
│   ├── RacketBridge.ts   # Communication with your Racket backend
│   ├── CodeScanner.ts    # File system scanning
│   └── ASTGenerator.ts   # Abstract Syntax Tree generation
└── settings/             # Plugin settings
    └── SettingsTab.ts    # Configuration UI
```

## 🎨 **Key Visual Features**

### 1. **Code Radar View**
```
[📡] Scan Project Structure
├── Detects: Racket, Python, TypeScript, Markdown files
├── Automatically creates canvas nodes for each file
├── Shows dependencies as connecting lines
└── Color codes by language/status
```
**Why**: Instantly see your entire polyglot codebase in one visual space.

### 2. **Smart Node Types**
```
🔵 Type: File Node
├── Click: Opens file in editor
├── Drag: Repositions in project structure
└── Right-click: Compile/Run options

🟢 Type: Function Node  
├── Auto-extracted from code files
├── Shows: Inputs/Outputs, Dependencies
└── Drag between files to move functionality

🟡 Type: Documentation Node
├── Links to code it documents
├── Auto-updates when code changes
└── Can generate documentation from nodes
```

### 3. **One-Click Compilation Pipeline**
```yaml
Compile Button Flow:
1. Scan canvas for connected nodes
2. Detect entry points (#main, #export nodes)
3. Generate dependency order from edges
4. Send to Racket backend for compilation
5. Display results inline on canvas
6. Update node colors: Green=✓, Red=✗
```

### 4. **Live Restructuring Tools**
```
🔄 Reorganize Button:
- Sorts nodes by:
  • Semantic similarity (code content)
  • Dependency hierarchy  
  • Frequency of edits
  • Test coverage

🎯 Focus Mode:
- Hide unrelated nodes
- Show only active development branch
- Highlight dead/unused code
```

### 5. **Mobile-Optimized Gestures**
```
Touch Gestures:
• Pinch: Zoom canvas in/out
• Two-finger drag: Pan canvas
• Long press node: Context menu
• Swipe between files: Quick navigation
• Voice: "Compile python module" → Executes

Voice Commands:
• "Find all TypeScript interfaces"
• "Show dependencies of this file"
• "Run tests for highlighted nodes"
• "Generate documentation from these"
```

## 🔧 **Actual Features You Can Use TODAY**

### Feature 1: **Codebase Import Wizard**
```typescript
// Click "Import Project" button
// → Scans your directory
// → Creates canvas nodes for each file
// → Auto-detects dependencies from imports/requires
// → Colors: Blue=Entry point, Yellow=Library, Red=Unused
```

### Feature 2: **Visual Dependency Debugger**
```
When you click a node:
• Highlights all nodes that DEPEND ON it (red glow)
• Highlights all nodes it DEPENDS ON (blue glow)
• Shows circular dependencies (pulsing orange)
• Suggests refactoring: "Move this function closer to its users"
```

### Feature 3: **Polyglot Compilation Bridge**
```
Drag Python node → Drop on Racket node
→ Plugin asks: "Convert Python to Racket?"
→ Generates equivalent Racket code
→ Creates transformation edge between nodes
→ Updates when either file changes
```

### Feature 4: **Smart Documentation Generator**
```
Select 3+ related code nodes
→ Click "Generate Docs"
→ Creates Markdown node with:
   • Function signatures
   • Example usage
   • Dependencies diagram
   • Test cases
→ Updates automatically when code changes
```

### Feature 5: **Dead Code Detector**
```
Automatic scanning shows:
• Files with no incoming edges (nobody uses them)
• Functions never called
• Unused imports
• Can safely delete with one click
```

## 🚀 **Simplest Starting Implementation**

### Phase 1 (Week 1): Basic Scanner + Canvas
```typescript
// 1. File scanner that creates simple nodes
class SimpleScanner {
  scanDirectory(path: string): CanvasNode[] {
    // Returns: {id: filepath, x: auto, y: auto, content: filename}
  }
}

// 2. Basic canvas with draggable nodes
// 3. Save/load to Obsidian .canvas format
```

### Phase 2 (Week 2): Connect to Your Racket Backend
```typescript
// 1. Add "Compile" button to nodes
// 2. Send node content to your obsidian-canvas.rkt
// 3. Display compilation results
// 4. Basic dependency detection
```

### Phase 3 (Week 3): Mobile Optimization
```typescript
// 1. Touch-friendly controls
// 2. Voice command integration
// 3. Cloud sync for canvas state
```

## 💡 **Why This Works for YOUR Situation**

### Problem: Disparate Codebases
```
Your current state:
• Racket files in ~/devopsmain/
• Python scripts scattered
• TypeScript components
• Markdown documentation
• No unified view
```

### Solution: Visual Entanglement
```
Plugin will:
1. Scan ALL files → Unified visual map
2. Auto-discover connections (imports, function calls)
3. Let you drag to reorganize (physical movement = logical restructuring)
4. One-click compile any subset
5. Mobile: Review structure on phone, make notes, sync to desktop
```

## 🎯 **Expected Outcomes**

### Week 1-2:
- **See** all your code in one interactive map
- **Click** any file to open it
- **Drag** files to group related functionality
- **Export** canvas as project documentation

### Week 3-4:
- **Compile** Racket modules directly from canvas
- **Detect** unused code automatically
- **Generate** dependency graphs
- **Mobile** view for reviewing structure

### Month 2:
- **Auto-refactor** suggestions
- **Test** generation from documentation nodes
- **Live** collaboration (if working with others)
- **Voice-controlled** development

## 🔗 **Integration with Your Existing Work**

The plugin directly uses your `obsidian-canvas.rkt` as the backend:

```
Obsidian Plugin (TypeScript)
        ↓ (HTTP/WebSocket)
Your Racket Backend (obsidian-canvas.rkt)
        ↓
Compilation/Execution
        ↓
Results displayed in Obsidian
```

## 📋 **Immediate Action Plan**

1. **Create basic Obsidian plugin skeleton**
   ```bash
   npx @obsidianjs/cli create logos-visual-compiler
   ```

2. **Implement file scanner** (2-3 hours)
   - List files in your projects
   - Create basic canvas nodes
   - Save/load .canvas format

3. **Add Racket communication** (2 hours)
   - Simple HTTP call to your running `obsidian-canvas.rkt`
   - Send node for compilation
   - Display results

4. **Test with your actual codebase** (1 hour)
   - Point at `~/devopsmain/`
   - See if it creates useful visualization
   - Try dragging nodes around

## 🎮 **The Simplest Possible Starting Point**

```typescript
// main.ts - Minimal starting plugin
export default class LogosVisualCompiler extends Plugin {
  async onload() {
    // 1. Add "Scan Project" button to ribbon
    this.addRibbonIcon('scan', 'Scan Codebase', () => {
      this.scanAndCreateCanvas();
    });

    // 2. Add "Compile Selected" button
    this.addRibbonIcon('play', 'Compile Selected', () => {
      this.compileSelectedNodes();
    });
  }

  async scanAndCreateCanvas() {
    // Simple: Scan ~/devopsmain, create nodes
    const files = await this.scanDirectory('~/devopsmain');
    const canvas = this.createCanvasFromFiles(files);
    await this.saveCanvas(canvas);
  }
}
```

## 💎 **The Core Value Proposition**

Instead of:
- Jumping between 10 different IDEs
- Manually tracking dependencies
- Forgetting what code exists where

You get:
- **One visual map** of everything
- **Natural reorganization** by dragging
- **Immediate feedback** on changes
- **Mobile access** to your entire codebase

**Start with the file scanner today.** In 2 hours, you could have your first visual map of `~/devopsmain`. Would you like me to write the exact TypeScript code for that scanner?