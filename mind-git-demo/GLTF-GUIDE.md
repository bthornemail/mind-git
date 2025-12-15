# GLTF/GLB Model Guide for mind-git Visualizer

## Overview

The mind-git visualizer now supports **GLTF** (JSON-based, human-readable) and **GLB** (binary, efficient) 3D model formats. This allows you to:

- Use custom 3D models for each node type
- Export canvases as GLTF/GLB files
- Create visually stunning and mathematically meaningful representations
- Optimize loading performance with binary GLB format

---

## GLTF vs GLB

### GLTF (Graphics Language Transmission Format)
- **Format**: JSON-based, human-readable
- **File extension**: `.gltf`
- **Pros**:
  - Easy to inspect and debug
  - Can be edited in text editors
  - Good for development
- **Cons**:
  - Larger file size
  - Slower to parse
  - Requires separate texture files

### GLB (Binary GLTF)
- **Format**: Binary, machine-readable
- **File extension**: `.glb`
- **Pros**:
  - Smaller file size (30-50% reduction)
  - Faster loading and parsing
  - Self-contained (textures embedded)
  - Better for production
- **Cons**:
  - Not human-readable
  - Requires tools to inspect/edit

**Recommendation**: Use **GLTF** during development for easy debugging, then convert to **GLB** for production deployment.

---

## Current Implementation

### Procedural Geometry (Default)

Each node type automatically uses a mathematically significant shape:

| Node Type | Geometry | Mathematical Significance |
|-----------|----------|---------------------------|
| **Observe** (D7) | Sphere | Perfect symmetry - identity element |
| **Activate** (D0) | Pyramid | Directional - entry point |
| **Integrate** (D1) | Torus | Ring - addition/integration |
| **Propagate** (D2) | Cone | Forward direction - propagation |
| **BackPropagate** (D3) | Inverted Cone | Backward flow - comparison |
| **Transform** (D4) | Octahedron | 8 faces - octonion algebra |
| **Verify** (D5) | Dodecahedron | 12 faces - verification |
| **Store** (D6) | Box | Container - storage |

### Visual Improvements

The new system provides:
- **Distinct shapes** for each operation type
- **Mathematical meaning** encoded in geometry
- **Better visual recognition** at a glance
- **Optimized performance** with proper mesh usage

---

## Using Custom GLTF/GLB Models

### Step 1: Create or Obtain Models

You can create custom models using:
- **Blender** (free, open-source)
- **Maya**
- **3ds Max**
- **SketchUp**
- **Online tools** (Sketchfab, etc.)

Export settings:
- Format: **GLTF 2.0** or **GLB**
- Include materials and textures
- Optimize geometry (use low-poly for better performance)
- Recommended poly count: **500-2000 triangles per model**

### Step 2: Place Models in Public Directory

```bash
mind-git-demo/
├── public/
│   └── models/
│       ├── observe.glb
│       ├── activate.glb
│       ├── integrate.glb
│       ├── propagate.glb
│       ├── backpropagate.glb
│       ├── transform.glb
│       ├── verify.glb
│       └── store.glb
```

### Step 3: Configure Model Paths

Edit `src/services/modelLoader.ts`:

```typescript
export const MODEL_PATHS: Record<NodeType, ModelConfig> = {
  [NodeType.Observe]: {
    path: '/models/observe.glb',
    scale: 1.0,
    useProcedural: false,  // Set to false to use custom model
  },
  // ... configure other types
};
```

### Step 4: The visualizer will automatically load your custom models!

---

## Creating Models in Blender

### Quick Tutorial

1. **Install Blender** (free from blender.org)

2. **Create Your Model**:
   ```
   - File → New → General
   - Model your shape (keep it simple, 500-2000 polys)
   - Apply materials and colors
   - UV unwrap if using textures
   ```

3. **Export as GLTF/GLB**:
   ```
   - File → Export → glTF 2.0
   - Format: GLB (for production) or GLTF Separate (for development)
   - Include: Materials, Cameras OFF, Punctual Lights OFF
   - Geometry: UVs ON, Normals ON, Vertex Colors if used
   - Click "Export glTF 2.0"
   ```

4. **Optimize** (optional):
   ```bash
   # Install gltf-pipeline
   npm install -g gltf-pipeline

   # Optimize GLB file
   gltf-pipeline -i model.glb -o model-optimized.glb -d
   ```

### Example: Creating an Octahedron for Transform Node

```blender-python
import bpy
import math

# Delete default cube
bpy.ops.object.select_all(action='SELECT')
bpy.ops.object.delete()

# Add octahedron
bpy.ops.mesh.primitive_ico_sphere_add(subdivisions=1, radius=1)

# Add material
mat = bpy.data.materials.new(name="Transform_Material")
mat.use_nodes = True
bsdf = mat.node_tree.nodes["Principled BSDF"]
bsdf.inputs['Base Color'].default_value = (0.67, 0.59, 0.85, 1.0)  # Purple
bsdf.inputs['Metallic'].default_value = 0.5
bsdf.inputs['Roughness'].default_value = 0.2

obj = bpy.context.active_object
obj.data.materials.append(mat)

# Export
bpy.ops.export_scene.gltf(
    filepath='/path/to/public/models/transform.glb',
    export_format='GLB'
)
```

---

## Advanced Usage

### Loading External GLTF Models Dynamically

```typescript
import { GLTFNode } from './components/NodeGeometry';

<GLTFNode
  modelPath="/models/custom-node.glb"
  nodeType={NodeType.Transform}
  color="#AA96DA"
  width={2}
  height={2}
  depth={0.3}
  hovered={false}
  selected={false}
/>
```

### Exporting Canvas as GLTF

You can export your entire canvas scene as a GLTF file:

```typescript
import { exportAsGLTF, exportAsGLB } from './services/modelLoader';

// Export as human-readable GLTF
const gltfJson = exportAsGLTF(sceneRef.current);
downloadFile('canvas-scene.gltf', gltfJson);

// Export as binary GLB (smaller)
const glbBuffer = exportAsGLB(sceneRef.current);
downloadBinary('canvas-scene.glb', glbBuffer);
```

### Preloading Models for Better Performance

```typescript
import { preloadModels } from './services/modelLoader';

// In your app initialization
useEffect(() => {
  preloadModels();
}, []);
```

---

## Model Requirements and Best Practices

### File Size
- **Target**: < 100 KB per model
- **Maximum**: < 500 KB per model
- **Total**: Keep all 8 models under 2 MB combined

### Geometry
- **Triangles**: 500-2000 per model
- **Vertices**: 250-1000 per model
- **No unnecessary subdivisions**
- **Merge vertices** where possible

### Materials
- Use **PBR materials** (Metallic-Roughness workflow)
- **Limit textures**: 512x512 or 1024x1024 max
- **Embed textures** in GLB for production
- **Avoid transparency** if possible (performance cost)

### Optimization
- Remove hidden faces
- Use instancing for repeated elements
- Compress textures (use PNG or JPEG in GLTF, WebP in modern browsers)
- Use **Draco compression** for GLB files

---

## Converting Between GLTF and GLB

### Using gltf-pipeline (Node.js)

```bash
# Install
npm install -g gltf-pipeline

# GLTF to GLB (compress)
gltf-pipeline -i model.gltf -o model.glb

# GLB to GLTF (extract for editing)
gltf-pipeline -i model.glb -o model.gltf

# Optimize with Draco compression
gltf-pipeline -i model.gltf -o model-draco.glb -d
```

### Using Blender

1. Import GLTF: `File → Import → glTF 2.0`
2. Export GLB: `File → Export → glTF 2.0` → Format: **GLB**

### Using Online Tools

- **glTF Viewer**: https://gltf-viewer.donmccurdy.com/
- **glTF Transform**: https://gltf-transform.donmccurdy.com/
- **Khronos glTF Validator**: https://github.khronos.org/glTF-Validator/

---

## Mathematical Model Design Guidelines

When creating custom models, consider the mathematical meaning:

### Observe (D7) - Identity Element
- Should be **symmetric** in all directions
- Consider: sphere, perfect cube, regular polyhedron
- Represents P₀ = 1 in polynomial algebra

### Activate (D0) - Entry Point
- Should point **upward** or **forward**
- Consider: arrow, pyramid, rocket
- Represents the start of computation

### Integrate (D1) - Addition
- Should suggest **combination** or **merging**
- Consider: torus, Möbius strip, interlocking shapes
- Represents XOR operation in F₂

### Propagate (D2) - Forward Shift
- Should show **directional flow**
- Consider: wave, spiral, arrow
- Represents polynomial degree shift

### BackPropagate (D3) - Comparison
- Should suggest **reflection** or **reversal**
- Consider: mirrored shapes, backward arrow
- Represents polynomial comparison

### Transform (D4) - Multiplication
- Should embody **8 dimensions**
- Consider: octahedron, octagonal prism, 8-pointed star
- Represents norm-preserving multiplication in octonions

### Verify (D5) - Consensus
- Should suggest **validation** or **checking**
- Consider: checkmark, shield, multi-faceted gem
- Represents voting mechanism

### Store (D6) - Memory
- Should suggest **containment** or **storage**
- Consider: box, vault, database cylinder
- Represents stack memory operations

---

## Example: Complete Custom Model Workflow

### 1. Design in Blender

```python
# Blender script for Transform node (octahedron)
import bpy
import math

# Clear scene
bpy.ops.object.select_all(action='SELECT')
bpy.ops.object.delete()

# Create octahedron
bpy.ops.mesh.primitive_ico_sphere_add(subdivisions=1, radius=1.0, location=(0, 0, 0))

# Set smooth shading
bpy.ops.object.shade_smooth()

# Create PBR material
mat = bpy.data.materials.new(name="OctahedronMat")
mat.use_nodes = True
nodes = mat.node_tree.nodes
bsdf = nodes["Principled BSDF"]

# Set material properties
bsdf.inputs['Base Color'].default_value = (0.67, 0.59, 0.85, 1.0)  # Purple
bsdf.inputs['Metallic'].default_value = 0.5
bsdf.inputs['Roughness'].default_value = 0.2
bsdf.inputs['Specular'].default_value = 0.5

# Apply material
obj = bpy.context.active_object
if obj.data.materials:
    obj.data.materials[0] = mat
else:
    obj.data.materials.append(mat)

# Export as GLB
bpy.ops.export_scene.gltf(
    filepath='transform.glb',
    export_format='GLB',
    export_texcoords=True,
    export_normals=True,
    export_materials='EXPORT',
    export_colors=True,
    export_cameras=False,
    export_lights=False
)
```

### 2. Optimize

```bash
# Optimize with Draco compression
gltf-pipeline -i transform.glb -o transform-optimized.glb -d

# Verify file size
ls -lh transform-optimized.glb
# Should be < 50 KB for simple geometry
```

### 3. Place in Project

```bash
cp transform-optimized.glb mind-git-demo/public/models/transform.glb
```

### 4. Configure

```typescript
// src/services/modelLoader.ts
[NodeType.Transform]: {
  path: '/models/transform.glb',
  scale: 1.0,
  rotation: [0, 0, 0],
  useProcedural: false,  // Enable custom model
},
```

### 5. Test

```bash
npm start
# Open http://localhost:3000
# Transform nodes should now use your custom octahedron model!
```

---

## Troubleshooting

### Model doesn't appear
- Check browser console for errors
- Verify file path is correct
- Ensure `useProcedural: false` in config
- Check file is accessible at `/models/yourmodel.glb`

### Model is too large/small
- Adjust `scale` in `MODEL_PATHS` config
- Recommended: 0.5 to 2.0

### Model appears black
- Ensure material has proper Base Color
- Check lighting in scene (visualizer has ambient + directional)
- Verify normals are correct (use smooth shading)

### Model has wrong orientation
- Adjust `rotation` in config (Euler angles in radians)
- Example: `rotation: [Math.PI / 2, 0, 0]` for 90° on X-axis

### Performance issues
- Reduce polygon count (target < 1000 triangles)
- Use Draco compression
- Disable unnecessary features (cameras, lights)
- Compress textures

### Model looks pixelated
- Increase texture resolution (512x512 → 1024x1024)
- Use mipmaps
- Enable anisotropic filtering in renderer

---

## Resources

### GLTF/GLB Tools
- **glTF Viewer**: https://gltf-viewer.donmccurdy.com/
- **glTF Editor**: https://gltf-transform.donmccurdy.com/
- **glTF Validator**: https://github.khronos.org/glTF-Validator/
- **glTF Pipeline**: https://github.com/CesiumGS/gltf-pipeline

### 3D Modeling Software
- **Blender** (free): https://www.blender.org/
- **SketchUp** (free): https://www.sketchup.com/
- **Autodesk Fusion 360** (free for students): https://www.autodesk.com/

### Model Libraries
- **Sketchfab**: https://sketchfab.com/ (search for CC0 models)
- **Poly Pizza**: https://poly.pizza/
- **Quaternius**: http://quaternius.com/ (free low-poly models)

### Learning Resources
- **GLTF Specification**: https://registry.khronos.org/glTF/specs/2.0/glTF-2.0.html
- **Blender GLTF Export**: https://docs.blender.org/manual/en/latest/addons/import_export/scene_gltf2.html
- **Three.js GLTF Loader**: https://threejs.org/docs/#examples/en/loaders/GLTFLoader

---

## Future Enhancements

Planned features:
- [ ] Animated GLTF models (rotation, pulsing)
- [ ] LOD (Level of Detail) for performance
- [ ] Model marketplace integration
- [ ] One-click model replacement UI
- [ ] Automatic optimization pipeline
- [ ] Model preview before applying
- [ ] Batch import/export

---

## Summary

The mind-git visualizer now supports:

✅ **8 procedural geometries** (default, mathematically meaningful)
✅ **Custom GLTF models** (for production-quality visuals)
✅ **GLB support** (optimized binary format)
✅ **Easy configuration** (just drop files and update config)
✅ **Fallback system** (procedural if GLTF fails)
✅ **Export capability** (save entire scenes as GLTF/GLB)

This gives you the flexibility to:
- Use default shapes for quick prototyping
- Create custom models for polished presentations
- Optimize with GLB for production deployment
- Share 3D canvases as standard GLTF files

**Next steps**: Try the default procedural geometries, then experiment with custom GLTF models to create your perfect spatial programming visualization!
