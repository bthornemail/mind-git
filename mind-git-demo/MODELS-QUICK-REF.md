# GLTF/GLB Models - Quick Reference

## Current Node Geometries

| Node Type | Default Shape | Meaning | Color |
|-----------|---------------|---------|-------|
| **Observe** | Sphere | Perfect symmetry - identity | Blue |
| **Activate** | Pyramid | Entry point - upward | Red |
| **Integrate** | Torus | Addition - ring | Teal |
| **Propagate** | Cone | Forward flow | Light Teal |
| **BackPropagate** | Inverted Cone | Backward flow | Pink |
| **Transform** | Octahedron | 8D multiplication | Purple |
| **Verify** | Dodecahedron | Verification | Light Pink |
| **Store** | Box | Storage container | Yellow |

## Quick Model Replacement

### 1. Create Model (Blender)
```
- Keep < 1000 triangles
- Export as GLB
- PBR materials only
```

### 2. Place File
```bash
cp your-model.glb public/models/transform.glb
```

### 3. Configure
```typescript
// src/services/modelLoader.ts
[NodeType.Transform]: {
  path: '/models/transform.glb',
  useProcedural: false,  // ← Change this!
}
```

### 4. Done!
Restart dev server and see your model.

## File Format Comparison

| Aspect | GLTF | GLB |
|--------|------|-----|
| Format | JSON | Binary |
| Readable | ✅ Yes | ❌ No |
| File Size | Larger | 30-50% smaller |
| Loading | Slower | Faster |
| Debugging | Easy | Hard |
| Use For | Development | Production |

## Convert GLTF ↔ GLB

```bash
# Install
npm install -g gltf-pipeline

# GLTF → GLB
gltf-pipeline -i model.gltf -o model.glb

# GLB → GLTF
gltf-pipeline -i model.glb -o model.gltf

# Optimize (Draco)
gltf-pipeline -i model.glb -o model-opt.glb -d
```

## Blender Export Settings

```
File → Export → glTF 2.0

Format: GLB ✅
Include:
  - Cameras: OFF ❌
  - Punctual Lights: OFF ❌
Mesh:
  - Apply Modifiers: ON ✅
  - UVs: ON ✅
  - Normals: ON ✅
  - Vertex Colors: ON ✅
Material:
  - Materials: Export ✅
  - Images: Automatic ✅
```

## Target Specifications

| Metric | Target | Maximum |
|--------|--------|---------|
| File Size | < 50 KB | < 500 KB |
| Triangles | 500-1000 | < 2000 |
| Texture | 512x512 | 1024x1024 |
| All Models | < 500 KB | < 2 MB |

## Troubleshooting

**Model not showing?**
- Check `useProcedural: false`
- Verify file path
- Check browser console

**Wrong size?**
- Adjust `scale: 1.0` in config

**Wrong rotation?**
- Set `rotation: [x, y, z]` (radians)

**Performance slow?**
- Reduce triangles
- Use Draco compression
- Smaller textures

## Example Blender Script

```python
import bpy

# Clear scene
bpy.ops.object.select_all(action='SELECT')
bpy.ops.object.delete()

# Add shape
bpy.ops.mesh.primitive_ico_sphere_add(subdivisions=1, radius=1)

# Material
mat = bpy.data.materials.new(name="Mat")
mat.use_nodes = True
bsdf = mat.node_tree.nodes["Principled BSDF"]
bsdf.inputs['Base Color'].default_value = (0.67, 0.59, 0.85, 1.0)
bsdf.inputs['Metallic'].default_value = 0.5
bsdf.inputs['Roughness'].default_value = 0.2

# Apply
obj = bpy.context.active_object
obj.data.materials.append(mat)

# Export
bpy.ops.export_scene.gltf(
    filepath='model.glb',
    export_format='GLB',
    export_cameras=False,
    export_lights=False
)
```

## Resources

- **GLTF Spec**: https://registry.khronos.org/glTF/
- **Viewer**: https://gltf-viewer.donmccurdy.com/
- **Blender**: https://www.blender.org/
- **Free Models**: https://poly.pizza/

---

See **GLTF-GUIDE.md** for complete documentation.
