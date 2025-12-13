# Agent Guidelines for Esp32-Metatron-Merkaba

## Build/Test Commands
- **Test**: `npm test` (currently not configured)
- **Install**: `npm install`
- No TypeScript build configured yet; files are `.ts` but no `tsconfig.json` exists

## Code Style

### TypeScript/JavaScript
- **Module system**: CommonJS (`"type": "commonjs"` in package.json)
- **Imports**: Use ES6 imports (`import { X } from 'module'`)
- **Types**: Define interfaces and types explicitly; use TypeScript type annotations
- **Naming**: 
  - Functions: camelCase (`getGeometry`, `parseCanvas`, `factor`)
  - Types/Interfaces: PascalCase (`CanvasJSON`, `GroupNode`, `EdgeSide`)
  - Constants: SCREAMING_SNAKE_CASE (`TERM`, `EXPONENT`, `OPERATOR`)
- **Async**: Use `async/await` pattern, not callbacks
- **Comments**: Minimal; avoid unless explaining complex math/polynomial logic

### Codacy Integration (CRITICAL)
- **After ANY file edit**: MUST run `codacy_cli_analyze` tool immediately for edited files
- **After dependency changes**: MUST run `codacy_cli_analyze` with `tool: "trivy"` for security scan
- Do NOT add code comments unless requested
