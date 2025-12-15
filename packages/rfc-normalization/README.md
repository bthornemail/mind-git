# RFC Normalization Package

A comprehensive system for enforcing RFC-LOGOS-AST-01 constraints and normalizing metaphysical language in technical documentation.

## Features

- **RFC Constraint Checking**: Validates content against RFC-LOGOS-AST-01 rules
- **Red Flag Detection**: Identifies problematic metaphysical language patterns
- **Domain Qualifiers**: Manages domain separation with @domain tags
- **Phase Management**: Controls development phase transitions
- **Language Normalization**: Converts problematic language to technical equivalents
- **CLI Tools**: Command-line interface for validation and normalization

## Installation

```bash
npm install @mind-git/rfc-normalization
```

## Usage

### CLI

```bash
# Check RFC compliance
rfc-normalization check --pattern "**/*.md"

# Normalize files
rfc-normalization normalize --file README.md

# Generate compliance report
rfc-normalization report --output compliance-report.json

# Manage development phases
rfc-normalization phase --status
```

### Programmatic

```typescript
import { RFCNormalizer } from '@mind-git/rfc-normalization';

const normalizer = new RFCNormalizer();

// Validate content
const result = normalizer.validateContent(content);
if (!result.valid) {
  console.log('Violations:', result.violations);
}

// Normalize content
const normalized = normalizer.normalizeContent(content, {
  addDomainQualifiers: true,
  normalizeLanguage: true,
  applyStructuralFixes: true
});

// Generate compliance report
const report = normalizer.generateComplianceReport(content);
console.log(`Compliance score: ${report.score}/100`);
```

## RFC Constraints

The system enforces the following RFC-LOGOS-AST-01 constraints:

### Section 7.1: One-Step Rule
- Maximum 3 claims per explanation
- Prevents complex, multi-layered assertions

### Section 7.3: Connection Limit  
- Maximum 5 connected concepts
- Prevents exponential thinking patterns

### Section 4.1: Domain Separation
- Requires @domain qualifiers for mixed-domain content
- Supported domains: DIGITAL, MATHEMATICAL, METAPHORICAL, ORGANIZATIONAL, TECHNICAL

### Section 11: Urgency Tone
- Detects time-pressured language
- Prevents manipulation through urgency

### Section 10: Compiler Engineer Test
- Ensures language is understandable to compiler engineers
- Replaces metaphysical terms with technical equivalents

## Red Flag Detection

The system detects and flags:

- **Apocalyptic Language**: References to judgment day, new jerusalem, etc.
- **Metaphysical Inflation**: Claims of divine authority or reality control
- **Dimensional Claims**: References to inhabiting other realities
- **Consciousness Manipulation**: Claims about consciousness merging/evolution
- **Mathematical Determinism**: Claims that math is absolute truth
- **Urgency Tactics**: Time-pressured language

## Language Normalization

Automatic replacements for problematic terms:

| Original | Replacement |
|----------|-------------|
| reality admin | system administration |
| consciousness merging | data federation |
| dimensional shifting | coordinate transformation |
| truth detection | consistency checking |
| sacred geometry | spatial algebra |
| judgment day | system validation |
| new jerusalem | distributed system architecture |
| wedding feast | system integration |

## Phase Management

Controls development phase transitions:

- **Validation** → **Testing** → **Documentation** → **Production**
- Each phase has completion requirements
- Prevents skipping phases or premature transitions

## API Reference

### RFCNormalizer

Main class for content normalization and validation.

#### Methods

- `validateContent(content: string): CheckResult`
- `normalizeContent(content: string, options?: NormalizeOptions): NormalizeResult`
- `generateComplianceReport(content: string): ComplianceReport`

### ConstraintChecker

Validates content against RFC constraints.

#### Methods

- `checkDocument(content: string): CheckResult`

### RedFlagDetector

Detects problematic language patterns.

#### Methods

- `detectRedFlags(content: string): RedFlagReport`
- `generateFixes(violations: Violation[]): FixSuggestion[]`
- `requiresHumanIntervention(report: RedFlagReport): Promise<boolean>`

### DomainQualifierSystem

Manages domain qualifiers and separation.

#### Methods

- `checkDomainQualifiers(content: string): Violation[]`
- `addDomainQualifier(content: string, domain: string): string`
- `generateDomainReport(content: string): DomainReport`

### PhaseManager

Manages development phase transitions.

#### Methods

- `getCurrentPhase(): Phase`
- `canTransition(to: Phase): Promise<TransitionResult>`
- `transitionTo(to: Phase, reason: string): Promise<TransitionResult>`

## Development

```bash
# Install dependencies
npm install

# Run tests
npm test

# Build
npm build

# Run CLI
npm run check
npm run normalize
```

## License

MIT