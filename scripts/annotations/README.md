# Annotation System

This directory contains the build-time annotation resolution system that keeps proof annotations aligned with Lean source code.

## The Problem

Annotations reference specific lines in Lean proofs. When the Lean source changes (lines added, removed, reordered), the line numbers in annotations become stale and point to wrong code.

## The Solution

Annotations now use **anchors** instead of line numbers. Anchors reference Lean constructs by name or content:

```json
{
  "id": "ann-main-theorem",
  "anchor": {
    "type": "declaration",
    "name": "knights_tour_oblique_min",
    "kind": "theorem"
  },
  "title": "Main Theorem",
  "content": "..."
}
```

At build time, anchors are resolved to actual line numbers.

## Anchor Types

| Type | Description | Example |
|------|-------------|---------|
| `declaration` | Theorem, lemma, def, structure, etc. | `{"type": "declaration", "name": "foo", "kind": "theorem"}` |
| `section-doc` | `/-! ... -/` module docstrings | `{"type": "section-doc", "contains": "Section 1"}` |
| `doc-comment` | `/-- ... -/` documentation | `{"type": "doc-comment", "contains": "Main result"}` |
| `block-comment` | `/- ... -/` comments | `{"type": "block-comment", "contains": "Header text"}` |
| `namespace` | Namespace declarations | `{"type": "namespace", "name": "MyProof"}` |
| `imports` | Import block | `{"type": "imports"}` |
| `pattern` | Content pattern (fallback) | `{"type": "pattern", "pattern": "theorem foo"}` |

## File Structure

For each proof:

```
src/data/proofs/{proof-name}/
├── annotations.source.json   # Source: anchors (what you edit)
├── annotations.json          # Generated: line numbers (for frontend)
├── meta.json
└── index.ts
```

## Commands

### Migrate existing line-based annotations

```bash
pnpm annotations:migrate src/data/proofs/{proof}/annotations.json proofs/Proofs/{Proof}.lean
```

This creates `annotations.source.json` with anchors. Review and commit it.

### Resolve anchors to line numbers

```bash
pnpm annotations:build
```

Runs during `pnpm build`. Resolves all anchor-based annotations.

### Validate line-based annotations (legacy)

For proofs not yet migrated, the build validates that line numbers still point to valid constructs.

```bash
pnpm annotations:validate  # Strict mode - fails on errors
```

### Parse a Lean file

See what constructs are available for anchoring:

```bash
pnpm annotations:parse proofs/Proofs/Sqrt2Irrational.lean
```

## Workflow

### Adding a new annotation

1. Run `pnpm annotations:parse proofs/Proofs/{Proof}.lean` to see available anchors
2. Add entry to `annotations.source.json` with appropriate anchor
3. Run `pnpm annotations:build` to generate line numbers

### When Lean source changes

1. The `annotations.source.json` anchors remain valid
2. Run `pnpm build` - line numbers are automatically recalculated
3. If an anchor can't be resolved (e.g., declaration renamed), build fails

### Migrating a proof

1. `pnpm annotations:migrate src/data/proofs/{proof}/annotations.json proofs/Proofs/{Proof}.lean`
2. Review `annotations.source.json` - fix any pattern-based anchors
3. Test: `pnpm annotations:build`
4. Commit both files

## Anchor Options

```typescript
interface AnnotationAnchor {
  type: AnchorType;
  name?: string;           // For declarations/namespaces
  kind?: DeclarationKind;  // For declarations
  contains?: string;       // For comments - text to match
  pattern?: string;        // For pattern anchors
  extendBefore?: number;   // Include N lines before
  extendAfter?: number;    // Include N lines after
  includeDocComment?: boolean;  // Include doc comment (default: true)
}
```

## Best Practices

1. **Prefer declaration anchors** - Most stable, based on Lean identifier names
2. **Use contains for comments** - Match unique text from the comment
3. **Avoid pattern anchors** - Use only as fallback; prone to false matches
4. **One anchor per annotation** - Don't share anchors between annotations
