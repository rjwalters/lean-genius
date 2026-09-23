# Annotation System

This directory contains the build-time annotation resolution system that keeps proof annotations aligned with Lean source code.

## The Problem

Annotations reference specific lines in Lean proofs. When the Lean source changes (lines added, removed, reordered), the line numbers in annotations become stale and point to wrong code.

## The Solution

Migrated annotations use **anchors** instead of line numbers. Anchors reference Lean constructs by name or content:

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

For a proof migrated to anchors:

```
src/data/proofs/{proof-name}/
├── annotations.source.json   # Source: anchors (what you edit)
├── annotations.json          # Generated: line numbers (for frontend)
└── meta.json
```

Only a small fraction of proofs have been migrated (currently ~56 of ~4,800
gallery entries have an `annotations.source.json`). The rest carry a
hand-maintained line-based `annotations.json`, which the build checks via the
legacy validation path below.

## Commands

### Migrate existing line-based annotations

```bash
pnpm annotations:migrate src/data/proofs/{proof}/annotations.json proofs/Proofs/{Proof}.lean
```

This creates `annotations.source.json` with anchors. Review and commit it.

### Re-align drifted line-based annotations

```bash
pnpm annotations:realign          # dry run: what would move, what cannot be placed
pnpm annotations:realign-apply    # write the moves in place (formatting preserved)
```

When a Lean file changes, the legacy line-based `annotations.json` ranges go
stale and `pnpm annotations:build` reports them ("No Lean construct found at
line N", type mismatches, out-of-bounds ranges). `realign-lines.ts` moves each
misaligned range back onto the construct it describes, using the same parser
and alignment rules as the validator: first by declaration name found in the
annotation's title or backticked content, then by a construct still inside the
annotation's own span, then by the nearest compatible construct within 15
lines. Multi-line annotations keep their extent; a kind-specific type that
contradicts the Lean source is corrected. Whatever it cannot place is listed
for a human. Anchor-based proofs are skipped (their `annotations.json` is
generated). Run it twice if the second dry run still reports moves: freeing a
construct can make a neighbor placeable.

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

### Normalize annotation enums

`type` and `significance` values must be members of the enums in
`src/types/proof.ts` (mirrored in `types.ts` here). `normalize-enums.ts` applies
the deterministic remediation map from issue #31246 to every `annotations.json`
in place (idempotent):

```bash
pnpm annotations:normalize          # rewrite invalid values
pnpm annotations:normalize-check    # dry run; exit 1 if any invalid value remains (CI guard)
```

### Repair anchors in source files

`fix-anchors.ts` fixes common anchor problems in `annotations.source.json`
(pattern anchors on `--` line comments, empty `doc-comment` anchors, non-matching
patterns):

```bash
npx tsx scripts/annotations/fix-anchors.ts            # apply
npx tsx scripts/annotations/fix-anchors.ts --dry-run
npx tsx scripts/annotations/fix-anchors.ts --mappings /path/to/proof_mappings.txt
```

## Files in this directory

| File | Role |
|------|------|
| `build.ts` | Build-time entry (`pnpm annotations:build` / `--strict`): resolves anchors, validates line-based files |
| `resolver.ts` | Anchor resolution; also the `migrate` / `parse` CLI behind `pnpm annotations:migrate` / `annotations:parse` |
| `lean-parser.ts` | Parses Lean files into anchorable constructs |
| `types.ts` | Annotation and anchor types (mirror of `src/types/proof.ts` enums) |
| `normalize-enums.ts` | Enum normalizer (`pnpm annotations:normalize[-check]`) |
| `fix-anchors.ts` | Anchor repair helper for `annotations.source.json` |

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
