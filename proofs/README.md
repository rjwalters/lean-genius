# LeanGenius Proofs

Lean 4 mathematical proofs with Mathlib, designed for use with [LeanGenius](https://github.com/rjwalters/lean-genius) proof viewer.

## Version Compatibility

This project uses pinned versions for LeanInk compatibility:

| Component | Version |
|-----------|---------|
| Lean | 4.10.0 |
| Mathlib | `05147a76b4` (July 2024) |
| LeanInk | Built from source |

## Setup

### Prerequisites

1. **Install elan** (Lean version manager):
   ```bash
   brew install elan
   ```

2. **Build LeanInk** (one-time setup):
   ```bash
   cd ~/Projects
   git clone https://github.com/leanprover/LeanInk
   cd LeanInk
   echo "leanprover/lean4:v4.10.0" > lean-toolchain
   MACOSX_DEPLOYMENT_TARGET=15.0 lake build
   ```

### Project Setup

```bash
./scripts/setup.sh
```

This will:
- Download Mathlib dependencies
- Build the cache tool (macOS 26 compatibility)
- Download prebuilt Mathlib cache
- Build all proofs

## Adding New Proofs

1. Create a new `.lean` file in `Proofs/`:
   ```lean
   -- Proofs/MyTheorem.lean
   import Mathlib.Tactic

   theorem my_theorem : P := by
     sorry
   ```

2. Add import to `Proofs.lean`:
   ```lean
   import Proofs.MyTheorem
   ```

3. Build:
   ```bash
   MACOSX_DEPLOYMENT_TARGET=15.0 lake build
   ```

## Extracting Goal States

Use LeanInk to extract goal states and type information:

```bash
# Single file
./scripts/extract-proof-info.sh Proofs/Sqrt2Irrational.lean

# All proofs
./scripts/extract-proof-info.sh --all
```

Output is saved as `<filename>.leanInk` JSON files.

## LeanInk Output Format

The `.leanInk` JSON contains:

```json
[
  {
    "_type": "sentence",
    "goals": [{
      "hypotheses": [{"names": ["n"], "type": "ℤ"}],
      "conclusion": "0 ≤ n²"
    }],
    "contents": [{"raw": "by_cases h : 0 ≤ n", "typeinfo": {...}}]
  }
]
```

## Project Structure

```
lean-genius-proofs/
├── lakefile.toml        # Lake configuration (pinned Mathlib)
├── lean-toolchain       # Lean 4.10.0
├── Proofs.lean          # Main import file
├── Proofs/
│   ├── Sqrt2.lean       # Basic proofs
│   └── Sqrt2Irrational.lean  # √2 irrationality
└── scripts/
    ├── setup.sh         # Initial setup
    └── extract-proof-info.sh  # LeanInk extraction
```

## Troubleshooting

### macOS 26 (Tahoe) Issues

If you see `__DATA_CONST segment missing SG_READ_ONLY flag`:
- Always use `MACOSX_DEPLOYMENT_TARGET=15.0` when building
- This affects Lean binaries built for older macOS versions

### Mathlib API Changes

This project uses an older Mathlib version. Some APIs may differ from current Mathlib:
- Check `Mathlib.Algebra.Ring.Parity` for Even/Odd
- Check `Mathlib.Algebra.Ring.Int` for Int-specific lemmas
