# LeanGenius Proofs

Lean 4 mathematical proofs with Mathlib, integrated into the LeanGenius monorepo.

## Proof Status

| Status | Description |
|--------|-------------|
| ✅ Verified | Compiles without sorry/axioms |
| ⚠️ WIP | Contains sorry or custom axioms |

### Verified Proofs
- `Sqrt2.lean` - Basic √2 properties
- `Sqrt2Irrational.lean` - √2 is irrational
- `OnePlusOne.lean` - 1 + 1 = 2
- `FundamentalTheoremCalculus.lean` - FTC
- `InfinitudePrimes.lean` - Infinitely many primes
- `CantorDiagonalization.lean` - Cantor's diagonal argument

### Work in Progress (contain sorry/axioms)
- `NavierStokes.lean` - Navier-Stokes regularity (θₖ approach)
- `AbelRuffini.lean` - Quintic unsolvability
- `GodelIncompleteness.lean` - Gödel's incompleteness
- `BrouwerFixedPoint.lean` - Brouwer fixed point
- `EulerIdentity.lean` - Euler's identity
- `FourColorTheorem.lean` - Four color theorem
- `FundamentalTheoremAlgebra.lean` - FTA
- `HaltingProblem.lean` - Halting problem
- `PythagoreanTheorem.lean` - Pythagorean theorem
- `RamanujanSumFallacy.lean` - 1+2+3+... = -1/12 fallacy

## Version Compatibility

| Component | Version |
|-----------|---------|
| Lean | 4.10.0 |
| Mathlib | `05147a76b4` (July 2024) |

## Setup

### Prerequisites

1. **Install elan** (Lean version manager):
   ```bash
   brew install elan
   ```

### Build

```bash
cd proofs
./scripts/setup.sh
```

This will:
- Download Mathlib dependencies
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
   lake build
   ```

## Extracting Goal States (LeanInk)

Use LeanInk to extract goal states for the web viewer:

```bash
./scripts/extract-proof-info.sh Proofs/Sqrt2Irrational.lean
./scripts/extract-proof-info.sh --all  # All proofs
```

Output is saved as `<filename>.leanInk` JSON files.

## Project Structure

```
proofs/
├── lakefile.toml        # Lake configuration
├── lean-toolchain       # Lean 4.10.0
├── Proofs.lean          # Main import file
├── Proofs/              # Individual proofs
│   ├── Sqrt2Irrational.lean  # ✅ Verified
│   ├── NavierStokes.lean     # ⚠️ WIP (axioms)
│   └── ...
└── scripts/
    ├── setup.sh
    └── extract-proof-info.sh
```

## Troubleshooting

### macOS Sequoia (15+) Issues

If you see `__DATA_CONST segment missing SG_READ_ONLY flag`:
```bash
MACOSX_DEPLOYMENT_TARGET=15.0 lake build
```
