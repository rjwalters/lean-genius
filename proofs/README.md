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
| Lean | 4.31.0 (authoritative: `proofs/lean-toolchain`) |
| Mathlib | `9a9483a929` (authoritative: `proofs/lakefile.toml`) |

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
   ./proofs/scripts/docker-build.sh Proofs.MyTheorem
   ```

   > **Never run `lake build` directly.** It can consume 100GB+ of memory in
   > seconds and crash the host. Always use the Docker wrapper. See the DANGER
   > section in the repository root `CLAUDE.md`.

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
├── lean-toolchain       # Lean 4.31.0
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
MACOSX_DEPLOYMENT_TARGET=15.0 ./proofs/scripts/docker-build.sh
```
