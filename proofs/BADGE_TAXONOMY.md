# Proof Badge Taxonomy

This document defines the badge system for categorizing proofs in Lean Genius based on their relationship to Mathlib and their pedagogical purpose.

## Badge Categories

| Badge ID | Display Name | Emoji | Color | Description |
|----------|--------------|-------|-------|-------------|
| `original` | Original Proof | 🏆 | Gold (#F59E0B) | Novel formalization with minimal Mathlib delegation. The main theorem is proven from first principles or with a unique approach. |
| `mathlib` | Mathlib | 📚 | Blue (#3B82F6) | Uses Mathlib theorems for the main result. Standard approach leveraging the library. |
| `pedagogical` | Learning Example | 🎓 | Green (#10B981) | Focused on teaching Lean techniques, syntax, or proof patterns. May be simple by design. |
| `from-axioms` | From Axioms | ⚡ | Purple (#8B5CF6) | Proves from first principles with no or minimal imports. Demonstrates foundational reasoning. |
| `fallacy` | Fallacy | ⚠️ | Red (#EF4444) | Demonstrates a mathematical fallacy or invalid argument. Shows where reasoning breaks down. |
| `wip` | Work in Progress | 🚧 | Orange (#F97316) | Has `sorry` statements, incomplete sections, or relies on unproven axioms. |

## Badge Selection Criteria

### 🏆 Original Proof
Use when:
- The main theorem is NOT directly imported from Mathlib
- The proof approach is novel or differs from Mathlib's
- Minimal delegation to existing theorems

Examples: `CantorDiagonalization`, `HaltingProblem`, `InfinitudePrimes`, `PythagoreanTheorem`

### 📚 Mathlib
Use when:
- The main theorem comes from Mathlib (e.g., `Complex.exists_root`)
- The file proves corollaries or demonstrates usage
- Standard approach leveraging the Mathlib library

Examples: `FundamentalTheoremAlgebra`, `EulerIdentity`, `Sqrt2Irrational`, `AbelRuffini`

### 🎓 Learning Example
Use when:
- Primary purpose is teaching Lean syntax or concepts
- Proof complexity is intentionally low
- Demonstrates specific proof techniques or patterns

Examples: `OnePlusOne`

### ⚡ From Axioms
Use when:
- No imports or only `Tactic` imports
- Builds all definitions from scratch
- Demonstrates what Mathlib abstracts away

Examples: `HaltingProblem` (no imports), `OnePlusOne` (Peano construction)

### ⚠️ Fallacy
Use when:
- The proof intentionally demonstrates invalid reasoning
- Shows where a mathematical argument breaks down
- Educational purpose: teaching what NOT to do

Examples: `RamanujanSumFallacy` (demonstrates why 1+2+3+... ≠ -1/12 in standard analysis)

### 🚧 Work in Progress
Use when:
- File contains `sorry` statements
- Proof is incomplete or partial
- Proof relies on unproven axioms
- Under active development

Examples: `NavierStokes` (8 axioms, conditional proof)

## Metadata Schema

Each proof's `meta.json` should include badge information:

```json
{
  "meta": {
    "status": "verified",
    "tags": ["algebra", "complex-analysis"],
    "badge": "mathlib",
    "mathlibDependencies": [
      {
        "theorem": "Complex.exists_root",
        "description": "Every non-constant complex polynomial has a root",
        "module": "Mathlib.Analysis.Complex.Polynomial.Basic"
      }
    ],
    "sorries": 0,
    "originalContributions": [
      "Contrapositive formulation (no_roots_implies_constant)",
      "Complete factorization theorem (monic_prod_roots)"
    ]
  }
}
```

### Required Fields

| Field | Type | Description |
|-------|------|-------------|
| `badge` | `BadgeType` | One of the badge IDs above |
| `sorries` | `number` | Count of `sorry` statements in the Lean file |

### Optional Fields

| Field | Type | Description |
|-------|------|-------------|
| `mathlibDependencies` | `MathlibDependency[]` | Key theorems imported from Mathlib |
| `originalContributions` | `string[]` | What this proof adds beyond Mathlib |

## UI Display

Badges should be displayed:
1. **Prominently on proof cards** - Top corner or header
2. **Filterable in proof list** - Users can filter by badge type
3. **With tooltip explanation** - Hover shows badge meaning
4. **Color-coded** - Visual distinction between categories

## Philosophy

Lean Genius aims to be:

1. **Honest** - We clearly show what comes from Mathlib vs. what's original
2. **Educational** - Badges help users find proofs matching their learning goals
3. **Valuable** - We don't just wrap Mathlib; we teach how to use it effectively
4. **Transparent** - Sorries and WIP status are clearly marked, not hidden

## Examples by Badge

### 🏆 Original Proofs
- **Borsuk-Ulam Theorem** - Complete proof via covering space theory
- **Brouwer Fixed Point Theorem** - Complete proof via retraction impossibility
- **Cantor's Diagonalization** - Complete diagonal argument without Mathlib's set theory
- **Four Color Theorem** - Five color theorem proof, reducibility/unavoidability framework
- **Gödel's Incompleteness** - Complete formalization of diagonal lemma and first theorem
- **Halting Problem** - Self-contained with zero imports
- **Infinitude of Primes** - Euclid's proof using basic Mathlib

### 📚 Mathlib
- **Abel-Ruffini Theorem** - Uses `solvableByRad.isSolvable'`, demonstrates Galois theory
- **Fermat's Last Theorem** - Uses `EllipticCurve`, axiomatized Wiles proof framework
- **Fundamental Theorem of Algebra** - Uses `Complex.exists_root`, proves corollaries
- **Euler's Identity** - Uses `Complex.exp_pi_mul_I`, demonstrates special functions
- **√2 Irrational** - Uses `irrational_sqrt_two`, shows proof techniques

### 🎓 Learning Examples
- **1+1=2** - Peano arithmetic fundamentals

### ⚡ From Axioms
- **Halting Problem** - Pure logic, no imports

### ⚠️ Fallacy
- **Ramanujan Sum Fallacy** - Demonstrates where the -1/12 argument breaks down

### 🚧 Work in Progress
- **Navier-Stokes** - 8 axioms, conditional proof of millennium problem
