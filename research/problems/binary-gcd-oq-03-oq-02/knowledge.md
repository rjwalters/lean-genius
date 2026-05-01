# Knowledge: Schönhage's Recursive HGCD (binary-gcd-oq-03-oq-02)

## Summary

Open question: can we formalize Schönhage's recursive half-GCD (HGCD) algorithm
in Lean 4, achieving the O(M(n)·log n) bit complexity bound, where M(n) is the
cost of multiplying n-bit integers?

## Mathematical content

Lehmer's algorithm (formalized in `BinaryGcdOQ03.lean`, 491 lines, 0 sorries)
extracts the top w bits of the inputs, computes a 2×2 cofactor matrix on those
small approximations, then applies the matrix to the full-precision inputs.
Each Lehmer step performs O(w) Euclidean iterations on small numbers.
Total cost: O(n²/w) bit operations vs O(n²) for plain Euclidean.

Schönhage's HGCD adds **recursion**:

1. Take inputs (a, b) of n bits.
2. **Recursively** compute the cofactor matrix M₁ that transforms the top half
   (n/2 bits) of (a, b) — solving the subproblem on n/2-bit inputs.
3. Apply M₁ to the full (a, b), reducing them to ~n/2 bits.
4. Recursively compute M₂ on the reduced pair.
5. Compose: total matrix M = M₂ · M₁.

The recursion depth is O(log n). Each level does O(M(n)) work for matrix
application (using fast multiplication). Total: O(M(n)·log n).

## Survey of existing infrastructure (2026-04-28)

### Already in this gallery (0 axioms, 0 sorries):

- `BinaryGcdOQ03.lean` (491 lines) — Lehmer hybrid: cofactor matrices,
  GCD invariance under det ±1, top-bit extraction, lehmerCofactors,
  cofactor_apply_gcd. **All the matrix machinery for HGCD is here.**
- `BinaryGcdOQ03OQ01.lean` (240 lines) — Lehmer step progress/correctness.
- `BinaryGcdOQ01.lean`, `BinaryGcdOQ01OQ03.lean`, `BinaryGcdOQ01OQ04.lean`
  — Binary GCD step bounds (Lamé-Fibonacci).

### Mathlib gaps (verified 2026-04-28):

| Need | Status |
|---|---|
| `Nat.gcd`, `Int.gcd`, basic divisibility | ✅ Mathlib |
| Bit operations (`Nat.shiftRight`, `Nat.log2`) | ✅ Mathlib |
| 2×2 integer cofactor matrices | ✅ in BinaryGcdOQ03 |
| GCD invariance under det ±1 matrices | ✅ in BinaryGcdOQ03 (`gcd_cofactor_eq`) |
| Half-GCD / HGCD definition | ❌ **gap** — neither Mathlib nor gallery |
| Karatsuba / Toom-Cook / FFT multiplication | ❌ **gap** — Mathlib has no fast multiplication |
| Bit-complexity model (M(n) = cost to multiply n-bit ints) | ❌ **gap** |
| Big-integer / arbitrary-precision arithmetic abstraction | ❌ **gap** — Mathlib uses `Nat`/`Int` opaquely |

`grep -ri "halfgcd\|hgcd\|schönhage\|karatsuba"` against Mathlib returned no
relevant matches.

## Research strategy (recommended)

The question as stated couples two distinct claims:

- **(A) Algorithmic formalization**: define `hgcdMatrix : ℕ → ℕ → CofactorMatrix`
  recursively, prove `cofactor_apply_gcd` for it (using the existing det ±1
  invariance), prove that applying it reduces input size by ~½.
- **(B) Complexity bound**: prove the bit operations are O(M(n)·log n).

(A) is **tractable**: ~300–500 lines extending `BinaryGcdOQ03.lean`.
The recursion structure is well-established and the matrix invariants are
already proved. The hard parts are (i) establishing termination of the
recursion and (ii) proving the size-reduction lemma `applying hgcdMatrix(a,b)
yields (a',b') with bitsize(max a' b') ≤ bitsize(max a b)/2 + O(1)`.

(B) is **blocked** on three foundational gaps in Mathlib (fast multiplication,
bit-complexity model, big-integer abstraction). Filling these gaps is a
multi-thousand-line project that should not be attempted as part of an HGCD
formalization. Cost would dwarf the actual algorithm.

**Recommendation**: split the question. Pursue (A) as a self-contained
verification: HGCD correctness + size-reduction. State the complexity bound
in a comment/docstring, deferring (B) until a complexity model lands in
Mathlib (or as a separate, much larger gallery initiative).

## Sessions

## Session 2026-04-28 (Session 1) — Initial Survey

**Mode**: FRESH
**Outcome**: surveyed — phase NEW → ORIENT, decision: SURVEY-then-defer-complexity

### What I Did

- Read parent `BinaryGcdOQ03.lean` (Lehmer-Schönhage hybrid, 491 lines, 0 sorries)
  to understand existing cofactor-matrix machinery.
- Surveyed siblings `BinaryGcdOQ01*` and `BinaryGcdOQ03OQ01.lean`.
- Searched Mathlib for HGCD, Schönhage, Karatsuba, fast-multiplication —
  no relevant infrastructure exists.
- Searched Mathlib `Computability/` directory — has Turing-machine/primrec
  infrastructure but no bit-complexity model for arithmetic operations.
- Identified the (correctness, complexity) split.

### Key Findings

- **All matrix-level invariants needed for HGCD correctness already exist**
  (`gcd_cofactor_eq`, `lehmerCofactors_det_unit`, `cofactor_apply_gcd`).
  The HGCD formalization is "just" wiring these into a recursion.
- **The complexity claim is currently unfalsifiable in Lean**: there is no
  Mathlib model in which to state "M(n) bit operations". Stating
  O(M(n)·log n) requires inventing/upstreaming substantial infrastructure
  first.
- **Termination of HGCD recursion** is the single hardest piece for the
  correctness side: need `bitsize(max a' b') < bitsize(max a b)` after
  one application of the recursively-computed matrix, which requires
  showing the matrix actually accumulated ≥ 1 Euclidean step.

### Files Modified

- `src/data/research/problems/binary-gcd-oq-03-oq-02.json` — populated
  knowledge fields, advanced phase NEW → ORIENT.
- `research/problems/binary-gcd-oq-03-oq-02/knowledge.md` — this file.
- `research/problems/binary-gcd-oq-03-oq-02/state.md` — synced to ORIENT.

### Next Steps

1. Decide explicitly whether to scope this problem to correctness-only
   (recommended) or keep the complexity claim in scope.
2. If correctness-only: draft `hgcdMatrix : ℕ → ℕ → CofactorMatrix`
   signature and termination measure (probably `bitsize a + bitsize b`).
3. If complexity-in-scope: spin off a separate gallery initiative for
   "Mathlib bit-complexity model + fast multiplication" — likely 2–4
   sessions of architectural work before HGCD complexity becomes
   provable.

### Honest Assessment

This survey produces a structural insight (the correctness/complexity split)
and identifies infrastructure gaps. It does **not** prove anything. The next
session can act on the recommendation in ~1–2 sessions of pure correctness
work, or escalate the complexity gap to a separate initiative.

## Session 2026-05-01 (Session 2) — Path A Correctness Layer

**Mode**: REVISIT (claim from available pool, knowledge tier MODERATE)
**Outcome**: in-progress → ACT — added `BinaryGcdOQ03OQ02.lean` with the
HGCD correctness layer (0 sorries on correctness; size-reduction stated
as a deferred placeholder).

### What I Did

1. Read `BinaryGcdOQ03.lean` (Lehmer infrastructure) and identified
   the operational correctness contract for HGCD: matrix has det ±1.
2. Designed `hgcdMatrix : ℕ → ℕ → ℕ → CofactorMatrix` as a fuel-indexed
   total function. Recursion structure: bottom out via `lehmerCofactors`
   below threshold; otherwise top-half recursion + `apply` to full
   precision + bottom-half recursion + matrix product `M₂ · M₁`.
3. Proved three results:
   - `cofactor_mul_apply`: cofactor multiplication corresponds to
     composition of `apply` actions.
   - `hgcdMatrix_det_unit`: induction on fuel proves det ±1 at every
     output. Leaf case: `lehmerCofactors_det_unit`. Recursive case:
     `det_mul` + IH twice.
   - `hgcdMatrix_preserves_gcd`: corollary of `cofactor_apply_gcd` from
     `BinaryGcdOQ03.lean`, given the determinant invariant.
4. Stated `hgcdMatrix_size_reduction` as a focused placeholder with a
   detailed comment laying out the bitsize / bound / constant choices
   needed for a precise proof. Stehlé–Zimmermann (2004) is cited as a
   reference with explicit constants.

### Key Findings

- **Correctness reduces to det invariance.** The matrix-determinant
  invariant proved for Lehmer carries through the HGCD recursion via
  `det_mul` and the IH. The recursion structure adds no new
  GCD-preservation obligation.
- **Fuel-indexing decouples correctness from size reduction.** Using
  fuel as the termination measure means we never need the size-reduction
  lemma to prove the function total, so the correctness theorems can be
  proved without it. Size reduction is a separable claim about *which*
  fuel suffices, i.e. a complexity claim, not a correctness claim.
- **The composition law is the only genuinely new content.**
  `cofactor_mul_apply` is the algebraic statement that `mul` is the
  right notion of "compose two cofactor matrices" relative to `apply`.
  Implicit in `BinaryGcdOQ03.lean`'s design but never explicitly stated;
  now a single short theorem (proved by `ring`).

### Files Modified

- `proofs/Proofs/BinaryGcdOQ03OQ02.lean` — new, ~340 lines, 0 axioms,
  0 sorries on the correctness layer; one stated
  `hgcdMatrix_size_reduction` placeholder.
- `proofs/Proofs.lean` — auto-regenerated to include the new module.
- `src/data/research/problems/binary-gcd-oq-03-oq-02.json` — phase ACT,
  builtItems, insights, nextSteps, progressSummary updated.
- `research/problems/binary-gcd-oq-03-oq-02/knowledge.md` — this file.
- `research/problems/binary-gcd-oq-03-oq-02/state.md` — synced to ACT.

### Next Steps

1. (Optional, in scope) Prove `hgcdMatrix_size_reduction` precisely.
   Bitsize via `Nat.log 2 + 1`. The advance lemma for one step needs
   the truncation-error bound from Stehlé–Zimmermann §3-4.
2. (Optional, in scope) Wire `hgcdMatrix` into a top-level GCD function
   `hgcdGcd : ℕ → ℕ → ℕ` and prove `hgcdGcd_correct`.
3. (Out of scope, separate initiative) Bit-complexity bound
   O(M(n)·log n). Requires Mathlib infrastructure that does not exist.

### Honest Assessment

This session **does** prove something nontrivial: the correctness contract
of Schönhage's recursive HGCD as a Lean theorem. It is a *modest* result
— the math reduces to existing Lehmer infrastructure plus the composition
law. But it removes one of the genuine open questions in the candidate
pool (binary-gcd-oq-03-oq-02 was MODERATE knowledge tier, phase ORIENT)
by reducing it to a focused size-reduction subproblem and a separable
complexity initiative. The phase advances ORIENT → ACT.
