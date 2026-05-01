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

## Session 2026-05-01 (Session 2) — HGCD skeleton compiled, det+gcd theorems proved

**Mode**: REVISIT (acted on Session-1 recommendation)
**Outcome**: progress — phase ORIENT → ACT; correctness side (A) reduced
to a single sorry (the size-reduction lemma).

### What I Did

- Made the scope decision recommended by Session 1: correctness-only.
  Documented (B) bit complexity as a Mathlib infrastructure gap and
  did not attempt it.
- Updated `problemStatement.formal` from the placeholder
  `\\text{(formal statement to be added)}` to a concrete 3-part
  spec: (A) correctness, (B) size reduction, (C) complexity (deferred).
- Updated `problemStatement.whyMatters` (was empty) and
  `knownResults.proven/open/goal` (were empty) with the classical
  references and precise sub-goals.
- Created `proofs/Proofs/BinaryGcdOQ03OQ02.lean` (~190 lines) with:
  - `hgcdThreshold`, `hgcdTopHalfStep`, `applyToNat`, `hgcdMatrix`
    (recursive HGCD with explicit fuel; two recursive calls composed
    with `CofactorMatrix.mul`).
  - `hgcdTopHalfStep_det_unit` (top-half step is unimodular).
  - `hgcdMatrix_det_unit` (recursive HGCD matrix is unimodular —
    induction on fuel; uses `CofactorMatrix.det_mul` for the
    composed branch).
  - `hgcdMatrix_apply_gcd` (application preserves `Nat.gcd` —
    immediate from the previous theorem and the existing
    `cofactor_apply_gcd` from `BinaryGcdOQ03`).
  - `bitsize` helper.
  - `hgcdMatrix_size_reduction` — **statement only, sorry**. The only
    sorry in the file. Quantitative bound is
    `bitsize(max(M·(a,b))) ≤ bitsize(max a b)/2 + (hgcdThreshold+2)`.
  - Three `example` smoke checks at the end (`det = 1` at fuel 0,
    `det = ±1` at fuel 5, `gcd` preservation at fuel 4).
- Registered the new file in `proofs/Proofs.lean`.

### Key Findings

- The det-unit and gcd-preservation halves of HGCD correctness are
  almost mechanical given the existing `CofactorMatrix` infrastructure
  in `BinaryGcdOQ03.lean`. They were proved with one induction and
  a four-way `rcases` on the determinant signs.
- The genuinely new mathematical content of OQ-02 is the
  size-reduction lemma `hgcdMatrix_size_reduction`. Closing it
  requires bounding the entries of the Lehmer cofactor accumulator
  by `2^(bitsize(max a b)/2 + 2)` — a Lehmer accumulator entry-bound
  lemma which appears not to exist either in Mathlib or in
  `BinaryGcdOQ03.lean`, and which is the natural focus of the next
  session.
- (C) bit complexity remains genuinely Mathlib-blocked; no Lean
  formulation is currently possible. Documenting this in a Part-V
  comment is itself a (small) contribution.

### Files Modified

- `proofs/Proofs/BinaryGcdOQ03OQ02.lean` (new, ~190 lines, 1 sorry, 0 axioms)
- `proofs/Proofs.lean` (added import)
- `src/data/research/problems/binary-gcd-oq-03-oq-02.json` (formal
  statement + whyMatters + knownResults populated)

### Next Steps

1. Prove `hgcdMatrix_size_reduction`. The critical lemma is an
   entry bound on `lehmerCofactors`: each entry of the accumulated
   matrix is at most `2^(fuel + 1)`. Combined with the Cramer
   inversion already used in `dvd_of_det_unit`, this gives the
   half-bitsize bound on the residual.
2. Once size reduction is established, derive a non-trivial
   termination measure (e.g. lexicographic on
   `(bitsize(max a b), fuel)`) and consider replacing the explicit
   fuel parameter with a `WellFounded.fix` definition.
3. (Optional, lower priority) wire `hgcdMatrix` into the existing
   `lehmerGcd` to give a recursive variant `hgcdGcd` and prove
   `hgcdGcd a b = Nat.gcd a b`.
