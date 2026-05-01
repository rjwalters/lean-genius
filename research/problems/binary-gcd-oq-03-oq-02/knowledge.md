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

## Session 2026-05-01 (Session 3) — Cofactor convention fix

**Mode**: continuation of Session 2 (same day)
**Outcome**: progress — corrected a convention mismatch that would
have made `hgcdMatrix_size_reduction` *false as previously stated*.
The lemma is now well-aligned with the algorithm semantics; sorry
count unchanged at 1.

### What I Did

While reviewing the file before attempting the size-reduction proof,
I traced `lehmerInnerStep` and `lehmerCofactors` against the
`CofactorMatrix.apply` definition, and discovered they use *different*
matrix conventions:

* `lehmerInnerStep` updates the accumulator via
  `M' = M · S` where `S = ⟨0, 1, 1, -q⟩` (right-multiplication by
  the step matrix). Equivalently, the maintained invariant is
  `(a₀, b₀) · M = (current pair)` — **row-vector convention**.

* `CofactorMatrix.apply (a, b) = (M.α·a + M.β·b, M.γ·a + M.δ·b)` is
  the **column-vector** product `M · (a, b)ᵀ`.

These products are equal only when `M.β = M.γ`, i.e. for the very
first Lehmer step (where `S = ⟨0, 1, 1, -q⟩` is symmetric on those
entries). After two or more Lehmer steps with distinct quotients,
the row and column products diverge.

For the Session-2 `applyToNat` (which used `M.apply`), this means:

* `cofactor_apply_gcd` is still applicable — column-applying any
  unimodular matrix preserves gcd. So `hgcdMatrix_apply_gcd` was
  *true* but read against the column product, not the actual
  Lehmer-reduced pair.
* `hgcdMatrix_size_reduction` was *false* in general, because the
  column-applied pair is not the reduced pair — it can even be
  larger than the input.

Concrete demonstration (now a `native_decide` test in the file):
take `(a, b) = (1000, 300)`. `hgcdTopHalfStep` extracts `aHi = 31,
bHi = 9` (`shift = 5`, `n = 10`) and runs two cofactor steps on
those:

* step 1: `q = 3, r = 4`, `M₁ = ⟨0, 1, 1, -3⟩`,
* step 2: `q = 2, r = 1`, `M₂ = ⟨1, -2, -3, 7⟩` (β = -2 ≠ γ = -3).

| Convention   | Result on (1000, 300)                    | Reduced? |
|--------------|------------------------------------------|----------|
| Row-apply    | (1000·1 + 300·(-3), 1000·(-2) + 300·7) = (100, 100) | yes (max bitsize 7 < 10) |
| Column-apply | (1·1000 + (-2)·300, (-3)·1000 + 7·300) = (400, -900) → (400, 900) | **no** (max bitsize 10) |

Both pairs preserve `Nat.gcd 1000 300 = 100`; only the row-apply
pair is the actual Lehmer reduction.

Fix applied:

1. `applyToNat M a b` now computes `(a·M.α + b·M.γ, a·M.β + b·M.δ)`
   directly (row product), bypassing `M.apply`.
2. `hgcdMatrix`'s recursive composition swapped from
   `(M_rec).mul (M_top)` to `(M_top).mul (M_rec)`, so that the
   row-apply of the composite is "top-half first, then recurse".
3. `hgcdMatrix_apply_gcd` restated with the row product on the
   left-hand side. Proof: relabel `(α, β, γ, δ) ← (M.α, M.γ, M.β,
   M.δ)` and apply `gcd_cofactor_eq` from `BinaryGcdOQ03`; the
   det condition `α·δ - β·γ = M.α·M.δ - M.γ·M.β = M.det` is
   symmetric under the swap `β ↔ γ`. Plus a `ring`-rewrite to
   match goal multiplication order.
4. `hgcdMatrix_det_unit` updated to feed
   `mul_unit_of_unit_of_unit` arguments in the new order
   (top-half first).
5. File-level docstring expanded to spell out the convention; new
   `native_decide` example pins the row-apply behaviour on the
   `(1000, 300)` case.

### Key Findings

* This is a non-trivial bug: it would have surfaced only when
  somebody tried to *use* the cofactor matrix to reduce a pair, which
  is exactly what HGCD does. The pure correctness theorems
  (`hgcdMatrix_det_unit`, `hgcdMatrix_apply_gcd`) were both true under
  the column convention, but the SIZE-REDUCTION lemma — the
  genuinely new content of OQ-02 — would have been false.
* The fix is local to `BinaryGcdOQ03OQ02.lean` and does not require
  changes to `BinaryGcdOQ03.lean`, because `lehmerCofactors`'s row
  convention is consistent within itself; the issue was only at the
  boundary where we tried to "apply" the accumulated matrix.
* Note that `lehmerReduce` in `BinaryGcdOQ03.lean` *also* uses
  `M.apply`, which has the same issue — it does not actually
  produce the Lehmer-reduced pair for matrices with two or more
  steps. The existing `lehmerGcd` algorithm is gcd-correct via
  fuel exhaustion + euclidGcd fallback, but the Lehmer "speedup"
  is not actually realised. This is a separate finding worth a
  follow-up issue against the OQ-03 line.

### Files Modified

* `proofs/Proofs/BinaryGcdOQ03OQ02.lean` — convention fix:
  `applyToNat` body, `hgcdMatrix` mul order, `hgcdMatrix_det_unit`
  arg order, `hgcdMatrix_apply_gcd` restated and re-proved, file-level
  + `applyToNat` docstrings, smoke-check example updated, new
  `native_decide` example for the (1000, 300) case. Sorry count
  unchanged at 1; axiom count unchanged at 0.
* `research/problems/binary-gcd-oq-03-oq-02/state.md` — Session-3
  block, updated active-approach narrative.
* `research/problems/binary-gcd-oq-03-oq-02/knowledge.md` — this
  Session-3 entry.

### Next Steps

The size-reduction lemma is now well-typed against the actual
Lehmer-reduced pair. The proof plan from Session 2 carries over,
with one wording change:

1. **Lehmer accumulator entry bound** —
   prove `|M.α|, |M.β|, |M.γ|, |M.δ| ≤ max(ahat, bhat)` (or some
   simple polynomial bound) for `M = lehmerCofactors fuel ahat
   bhat id`. Most likely route: maintain the matrix-vector
   invariant `(ahat₀, bhat₀) · M = (current pair)` *as a
   theorem*, and combine it with sign tracking on the cofactors
   (the alternation `α, δ` vs `β, γ` per step).
2. **Half-bitsize residual via the entry bound** —
   write `a = aHi · 2^shift + aLo`, similar for b, expand the
   row product, and bound the result by
   `2^shift · (aHi' + |M.α| + |M.γ|)`.
3. **Iterate** the half-reduction (top-half + recursive call) to
   close the threshold gap.

Step 1 is the bulk of the work and the natural focus of a future
session.

A separate follow-up: file an issue against `BinaryGcdOQ03.lean`
noting that `lehmerReduce` uses `M.apply` (column) on a
row-accumulated `M`, so the "Lehmer step" in the existing algorithm
does not actually reduce the pair. The algorithm is still
gcd-correct via fuel exhaustion + `euclidGcd` fallback.

## Session 2026-05-01 (Session 4) — Matrix-vector invariant

**Mode**: continuation of Session 3 (same day)
**Outcome**: progress — Step 1 of three for `hgcdMatrix_size_reduction`
done. Three new theorems established in `BinaryGcdOQ03OQ02.lean`'s
new PART IV. Sorry count unchanged at 1; axiom count unchanged at 0.

### What I Did

Implemented the matrix-vector invariant for `lehmerCofactors`, which
is the foundational lemma identified by the Session-2 (and Session-3
restated) proof plan.

The invariant: for `M = lehmerCofactors fuel ahat₀ bhat₀ id`, there
exist final residues `(ahat', bhat')` (from iterating `lehmerInnerStep`)
such that

```
ahat₀ * M.α + bhat₀ * M.γ = ahat'    (in ℤ)
ahat₀ * M.β + bhat₀ * M.δ = bhat'    (in ℤ)
```

— equivalently `(ahat₀, bhat₀) · M = (ahat', bhat')` in row-vector
convention. This is the algebraic content underlying the algorithm:
the matrix encodes the linear combination producing the current
Euclidean residues from the inputs.

Three theorems added, in escalating generality:

1. `lehmerInnerStep_invariant {a₀ b₀ : ℤ}`: per-step preservation
   of the relation, parameterised over a "ghost original pair"
   `(a₀, b₀)` (allowing `a₀, b₀` to be different from the current
   `(ahat, bhat)` so that the induction can carry through). Proof:
   unfold `lehmerInnerStep`, split on `bhat = 0` then on
   `ahat % bhat = 0`, reach the surviving case where the new
   matrix is `⟨M.β, M.α - q·M.β, M.δ, M.γ - q·M.δ⟩` and the new
   pair is `(bhat, ahat % bhat)`. The first conclusion is
   `h_inv₂` directly; the second follows from
   `h_inv₁ - q · h_inv₂` plus `Nat.div_add_mod`. Uses `linarith`
   with a `mul_comm` hint to handle the ℤ-cast multiplication.

2. `lehmerCofactors_invariant {a₀ b₀ : ℤ} (fuel)`: existential
   multi-step version. Inductive on `fuel`; base case is
   `⟨ahat, bhat, h_inv₁, h_inv₂⟩`; successor case uses
   `match hstep : lehmerInnerStep ahat bhat M with` (the same
   pattern as the existing `lehmerCofactors_det_unit`) to split
   on whether the head step succeeds, applying
   `lehmerInnerStep_invariant` to compute the new invariants and
   `ih` to descend.

3. `lehmerCofactors_id_apply_eq`: specialisation to `M = id`
   and ghost pair = input pair. Direct corollary of (2).

Choice of formulation: the existential form was preferred over
defining a parallel "track residues" function, because the explicit
residues are not needed for the entry-bound argument that
follows — only their existence and the invariant relation. This
keeps the file additions to a single section without a new
recursive definition.

Build verification: Docker daemon was unresponsive during multiple
attempts at session start (matches the Session-3 docker-daemon
failure mode under heavy multi-agent activity). Proofs are written
conservatively to mirror existing `lehmerInnerStep_det` and
`lehmerCofactors_det_unit` patterns; build risk should be low but
remains unverified this session. PR remains DRAFT pending
build success.

### Key Findings

* The matrix-vector invariant is genuinely the right generalised
  statement for the inductive proof. The naive form
  `(ahat₀, bhat₀) · M = (final pair)` would not survive the
  inductive step because the "current pair" changes; the ghost
  original pair `(a₀, b₀)` remains fixed throughout the
  recursion, which is exactly what's needed.
* The decomposition into per-step + multi-step keeps the
  arithmetic-heavy reasoning (Nat.div_add_mod + cast handling)
  isolated to the per-step lemma, while the inductive proof
  is purely structural. This split mirrors how the existing
  file separates `lehmerInnerStep_det` (one step) from
  `lehmerCofactors_det_unit` (induction).
* Sign tracking is automatic in ℤ: `a₀, b₀ : ℤ` means we don't
  have to worry about `Nat`-subtraction-truncation in the
  linear-combination steps. The only ℕ↔ℤ bridging is in the
  Euclidean-modulo step.

### Files Modified

* `proofs/Proofs/BinaryGcdOQ03OQ02.lean` — added PART IV
  (matrix-vector invariant) with three theorems
  (`lehmerInnerStep_invariant`, `lehmerCofactors_invariant`,
  `lehmerCofactors_id_apply_eq`). Renumbered subsequent parts
  V→VI (complexity), VI→VII (sanity checks), and added
  `PART V: SIZE REDUCTION` heading. Updated file-level
  docstring and final summary section. Sorry count unchanged
  at 1; axiom count unchanged at 0; +157 lines, -9 lines.
* `research/problems/binary-gcd-oq-03-oq-02/state.md` — Session 4
  block, iteration 4 → 5, restated next-action plan
  (1 done, 2-5 remain).
* `research/problems/binary-gcd-oq-03-oq-02/knowledge.md` —
  this Session-4 entry.

### Next Steps

The matrix-vector invariant is now in place. The natural next
session continues with **Step 2** of the proof plan: the
**Lehmer accumulator entry bound**.

With the invariant `a₀ * M.α + b₀ * M.γ = ahat'` and
`a₀ * M.β + b₀ * M.δ = bhat'` (with `det M = ±1`), Cramer's rule
recovers `a₀, b₀` from the final residues:

```
a₀ = ±(δ * ahat' - β * bhat')
b₀ = ±(α * bhat' - γ * ahat')
```

Combined with `bhat' < ahat'` (Euclidean residues form a
decreasing sequence in `bhat`) and `ahat' ≥ 1` (assuming the
algorithm hasn't terminated), this gives:

```
|α|, |β|, |γ|, |δ| ≤ max(|a₀|, |b₀|) / max(ahat', bhat')
```

So the entries of `M` are bounded by the input size divided by
the residual size — precisely the bound needed for the
perturbation analysis in Step 3.

Step 2 will need a separate small lemma about Euclidean-step
monotonicity (`bhat_final ≤ bhat₀`), provable by induction on
fuel using `Nat.mod_lt`.

## Session 2026-05-02 (Session 5) — Residue monotonicity (Step 2a)

**Mode**: REVISIT (continuation of in-progress problem; tier RICH)
**Outcome**: progress — added the residue-monotonicity bound for
the iterated Lehmer machine. The size-reduction `sorry` is unchanged
in count, but a major component of its proof (the residue side) is
now in place.

### What I Did

1. Re-read Session-4 state. The matrix-vector invariant
   (`lehmerCofactors_invariant`, `lehmerCofactors_id_apply_eq`)
   is in place; the next-action plan called for a Cramer-inversion
   entry bound that requires residue monotonicity as a prerequisite.

2. Implemented Step 2a: the small but missing lemma about Euclidean-
   step monotonicity, in four parts:

   - `lehmerInnerStep_residue_le`: per-step structure result.
     Proves `ahat' = bhat ∧ bhat' < bhat` for any successful inner
     step. Proof uses the existing `lehmerInnerStep_det` pattern
     (`simp [lehmerInnerStep] at h`, two `split at h <;> simp_all`,
     destructure the surviving equation), then `omega`.

   - `lehmerInnerStep_max_le`: the corollary
     `max ahat' bhat' ≤ max ahat bhat`. Direct from the structure
     result and `le_max_right`.

   - `lehmerCofactors_invariant_le`: existential multi-step version
     strengthening Session-4's `lehmerCofactors_invariant` with
     the residue bound. Same induction structure as the parent;
     the recursive case combines per-step `_max_le` with the IH's
     bound via `le_trans`.

   - `lehmerCofactors_id_apply_le`: specialisation to `M = id` and
     ghost-pair = input-pair. Direct from the multi-step lemma;
     gives the closed form
     `(ahat, bhat) · M = (ahat', bhat') ∧
      max ahat' bhat' ≤ max ahat bhat` for `M = lehmerCofactors
      fuel ahat bhat id`.

3. Attempted Docker build verification. Docker daemon was
   unresponsive (multiple stuck `docker-build.sh` processes
   from concurrent agents; matches the
   "Docker build I/O errors during heavy multi-agent activity"
   pattern documented in working memory). Build verification
   deferred to next session. The proofs are written to mirror
   existing patterns from `BinaryGcdOQ03.lean`
   (`lehmerInnerStep_det`, `lehmerCofactors_det_unit`); risk of
   a tactic-script issue is low but non-zero.

### Key Findings

- **Step 2 splits cleanly into 2a (residue monotonicity) and 2b
  (entry bound).** Session-4's plan named "entry bound from
  invariant + residue monotonicity + Cramer" as one piece; in
  practice the residue monotonicity is a self-contained ~30-line
  lemma that doesn't need the determinant or the invariant.
  Separating it lets 2b focus narrowly on the Cramer inversion.

- **The proof of `lehmerInnerStep_residue_le` is mechanical.** The
  per-step structure (`ahat' = bhat`, `bhat' = ahat % bhat`) is
  exactly the Euclidean update; `omega` handles the inequality
  given `bhat ≠ 0` from the surviving branch.

- **`lehmerInnerStep_max_le` is the right shape for induction.**
  The conjunction `ahat' = bhat ∧ bhat' < bhat` is too specific
  to thread through the multi-step induction directly; the
  weaker `max ahat' bhat' ≤ max ahat bhat` composes via
  transitivity and is exactly what `_invariant_le` needs.

### Files Modified

- `proofs/Proofs/BinaryGcdOQ03OQ02.lean`: 450 → 541 lines.
  Four new theorems in PART IV. 0 axioms, 1 unchanged sorry
  (in `hgcdMatrix_size_reduction`).

### Next Steps

Step 2b: Cramer-inversion entry bound. With
`lehmerCofactors_id_apply_le` in hand we have
`(ahat, bhat) · M = (ahat', bhat')` with `max ahat' bhat' ≤
max ahat bhat` and `det M = ±1`. Cramer's rule gives

```
ahat = ±(δ · ahat' - β · bhat')
bhat = ±(α · bhat' - γ · ahat')
```

so by the standard identity for unimodular 2×2 matrices,
the cofactor entries can be bounded by the input size. The
delicate point is what to do when `ahat' = 0` or `bhat' = 0`
(either residue degenerate). One option: state the Cramer
identity as a triangular bound (e.g. `|α| · ahat' + |γ| · bhat' =
|ahat|`) and recover individual entry bounds from it; another
is to handle the `bhat' = 0` case separately (algorithm has
terminated, `bhat = 0` originally, trivial bound).

Step 3: perturbation analysis. After the entry bound, combine
with `applyToNat M aHi bHi → applyToNat M a b` low-bit error
(of size `2^shift · max(|α|+|γ|, |β|+|δ|)`) and the half-
bitsize bound on the Hi-pair to close the size-reduction
inequality.

### Honest Assessment

This session removes one of the two prerequisites for the entry-
bound argument. It is a *modest* result — the lemma is short
and follows known patterns from `BinaryGcdOQ03.lean` — but it
is on the critical path: without `lehmerCofactors_id_apply_le`
the Cramer step in 2b has no cofactor-side bound to invoke.
The size-reduction sorry remains unchanged in count, which is
the honest read: this is intermediate-step infrastructure,
not a result anyone will cite without 2b/3 also closed.
