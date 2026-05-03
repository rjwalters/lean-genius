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

## Session 2026-05-02 (Session 3) — Matrix-vector invariant + residue monotonicity

**Mode**: REVISIT (continuing from Session 2)
**Outcome**: progress — added Steps 1 + 2a of the size-reduction
proof plan to `BinaryGcdOQ03OQ02.lean`. Still 1 placeholder
`hgcdMatrix_size_reduction` (`True`); now backed by row-convention
infrastructure that the eventual proof will consume.

### What I Did

1. Identified that the size-reduction lemma cannot be expressed
   (faithfully) using `CofactorMatrix.apply` (the column-vector
   action `M·(a,b)ᵀ`). Concrete reason: `lehmerInnerStep` updates
   the cofactor accumulator via `M' = M.mul ⟨0, 1, 1, -q⟩`
   (right-multiplication by the Euclidean step matrix). Under
   right-multiplication, the invariant that tracks the algorithm's
   actual state is the *row*-vector relation
   `(a₀, b₀) · M = (current pair)`, i.e.
   `a₀·M.α + b₀·M.γ = ahat ∧ a₀·M.β + b₀·M.δ = bhat`.
   The column action `M.apply a₀ b₀ = (M.α·a₀ + M.β·b₀, ...)` does
   not satisfy this invariant in general (it tracks a different
   intermediate state).
2. Added a new section PART V.5 to `BinaryGcdOQ03OQ02.lean`
   with the row-convention infrastructure (8 theorems, ~140 lines):
   - `lehmerInnerStep_invariant`: the row-vector relation persists
     across one inner step. Proof: unfold the `lehmerInnerStep`
     definition, eliminate the `if`s, then `linarith` using
     `Nat.div_add_mod`.
   - `lehmerCofactors_invariant`: existential multi-step version,
     by induction on `fuel` with the per-step lemma.
   - `lehmerCofactors_id_apply_eq`: specialisation to `M = id` and
     ghost pair = input pair.
   - `lehmerInnerStep_residue_le`: per-step bound. A successful
     `lehmerInnerStep` returns `(ahat', bhat')` with `bhat' < bhat`
     and `ahat' = bhat`. Proof: `omega` after splitting the `if`s.
   - `lehmerInnerStep_max_le`: corollary, `max ahat' bhat' ≤
     max ahat bhat`.
   - `lehmerCofactors_invariant_le`: strengthened multi-step
     invariant carrying the residue bound through the induction
     via transitivity.
   - `lehmerCofactors_id_apply_le`: specialisation to `M = id`.
3. Updated the file docstring + Summary to reflect the new section
   and the convention finding.
4. Build pending (Docker), see "Build status" below.

### Key Findings

- **Convention dichotomy is a real obstruction.** The `apply`
  action used by `cofactor_apply_gcd` and `hgcdMatrix_preserves_gcd`
  is the column-vector convention. For size reduction, we need the
  row-vector convention. They are not interchangeable: the row
  convention tracks `(a₀, b₀) · M = (current pair)` (preserved by
  right-multiplication, which is exactly what `lehmerInnerStep`
  does); the column convention tracks a different, less useful
  invariant. The two conventions agree on det-based theorems
  (because det doesn't care which side acts) but disagree on
  state-tracking.
- **Residue monotonicity is self-contained.** The bound
  `max ahat' bhat' ≤ max ahat bhat` follows directly from
  `Nat.mod_lt`, with no need for the matrix-vector invariant. It
  composes cleanly through `lehmerCofactors` by transitivity.
- **The remaining work is a clean entry-bound problem.** Given
  the row-vector invariant `(a₀, b₀) · M = (ahat', bhat')` and
  `det M = ±1`, Cramer's rule gives the cofactor entries as
  `M.α = ±(δ₀ · ahat' - β₀ · bhat')` etc. — but here `δ₀` and
  `β₀` are themselves matrix entries. The actual entry bound
  comes from inverting the relation: from `(a₀, b₀) · M = (ahat',
  bhat')` and unimodularity of M, `(a₀, b₀) = (ahat', bhat') ·
  M⁻¹`, which bounds M⁻¹'s entries by the original `(a₀, b₀)`
  divided by the new `(ahat', bhat')`. Composed with residue
  monotonicity (`max ahat' bhat' ≤ max ahat bhat`), this gives
  the multiplicative entry bound for M⁻¹, hence for M (whose
  entries are bounded by `det · entries(M⁻¹) = entries(M⁻¹)`).
  This is Step 2b — the next-session focus.

### Files Modified

- `proofs/Proofs/BinaryGcdOQ03OQ02.lean` — +207 lines:
  PART V.5 (8 theorems for matrix-vector invariant + residue
  monotonicity), updated file docstring, updated Summary.
  No new sorries, no new axioms.
- `research/problems/binary-gcd-oq-03-oq-02/knowledge.md` — this
  Session 3 entry.
- `research/problems/binary-gcd-oq-03-oq-02/state.md` — synced.
- `src/data/research/problems/binary-gcd-oq-03-oq-02.json` — phase
  remains ACT, knowledge updated.

### Build Status

Docker build in progress at session-end (Mathlib + new lemmas).
Each individual proof was checked tactic-by-tactic against the
identical proof from a prior commit (38b9ccfc10d, where Session 4
of an earlier branch had the same lemmas compiling); the only
adaptations made are namespace (the new file is in `HGcd`, the
prior file was in `LehmerGcd`) and references to existing
infrastructure remain identical.

### Next Steps

1. **Step 2b (next session)**: Cramer-inversion entry bound.
   From `(a₀, b₀) · M = (ahat', bhat')` and `det M = ±1`,
   invert to `(a₀, b₀) = (ahat', bhat') · M⁻¹`, where
   `M⁻¹.α = δ`, `M⁻¹.β = -β`, `M⁻¹.γ = -γ`, `M⁻¹.δ = α` (up to
   sign of det). Bound each entry of `M⁻¹` by the input pair
   divided by the residue pair; combine with `lehmerCofactors_id_apply_le`
   (residue monotonicity) for the final entry bound.
2. **Step 3**: perturbation argument bounding the difference
   between `(a, b) · M` and the truncated top-half input
   `(aHi · 2^shift, bHi · 2^shift) · M`.
3. **Step 4**: closing `hgcdMatrix_size_reduction` by composing
   the entry bound (Step 2b) with the residue bound (Step 2a) and
   the perturbation bound (Step 3).

### Honest Assessment

This session is **incremental but on the critical path**. The two
new lemma families (matrix-vector invariant + residue monotonicity)
are exactly Steps 1 and 2a of the canonical Stehlé–Zimmermann (2004)
size-reduction proof. Neither lemma is mathematically deep — both
follow from existing Mathlib by routine induction — but their
*statement* required identifying the convention obstruction, which
was non-obvious from the merged correctness layer (where everything
is column-convention and `True` placeholder hides the issue).

The phase remains ACT because `hgcdMatrix_size_reduction` is still
a placeholder. Sessions 4-5 of the prior `research/binary-gcd-hgcd-skeleton-2026-05-01`
branch (PR #14097, conflicting/draft) had the same lemmas in a
divergent file structure; this session cleanly ports them onto the
merged file.

## Session 2026-05-02 (Session 6) — Audit + Circular-Dependency Insight

**Mode**: REVISIT
**Outcome**: knowledge-sync — sessions 4-5 (Step 2b) already committed (8595544, 67e6d6c); knowledge.md was 2 sessions behind.

### What Sessions 4-5 Added (already in git)

Per commits `8595544e6b3` and `67e6d6c9833`:
- `row_vec_cramer`: from row-vec invariant + det, derives entries in terms of residues.
- `EvenPattern` / `OddPattern` defs + alternation lemmas (lehmerInnerStep flips pattern).
- `lehmerCofactors_has_pattern` / `lehmerCofactors_has_pattern_from`.
- `entry_bound_of_even` / `entry_bound_of_odd`: M entries ≤ a₀, b₀ (initial inputs).

Step 2b is complete. The file has 8 proved milestones (detailed in file Summary).

### Circular Dependency in Step 3 (Key Insight)

Step 3 requires bounding `|(a,b)·M - (aHi·2^s, bHi·2^s)·M|` where `(a,b) = (aHi·2^s + aLo, bHi·2^s + bLo)`.

Perturbation = `|aLo·M.α + bLo·M.γ|` ≤ `2^s · max_entry`.

With `entry_bound_of_even/odd`: max_entry ≤ max(a₀, b₀) ≤ 2^(N/2), so perturbation ≤ `2^(N/2) · 2^(N/2) = 2^N` — equal to the input size. NOT useful.

The TIGHT bound requires max_entry ≤ 2^(N/4) — which comes from knowing the REDUCED PAIR has N/4 bits. But that IS size reduction. This is a circular dependency.

**Resolution**: joint induction on N, proving size-of-output AND entry-bound simultaneously. This matches Stehlé-Zimmermann (2004) Theorem 1.

### Next Steps

1. **Restate `hgcdMatrix_size_reduction`** with a joint statement: `max output ≤ 2^(N/2 + c) ∧ entry_bound ≤ 2^(N/2)`. ~50 lines setup.
2. **Joint induction proof** by strong induction on `Nat.log 2 (max a b)`. ~150-200 lines.
3. This is a dedicated session of ~4-6 hours.

## Session 2026-05-03 (Session 5) — Perturbation Infrastructure (Step 3)

**Mode**: REVISIT
**Outcome**: progress (Step 3 infrastructure added)

### What I Did

- Verified that Sessions 3 and 4 work (Steps 1, 2a, 2b) is already merged into main (PRs #14522 and #14881).
- Added PART VII (~114 lines) to `BinaryGcdOQ03OQ02.lean` with 6 theorems forming the perturbation infrastructure for Step 3:

  1. `cofactor_apply_add`: `apply` distributes over addition of inputs (ring).
  2. `cofactor_apply_smul`: `apply` commutes with scalar multiplication (ring).
  3. `cofactor_apply_shift_decomp`: Decomposes `apply(aHi·2^s + ea, bHi·2^s + eb)` as `2^s · apply(aHi, bHi) + apply(ea, eb)`. This is the key algebraic identity for the perturbation argument.
  4. `cofactor_apply_natAbs_le`: Triangle bound `|M.apply(ea, eb).1| ≤ |M.α|·|ea| + |M.β|·|eb|` using `Int.natAbs_add_le` + `Int.natAbs_mul`.
  5. `cofactor_apply_err_bound`: Given `|M.α|, |M.β| ≤ C` and `|ea|, |eb| ≤ B`, then `|apply(ea, eb).1| ≤ 2·C·B`.
  6. `cofactor_apply_err_bound_snd`: Same for the second component using `|M.γ|` and `|M.δ|`.

- 0 new sorries, 0 new axioms.

### Key Findings

- Steps 1, 2a, 2b all complete in main. The size-reduction proof structure is clear:
  - `cofactor_apply_shift_decomp` gives the algebraic split: `apply(a, b) = 2^s·apply(aHi, bHi) + apply(ea, eb)`.
  - `cofactor_apply_err_bound` bounds the error term using Step 2b entry bounds.
  - The MISSING piece (Step 4) is an inductive proof that `hgcdMatrix fuel aHi bHi` reduces `max(aHi, bHi)` by half — this requires induction on bitsize and is inherently recursive.

- The PART VII placeholder `hgcdMatrix_size_reduction := True` is renamed PART VIII.

### Files Modified

- `proofs/Proofs/BinaryGcdOQ03OQ02.lean` — +124 lines (PART VII: 6 theorems + renamed PART VIII, updated Summary).

### Next Steps

1. **Step 4 (inductive)**: Prove `hgcdMatrix` reduces bitsize by half. Requires fuel-based induction with a strengthened IH tracking `Nat.log 2 (max output) ≤ Nat.log 2 (max input) / 2`. May need a `bitsize_reduction_for_lehmerCofactors` lemma first (that lehmerCofactors on (aHi, bHi) reduces max by at least 1 step).

2. **Alternative step 4**: Use the WEAK size-reduction: show that if `hgcdMatrix fuel aHi bHi` is NOT the identity, then `max(output) < max(input)`. This is weaker than "by half" but shows strict decrease, which might be enough for termination-style arguments.

## Session 2026-05-02 (Session 6) — Audit + Circular-Dependency Insight

**Mode**: REVISIT
**Outcome**: knowledge-sync — sessions 4-5 (Steps 2b) already committed; circular dependency identified in Step 3.

### Key Findings

- Step 2b is complete (commits 8595544 and 67e6d6c): `row_vec_cramer`, `EvenPattern`/`OddPattern`, `entry_bound_of_even`/`entry_bound_of_odd`.
- **Circular dependency in Step 3**: perturbation `|aLo·M.α + bLo·M.γ|` ≤ `2^s · max_entry`. With entry_bound, max_entry ≤ max(a₀, b₀) ≤ 2^(N/2), perturbation ≤ 2^N — equal to input size, useless. Tight bound requires max_entry ≤ 2^(N/4) which comes from knowing the REDUCED pair has N/4 bits — which IS size reduction. Circular.
- **Resolution**: joint induction on N, proving size-of-output AND entry-bound simultaneously, matching Stehlé-Zimmermann (2004) Theorem 1.

## Session 2026-05-03 (Session 7) — Convention Correction and Base-Case Row Bound

**Mode**: REVISIT
**Outcome**: progress — removed false `hgcdMatrix_joint_bound` column-convention theorem, proved base case of row-output bound, identified recursive-case blocker.

### Key Findings

- `hgcdMatrix_joint_bound` as previously stated (column output ≤ 2^(s+3)) was initially suspected to be false; a `native_decide` counterexample was identified but not yet added.
- The CORRECT bounded quantity for `lehmerCofactors` is the ROW output (tracked by the invariant), not the COLUMN output.
- Base case `hgcdMatrix_small_row_output_le` proved: for small inputs, `lehmerCofactors_id_apply_le` directly gives the row output ≤ max(a,b).
- Recursive case blocked: IH for M₂ applies to M₂'s intended inputs `(a/2^s, b/2^s)`, not to `rowOut(M₂, rowOut(M₁, a, b))`. Bridging requires a new invariant.

## Session 2026-05-03 (Session 8) — Counterexample Confirmed + Gallery Entry

**Mode**: REVISIT
**Outcome**: blocker documented — `hgcdMatrix_joint_bound` FALSE as stated; native_decide counterexample added; gallery entry created.

### What I Did

1. Traced through `lehmerCofactors 64 60 7 id` manually and via `native_decide`:
   - 3 steps fire (q=8 giving r=4, q=1 giving r=3, q=1 giving r=1); step 4 has r=3%1=0 → none.
   - Final M = ⟨-1, 2, 9, -17⟩.
   - Column output: M.apply(60, 7) = (-46, 421). |421| >> 64 = 2^(hgcdShift 60 7 + 3).
2. Added 3 `native_decide` examples to PART IX confirming the counterexample.
3. Rewrote PART IX docstring explaining the root cause (base case runs full Euclidean for unbalanced inputs → large column output) and what a correct theorem requires (`hgcdMatrixProper` with identity base case).
4. Updated `hgcdMatrix_joint_bound` sorry comment to say BLOCKED/false.
5. Updated Summary section.
6. Created gallery entry `src/data/proofs/binary-gcd-oq-03-oq-02/` (meta.json, annotations.json, index.ts).

### Key Findings

- **`hgcdMatrix_joint_bound` is FALSE**: the current base case runs the full Euclidean algorithm for unbalanced inputs. Column output is O(a·b/gcd²) — quadratic in the input, not bounded by 2^(n/2).
- **Counterexample**: a=60, b=7 gives M=⟨-1,2,9,-17⟩ and column output 421 > 64. Verified by native_decide.
- **What IS provable** (already proved): entries ≤ max(a,b) for base case (entry_bound_of_even/odd). GCD preservation and det ±1 are unconditional.
- **Correct fix**: define `hgcdMatrixProper` where the base case returns IDENTITY when b < 2^(hgcdShift a b) (Stehlé-Zimmermann 2004 Alg. HGCD). The joint bound then holds because the base case never accumulates large column output.

### Files Modified

- `proofs/Proofs/BinaryGcdOQ03OQ02.lean` — PART IX rewritten with counterexample + blocked sorry (~80 lines changed).
- `src/data/proofs/binary-gcd-oq-03-oq-02/` — gallery entry created (meta.json, annotations.json, index.ts).
- This knowledge.md — Sessions 6, 7, 8 added.

### Next Steps

1. **`hgcdMatrixProper` definition** (~100 lines): define a new HGCD that returns identity for b < 2^(hgcdShift a b). This is the standard Stehlé-Zimmermann structure.
2. **Joint bound for `hgcdMatrixProper`** (~300 lines): the joint induction now works cleanly since the base case contributes identity (trivially bounded). This is a separate multi-session project.
3. **Gallery entry** is live; the correctness results are published.

### Honest Assessment

This session documents a critical finding (false theorem) and adds the gallery entry for the proved correctness results. No new Lean theorems are proved. The sorry count remains 1. The value is preventing future wasted work on an unprovable theorem and making the proved results visible in the gallery.

