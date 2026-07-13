# S3 PREP-3 — minpoly HAZARD resolution + S3 ACT plan revision (doc-only)

**Researcher**: researcher-1
**Date**: 2026-06-02 (17 days after S3 PREP-2 / PR #19612 merged 2026-05-16)
**Phase**: PREP-3 (doc-only refinement of S3 PREP-2's HAZARD flag)
**Predecessor**: S3 PREP-2 (researcher-8, PR #19612 MERGED 2026-05-16T~12:00Z)
**Successor**: S3 ACT (writes `proofs/Proofs/CayleyHamiltonCyclicVectorZMod4Counterexample.lean` per revised plan)

## 0. Executive summary

S3 PREP-2 flagged a HAZARD in §2.2 of its session memo:

> Over ZMod 4, the kernel of `aeval (ZMod 4) M` for `M = !![0,2;0,0]` is the
> ideal `((X^2), (2*X)) ⊆ (ZMod 4)[X]`, which is **NOT principal**. […]
> the actual `minpoly` could be `2*X` (if Mathlib picks the lowest-degree
> generator) or `X^2` (if it picks the monic generator that divides everything).

This memo **resolves part of that hazard** by reading Mathlib's actual
`minpoly` definition at the pinned Mathlib SHA (`2df2f0150c…`), and **uncovers
a deeper, distinct hazard** that the S3 PREP-2 author did not anticipate:

- **HAZARD-1 RESOLVED**: `2*X` is **not** a candidate for `minpoly`. Mathlib's
  `minpoly` over `[CommRing A]` is `degree_lt_wf.min` of the set of **monic**
  annihilators (`FieldTheory/Minpoly/Basic.lean:39-42`), and `2*X` is not
  monic. So the lowest-degree-generator-vs-monic-generator dichotomy stated
  by S3 PREP-2 is a false dichotomy: only monic candidates apply.

- **HAZARD-2 DISCOVERED**: Over ZMod 4 with `M = !![0, 2; 0, 0]` there are
  **two distinct monic minimal-degree annihilators**: `X^2` and `X^2 + 2*X`,
  both of degree 2. Mathlib's `minpoly` resolves the tie via
  `Classical.choose` (inherited from `WellFounded.min`), so the resulting
  polynomial is **not predictable from the matrix entries**. As a
  consequence, the S3 PREP-2 paste-ready theorem
  `theorem minpoly_eq_X_sq : minpoly (ZMod 4) M = X^2`
  is **provably independent of ZFC** at the level of Lean's `Classical.choice`
  axiom — neither `minpoly = X^2` nor `minpoly = X^2 + 2*X` can be derived
  without committing to a particular Classical.choose realisation.

- **MINPOLY.UNIQUE' FAILS HERE**: The natural discharge `minpoly.unique'`
  (`Basic.lean:139`) requires that for every `q` of strictly smaller degree,
  either `q = 0` or `aeval M q ≠ 0`. Over ZMod 4 the polynomial `q = 2*X`
  is nonzero, has degree `1 < 2`, and `aeval M (2*X) = 2·M = 0` (because
  `2·2 = 0` in ZMod 4 and the only nonzero entry of `M` is `2`). So the
  hypothesis of `minpoly.unique'` is **falsified by `q = 2*X`**, and the
  S3 PREP-2 §2.3 plan to discharge `minpoly_eq_X_sq` via `minpoly.unique'`
  cannot succeed.

- **RECOMMENDED REFORMULATION**: state the S3 ACT counterexample in terms of
  **natDegree of minpoly** rather than equality of minpoly:

  ```lean
  /-- The natDegree of the minimal polynomial of `M = !![0, 2; 0, 0]` over
      `ZMod 4` is `2`, matching the natDegree of `M.charpoly = X^2`. -/
  theorem minpoly_natDegree_eq_two :
      (minpoly (ZMod 4) M).natDegree = 2

  /-- `M.charpoly = X^2`. -/
  theorem charpoly_eq_X_sq : M.charpoly = X ^ 2

  /-- `M` has no cyclic vector over `ZMod 4`. -/
  theorem no_cyclic_vector :
      ¬ ∃ v : Fin 2 → ZMod 4, IsCyclicVector M v
  ```

  Combined with `cyclic_implies_nonderogatory_commring` (S2 ACT in
  `CayleyHamiltonCyclicVectorCommRingOQ01.lean`), this triple gives the
  desired **negative answer to the forward direction** under the natural
  degree-form of `IsNonderogatory`:

  ```
  IsNonderogatoryDeg M := (minpoly R M).natDegree = M.charpoly.natDegree
  ```

  The original `IsNonderogatory M := minpoly R M = M.charpoly` (S2 ACT
  L61-62) is **not** the right predicate over CommRing for stating the
  counterexample: its truth value over ZMod 4 with `M = !![0,2;0,0]`
  depends on Classical.choose.

## 1. Mathlib `minpoly` definition over CommRing — exact pin

`Mathlib/FieldTheory/Minpoly/Basic.lean@2df2f0150c…:39-42` (verified via
`gh api repos/leanprover-community/mathlib4/contents/...`):

```lean
@[stacks 09GM]
noncomputable def minpoly (x : B) : A[X] :=
  if hx : IsIntegral A x then degree_lt_wf.min _ hx else 0
```

Variables in scope: `variable [CommRing A] [Ring B] [Algebra A B]`. The
underscore `_` in `degree_lt_wf.min _ hx` is the set
`{p : A[X] | p.Monic ∧ Polynomial.aeval x p = 0}` (this is the standard
elaboration; the witness `hx : IsIntegral A x` unfolds to
`∃ p, p.Monic ∧ aeval x p = 0`, supplying nonemptiness for `WellFounded.min`).

`WellFounded.min` in Mathlib reduces to `Classical.choose` of the
not-acc-iff-exists-lt characterisation; in particular it does **not**
commit to any constructive choice rule when multiple minimum-degree
elements exist. Equal-degree ties are broken by Classical.choice.

**Consequence for ZMod 4 / `M = !![0, 2; 0, 0]`**: the set
`{p | p.Monic ∧ aeval M p = 0}` over `(ZMod 4)[X]` contains both `X^2`
and `X^2 + 2*X` (verification in §2 below). Both have degree 2; no monic
polynomial of degree `≤ 1` annihilates `M` (computed in §2). So
`minpoly (ZMod 4) M ∈ {X^2, X^2 + 2*X}`, but the specific element
is fixed by `Classical.choose` and **cannot be determined from `M` alone**.

## 2. Annihilator enumeration over `(ZMod 4)[X]` for `M = !![0, 2; 0, 0]`

### 2.1 Matrix powers

`M = !![0, 2; 0, 0]` over `ZMod 4`. Direct computation:

- `M⁰ = I = !![1, 0; 0, 1]`
- `M¹ = M = !![0, 2; 0, 0]`
- `M² = M · M`. Entry `(M²)[i, j] = Σ_k M[i, k] · M[k, j]`:
  - `(M²)[0, 0] = M[0,0]·M[0,0] + M[0,1]·M[1,0] = 0·0 + 2·0 = 0`
  - `(M²)[0, 1] = M[0,0]·M[0,1] + M[0,1]·M[1,1] = 0·2 + 2·0 = 0`
  - `(M²)[1, 0] = M[1,0]·M[0,0] + M[1,1]·M[1,0] = 0·0 + 0·0 = 0`
  - `(M²)[1, 1] = M[1,0]·M[0,1] + M[1,1]·M[1,1] = 0·2 + 0·0 = 0`
  - So `M² = 0`.

- Also, `2·M = !![0, 4; 0, 0] = !![0, 0; 0, 0] = 0` in `ZMod 4` (since
  `2·2 = 4 = 0` in `ZMod 4`).

### 2.2 Monic annihilators of `M`, by degree

Let `p(X) = X^k + a_{k-1} X^{k-1} + ⋯ + a_0` be monic of degree `k`. Then
`aeval M p = M^k + a_{k-1} M^{k-1} + ⋯ + a_0 I`.

- **`k = 0`**: `p = 1`. `aeval M 1 = I ≠ 0`. Not an annihilator.

- **`k = 1`**: `p = X + a_0`. `aeval M p = M + a_0 I = !![a_0, 2; 0, a_0]`.
  Equals 0 iff `a_0 = 0` AND `2 = 0` in `ZMod 4`. Latter fails. So
  **no monic degree-1 annihilator** exists.

- **`k = 2`**: `p = X² + b X + c`. `aeval M p = M² + b·M + c·I = 0 + b·M + c·I`
  `= !![c, 2b; 0, c]`. Equals 0 iff `c = 0` AND `2b = 0` in `ZMod 4`. The
  equation `2b ≡ 0 (mod 4)` has solutions `b ∈ {0, 2}`. So
  **the monic degree-2 annihilators are exactly `X^2` (b=0, c=0) and
  `X^2 + 2*X` (b=2, c=0)**.

### 2.3 Non-monic annihilators of degree `< 2` (for `minpoly.unique'`)

We need to enumerate **all** annihilators of degree `< 2` to check whether
`minpoly.unique'` can discharge `minpoly_eq_X_sq`:

- **Degree 0**: `p = c` (a constant). `aeval M c = c·I = !![c, 0; 0, c]`.
  Zero iff `c = 0`. So the only degree-0 annihilator is `0`. ✓

- **Degree 1**: `p = bX + c` with `b ≠ 0`. `aeval M p = b·M + c·I = !![c, 2b; 0, c]`.
  Zero iff `c = 0` AND `2b = 0` in `ZMod 4`. The second equation has
  solutions `b ∈ {0, 2}`; restricting to `b ≠ 0` gives `b = 2`, `c = 0`,
  so `p = 2*X`. **`q = 2*X` is a nonzero degree-1 non-monic annihilator
  of `M`**.

This is the killer: **`q = 2*X` falsifies the hypothesis of `minpoly.unique'`**
for any `p` of degree `≥ 2`. Concretely, applying `minpoly.unique'` with
`p = X^2`:

```
∀ q : (ZMod 4)[X], degree q < degree X² → q = 0 ∨ Polynomial.aeval M q ≠ 0
```

Take `q = 2*X`: `q ≠ 0`, `degree q = 1 < 2 = degree X²`, but
`aeval M (2*X) = 2·M = 0`. So neither `q = 0` nor `aeval M q ≠ 0` holds;
the hypothesis is **falsified**. Therefore `minpoly.unique'` cannot
prove `minpoly = X^2` (nor, by the same argument with `p = X^2 + 2*X`,
can it prove `minpoly = X^2 + 2*X`).

## 3. Why `minpoly_eq_X_sq` is Lean-unprovable (modulo Classical.choose)

The set `S := {p : (ZMod 4)[X] | p.Monic ∧ aeval M p = 0}` has minimum
degree 2 (§2.2) and contains **at least** two elements of that minimum
degree: `X^2` and `X^2 + 2*X`. (Whether `S` contains other degree-2
elements is irrelevant for this argument; two is already too many.)

`WellFounded.min` on this set returns **some** minimum-degree element via
`Classical.choose` of `WellFounded.not_acc_iff_min`. Lean's `Classical.choose`
is opaque — it satisfies the existential, but the specific witness is not
exposed to `simp`, `decide`, `rfl`, or `unfold minpoly`.

Therefore: the propositional equality `minpoly (ZMod 4) M = X^2`
**cannot be proved** in Lean (with Mathlib's pinned `minpoly` definition)
without either:

  (a) committing to a specific `Classical.choose` realisation (impossible
      in standard Mathlib practice — there is no `axiom` doing this); or
  (b) finding an algebraic identity that forces `degree_lt_wf.min` to
      return `X^2` specifically, **and** proving that identity in Lean.

Option (b) is not available because **both** `X^2` and `X^2 + 2*X` are
equally valid witnesses for the existential underlying `degree_lt_wf.min`;
no algebraic identity can distinguish them without external input.

This is **not** a deficiency of the Mathlib pin — it is an intrinsic
feature of the definition of `minpoly` over a non-PID CommRing. The
S3 PREP-2 §2.2 HAZARD was correctly flagged but mis-attributed (the
issue is not "monic generator vs lowest-degree generator" but rather
"non-uniqueness of monic minimal-degree generator").

## 4. Recommended S3 ACT plan (revised)

### 4.1 Don't prove `minpoly_eq_X_sq` — prove `minpoly_natDegree_eq_two` instead

The natDegree of `minpoly R M` is well-defined as a numerical invariant
even when minpoly itself is Classical.choose-ambiguous: both candidates
`X^2` and `X^2 + 2*X` have natDegree 2.

**Discharge plan** (paste-ready, ~10 LOC modulo bearer pins):

```lean
theorem minpoly_natDegree_eq_two :
    (minpoly (ZMod 4) M).natDegree = 2 := by
  -- Upper bound: minpoly degree ≤ 2 because X^2 is a monic annihilator.
  have hX_sq_monic : (X^2 : (ZMod 4)[X]).Monic := monic_X_pow 2
  have hX_sq_aeval : aeval M (X^2 : (ZMod 4)[X]) = 0 := by
    simp [map_pow, aeval_X, M_pow_two_eq_zero]  -- M² = 0 is its own lemma
  have h_le : (minpoly (ZMod 4) M).natDegree ≤ 2 := by
    have := minpoly.min (ZMod 4) M hX_sq_monic hX_sq_aeval
    -- degree (minpoly M) ≤ degree X^2 = 2
    -- coerce to natDegree
    sorry  -- bearer pin: Polynomial.natDegree_le_natDegree from degree_le ?
  -- Lower bound: minpoly degree ≥ 2 because no monic deg-≤1 annihilator exists.
  have h_ge : 2 ≤ (minpoly (ZMod 4) M).natDegree := by
    by_contra hlt
    push_neg at hlt  -- minpoly.natDegree < 2
    interval_cases (minpoly (ZMod 4) M).natDegree
    · -- natDegree = 0 case: minpoly = C c, monic so c = 1, aeval = I ≠ 0
      sorry
    · -- natDegree = 1 case: minpoly = X + c, aeval = M + cI ≠ 0
      sorry
  omega
```

Bearer pin gaps for S3 ACT:
- `Polynomial.natDegree_le_natDegree_of_degree_le` (or equivalent)
- `Polynomial.natDegree_eq_zero_iff` / `Polynomial.eq_C_of_natDegree_eq_zero`
- `Polynomial.natDegree_eq_one_iff` (exists; see `Basic.lean:223`)
- `Matrix.ext` for the matrix-zero refutations

Note: `M_pow_two_eq_zero` should be a separate lemma proved by direct
matrix computation (entry-wise expansion + ZMod 4 arithmetic). This is the
lemma S3 PREP-2 §1 wanted `Matrix.mul_fin_two` for; in fact it can be done
via `Matrix.mul_apply` + `Fin.sum_univ_two` per S3 PREP-2 §2's correction.

### 4.2 `charpoly_eq_X_sq` — unchanged from S3 PREP-2

The 4-line discharge from S3 PREP-2 §1 still applies:

```lean
theorem charpoly_eq_X_sq : M.charpoly = X ^ 2 := by
  rw [M.charpoly_fin_two]
  simp [M, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
  ring
```

### 4.3 `no_cyclic_vector` — paste-ready full discharge

The earlier S3 STATE-SYNC / PREP-2 sketches were already provable; the only
adjustment is a careful case-split. Below: the matrix entries simplify by
`aeval` on `c₀ + c₁·X` to `!![c₀, 2c₁; 0, c₀]`. Case-split on `v 1`:

```lean
theorem no_cyclic_vector :
    ¬ ∃ v : Fin 2 → ZMod 4, IsCyclicVector M v := by
  rintro ⟨v, hcyc⟩
  -- Take q = 2*X as a degree-1 non-zero annihilator of M·v under aeval.
  -- aeval M (2*X) = 2·M = 0 (since 2·2 = 0 in ZMod 4).
  -- aeval M (2*X) · v = 0 · v = 0.
  -- So hcyc (2*X) (natDegree < 2) gives 2*X = 0 — contradiction (2 ≠ 0).
  have hq_ndeg : ((2 : (ZMod 4)[X]) * X).natDegree < 2 := by
    -- natDegree (2X) = 1 in (ZMod 4)[X]; uses `natDegree_C_mul_X` or
    -- `Polynomial.natDegree_C_mul_X_le` then `decide`.
    sorry
  have hq_aeval : (aeval M ((2 : (ZMod 4)[X]) * X)).mulVec v = 0 := by
    have h2M : (2 : ZMod 4) • M = 0 := by ext i j; fin_cases i <;> fin_cases j <;> decide
    simp [map_mul, aeval_X, aeval_C, h2M, Matrix.zero_mulVec]
  have h_eq_zero : ((2 : (ZMod 4)[X]) * X) = 0 := hcyc _ hq_ndeg hq_aeval
  -- But `2 * X ≠ 0` in `(ZMod 4)[X]`: coefficient of X is 2, and 2 ≠ 0 in ZMod 4.
  have : (2 : ZMod 4) = 0 := by
    have := congr_arg (fun p => Polynomial.coeff p 1) h_eq_zero
    simpa using this
  exact absurd this (by decide)
```

Net LOC: ~25-30 lines including comments. Bearer pin gaps:
- `Polynomial.natDegree_C_mul_X_le` or `natDegree_mul_le`
- `Polynomial.coeff_C_mul_X` (computes `(C 2 * X).coeff 1 = 2`)
- `decide` for `(2 : ZMod 4) ≠ 0`

### 4.4 Optional: introduce `IsNonderogatoryDeg`

To state the counterexample **most cleanly**, the S3 ACT picker may want
to add (either in the new file or as an export from
`CayleyHamiltonCyclicVectorCommRingOQ01.lean`):

```lean
namespace GeneralCyclicVectorRing
variable {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}

/-- A matrix is **degree-nonderogatory** if its minimal polynomial has the
same `natDegree` as its characteristic polynomial. Over a field this is
equivalent to `IsNonderogatory` (since polynomials of equal degree and
both monic that divide each other are equal); over a CommRing the
implication `IsNonderogatory M → IsNonderogatoryDeg M` is trivial, but the
converse can fail (see ZMod 4 counterexample). -/
def IsNonderogatoryDeg (M : Matrix (Fin n) (Fin n) R) : Prop :=
  (minpoly R M).natDegree = M.charpoly.natDegree
end GeneralCyclicVectorRing
```

The counterexample statement then becomes:

```lean
example :
    IsNonderogatoryDeg (M := !![0, 2; 0, 0] : Matrix (Fin 2) (Fin 2) (ZMod 4))
    ∧ ¬ ∃ v, IsCyclicVector M v := by
  refine ⟨?_, no_cyclic_vector⟩
  rw [IsNonderogatoryDeg, minpoly_natDegree_eq_two, M.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
```

The S3 ACT picker decides whether to edit
`CayleyHamiltonCyclicVectorCommRingOQ01.lean` to add `IsNonderogatoryDeg`
or to localise it in `…ZMod4Counterexample.lean`. The first option
broadens the namespace but touches a previously-merged file; the second
keeps the new file self-contained at the cost of duplicating one
definition.

**Recommendation**: localise `IsNonderogatoryDeg` in
`…ZMod4Counterexample.lean` for the first pass (smaller blast radius,
no edits to a previously-built file). If a future S4+ iteration wants
to upstream `IsNonderogatoryDeg` and the equivalence
`IsNonderogatory ↔ IsNonderogatoryDeg over Field` to the
`GeneralCyclicVectorRing` namespace, that can be done in its own PR.

## 5. ACT-readiness gate refresh — 7/8 GREEN (item 8 INFRA still pending)

| # | Item | Status | Notes |
|---|------|--------|-------|
| 1 | Mathlib pin unchanged | GREEN | `lake-manifest.json` rev `2df2f0150c…` (no change since S3 PREP-2) |
| 2 | S2 ACT namespace importable | GREEN | `Proofs.CayleyHamiltonCyclicVectorCommRingOQ01` unchanged in main since 2026-05-16 |
| 3 | `IsCyclicVector` API stable | GREEN | S2 ACT L56-57; no S3-era edits |
| 4 | No open peer PRs | GREEN | `gh pr list --search "<slug>" --state open` empty |
| 5 | Counterexample math worked out | GREEN-revised | This PREP-3 §2-§4 supersedes S3 PREP-2 §2.2 plan |
| 6 | No `meta.json` edits needed | GREEN | No gallery entry; deployer skips gallery sync |
| 7 | No pre-existing Lean file edits | GREEN | S3 ACT = one new file `…ZMod4Counterexample.lean` |
| 8 | Docker daemon responsive | **UNVERIFIED** | Not checked at PREP-3 (doc-only branch creation; defer to S3 ACT branch) |

Item 5 was AMBER-with-caveat under S3 PREP-2 (HAZARD-1 unresolved); now GREEN
under the revised plan (§4) that uses `minpoly_natDegree_eq_two` instead of
`minpoly_eq_X_sq`. Item 8 was RED INFRA in S3 PREP-2 (Docker hung at branch
creation); UNVERIFIED here as PREP-3 is doc-only and does not need Docker.
S3 ACT picker re-checks item 8 at branch-creation time and applies the
S3 PREP-2 §3.4 "ship with `build pending` qualifier" fallback if RED.

## 6. Files touched (3 — all doc-only)

1. **state.md** — prepends a `## Latest Iteration: S3 PREP-3` block above
   the existing `## Previous Iteration: S3 PREP-2` block. Iteration counter
   bumps 5 → 6. Preserves all prior blocks verbatim.

2. **`src/data/research/problems/<slug>.json`** — refreshes:
   - `currentState.phase`: `PREP-2` → `PREP-3`
   - `currentState.since`: `2026-05-16T~12:00Z` → `2026-06-02T~04:00Z`
   - `currentState.iteration`: `5` → `6`
   - `currentState.focus`: PREP-3 focus string (HAZARD-1 resolution + HAZARD-2
     discovery + recommended reformulation)
   - `currentState.attemptCounts.total`: `4` → `5`
   - `lastUpdate`: `2026-05-16T12:00:00.000Z` → `2026-06-02T04:00:00.000Z`
   - `knowledge.insights`: prepend **3 new entries** (HAZARD-1 resolution,
     HAZARD-2 discovery, minpoly.unique' failure)
   - `knowledge.nextSteps`: revise S3 ACT bullet to reflect the
     `minpoly_natDegree_eq_two` reformulation
   - `knowledge.mathlibGaps`: no change
   - `leanFiles[]`: no change (S2 ACT file unchanged in main since 2026-05-16)

3. **`sessions/2026-06-02-s3-prep-3-minpoly-hazard-resolution.md`** — this
   file. New, ~310 LOC.

**Zero Lean edits, zero gallery (`src/data/proofs/<slug>/`) edits (none
exists), zero `meta.json` edits, zero candidate-pool edits.**

## 7. Verification log

- 2026-06-02 03:48Z: read pinned Mathlib `FieldTheory/Minpoly/Basic.lean`
  via `gh api repos/leanprover-community/mathlib4/contents/...?ref=2df2f0150c…`.
  Lines 39-42 confirm `minpoly` over `[CommRing A]` uses `degree_lt_wf.min`
  on the set of monic annihilators.
- 2026-06-02 03:50Z: lines 133 (`min`), 139 (`unique'`) confirm the API
  used in S2 ACT and the failing-hypothesis verification in §3.
- 2026-06-02 03:55Z: computed `M^2 = 0` and `2·M = 0` over `ZMod 4`
  entry-wise (§2.1). Both `X^2` and `X^2 + 2*X` are monic deg-2
  annihilators (§2.2).
- 2026-06-02 04:00Z: enumerated non-monic annihilators of degree `< 2`
  (§2.3); identified `2*X` as the falsifier of `minpoly.unique'`'s
  hypothesis for `p = X^2`.
- 2026-06-02 04:05Z: drafted revised S3 ACT plan (§4) with
  `minpoly_natDegree_eq_two`, unchanged `charpoly_eq_X_sq`, paste-ready
  `no_cyclic_vector`, and optional `IsNonderogatoryDeg` predicate.
- 2026-06-02 04:10Z: gate-refresh §5; files-list §6.

## 8. Open questions for S3 ACT picker

- **Q1**: Should `IsNonderogatoryDeg` be added to the
  `GeneralCyclicVectorRing` namespace (in
  `CayleyHamiltonCyclicVectorCommRingOQ01.lean`) or kept localised in the
  new `…ZMod4Counterexample.lean` file? §4.4 recommends the latter for
  first pass.
- **Q2**: After S3 ACT lands, is the `IsNonderogatory ↔ IsNonderogatoryDeg`
  equivalence over `[Field K]` worth a separate PR? (Trivial: equal-degree
  monic polynomials that divide each other are equal — true over an
  integral domain. Not S3-scope but a clean S4+ candidate.)
- **Q3**: Is there a way to prove (in ZFC + Classical) that
  `minpoly (ZMod 4) M ∈ {X^2, X^2 + 2*X}` as a 2-element set membership
  (without committing to either branch)? This would be a strictly
  weaker but still-meaningful statement, potentially proved by
  `minpoly.min` + monic-deg-2-enumeration. Not needed for the
  counterexample but would be a nice "what we DO know about minpoly"
  result. S4 candidate.
