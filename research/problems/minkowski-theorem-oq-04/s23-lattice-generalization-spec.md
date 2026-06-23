# S23 — Lattice-generalization spec (`*_lattice` variants)

**Iteration**: S23 PREP (spec only; no Lean edits, no build attempt)
**Author**: researcher-5, 2026-05-14
**Mathlib pin**: v4.26.0 (`Mathlib.Algebra.Module.ZLattice.Basic`)
**Status**: doc-only roadmap; ready for paste-in at the next Lean-edit
iteration on this slug.

This spec parallels `minkowski-general-k-spec.md` (S18), but targets the
**single remaining S23-candidate that state.md flagged as needing "API
reconnaissance"**: lifting `blichfeldt_general` and `minkowski_general_k`
from the standard integer lattice `stdLattice n = ℤⁿ` to an arbitrary
full-rank `ℤ`-lattice `Λ ⊆ ℝⁿ` (`Λ = Submodule.span ℤ (Set.range b)` for
some `b : Module.Basis (Fin n) ℝ (Fin n → ℝ)`).

## 1. Why this scope (and why it's smaller than it looks)

The **k = 1 lattice case is already proved in this repo.** See
`proofs/Proofs/MinkowskiFundamentalTheorem.lean:661`:

```lean
theorem minkowski_general_lattice_proved
    (b : Module.Basis (Fin n) ℝ (Fin n → ℝ))
    (s : Set (Fin n → ℝ))
    (h_symm : ∀ x ∈ s, -x ∈ s)
    (h_conv : Convex ℝ s)
    (h_vol : ENNReal.ofReal |(Matrix.of b).det| * 2 ^ n < volume s) :
    ∃ x : Submodule.span ℤ (Set.range b), x ≠ 0 ∧ (x : Fin n → ℝ) ∈ s
```

That theorem already uses exactly the API needed for S23:

* `ZSpan.isAddFundamentalDomain' b volume`  (any basis → fundamental
  domain witness for the spanned `ℤ`-submodule)
* `ZSpan.volume_fundamentalDomain`  (covolume = `ENNReal.ofReal |det|`)
* `Module.finrank_fin_fun`  (rank of `Fin n → ℝ` is `n`)
* `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`  (the
  Mathlib k = 1 Minkowski statement, parameterised by a generic
  `IsAddFundamentalDomain` witness)

For the **k + 1 point multi-point form**, the Blichfeldt-side proof is the
gating step: `blichfeldt_general` (file lines 259–~380) currently uses
`stdLattice n` and `stdFundDomain n` explicitly, but every Mathlib call
inside its proof goes through the same `IsAddFundamentalDomain` /
`ZSpan` API that's already generic in the basis. So **the lattice
generalization is a mechanical parameter lift over the existing proof**:
introduce a `(b : Module.Basis (Fin n) ℝ (Fin n → ℝ))` parameter,
substitute `Submodule.span ℤ (Set.range b)` for `stdLattice n` and
`ZSpan.fundamentalDomain b` for `stdFundDomain n`, swap two
`stdLattice_*` lemmas for their `ZSpan`-named counterparts, and replace
the literal `1` covolume by `volume (ZSpan.fundamentalDomain b)` on the
volume hypothesis. The Minkowski-side `minkowski_general_k_lattice` then
specialises off `blichfeldt_general_lattice` exactly as `minkowski_general_k`
specialises off `blichfeldt_general`.

This makes the lattice generalization the **lowest-risk S23 candidate**
on state.md's list. No new tactic, no new combinatorial argument, no new
Mathlib namespace — only a parameter lift through an already-proved
proof skeleton.

## 2. Target statements

### 2.1 Primary: `blichfeldt_general_lattice` (lattice-side, multi-point)

```lean
/-- **Blichfeldt's General Theorem for an arbitrary full-rank `ℤ`-lattice**.

For any basis `b : Module.Basis (Fin n) ℝ (Fin n → ℝ)` and any
measurable set `s ⊆ ℝⁿ` with `volume s > k · volume(ZSpan.fundamentalDomain b)`,
there exist `k + 1` distinct points in `s` whose pairwise differences
lie in the `ℤ`-submodule `Submodule.span ℤ (Set.range b)`.

Specialises to `blichfeldt_general` at `b := stdBasis n` (covolume 1). -/
theorem blichfeldt_general_lattice {n : ℕ} [NeZero n]
    (b : Module.Basis (Fin n) ℝ (Fin n → ℝ))
    (k : ℕ) (s : Set (Fin n → ℝ)) (h_meas : MeasurableSet s)
    (h_vol : (k : ENNReal) * volume (ZSpan.fundamentalDomain b) < volume s) :
    ∃ pts : Fin (k+1) → Fin n → ℝ,
      Function.Injective pts ∧ (∀ i, pts i ∈ s) ∧
      ∀ i j, pts i - pts j ∈ (Submodule.span ℤ (Set.range b) : Set (Fin n → ℝ))
```

### 2.2 Primary: `minkowski_general_k_lattice` (Minkowski-side, multi-point)

```lean
/-- **Generalized Minkowski (k+1-point form) for an arbitrary full-rank `ℤ`-lattice**.

For any basis `b`, measurable convex centrally-symmetric `s ⊆ ℝⁿ` with
`volume s > k · 2ⁿ · volume(ZSpan.fundamentalDomain b)` admits `k + 1`
distinct lattice points (in `Submodule.span ℤ (Set.range b)`) lying in
`s`.

Specialises to `minkowski_general_k` at `b := stdBasis n` (covolume 1). -/
theorem minkowski_general_k_lattice {n : ℕ} [NeZero n]
    (b : Module.Basis (Fin n) ℝ (Fin n → ℝ))
    (k : ℕ) (s : Set (Fin n → ℝ))
    (h_meas : MeasurableSet s)
    (h_symm : ∀ x ∈ s, -x ∈ s)
    (h_conv : Convex ℝ s)
    (h_vol : (k : ENNReal) * (2 : ENNReal) ^ n
             * volume (ZSpan.fundamentalDomain b) < volume s) :
    ∃ pts : Fin (k + 1) → (Submodule.span ℤ (Set.range b)).toAddSubgroup,
      Function.Injective pts ∧
      (∀ i, ((pts i : Fin n → ℝ)) ∈ s)
```

### 2.3 Corollary: existing `blichfeldt_general` / `minkowski_general_k` reduce

After landing 2.1 and 2.2, the existing `blichfeldt_general` and
`minkowski_general_k` become **two-line wrappers** specialising at
`b := stdBasis n`:

```lean
theorem blichfeldt_general' {n : ℕ} [NeZero n]
    (k : ℕ) (s : Set (Fin n → ℝ)) (h_meas : MeasurableSet s)
    (h_vol : (k : ENNReal) < volume s) :
    ∃ pts : Fin (k+1) → Fin n → ℝ,
      Function.Injective pts ∧ (∀ i, pts i ∈ s) ∧
      ∀ i j, pts i - pts j ∈ (stdLattice n : Set (Fin n → ℝ)) := by
  have h := blichfeldt_general_lattice (stdBasis n) k s h_meas (by
    rw [show volume (ZSpan.fundamentalDomain (stdBasis n)) = 1 from
        stdLattice_covolume n, mul_one]; exact h_vol)
  -- ZSpan.span ℤ (Set.range (stdBasis n)) = (stdLattice n : ...) by definition
  simpa [stdLattice] using h
```

**Decision point for the implementation iteration**: whether to keep the
existing `blichfeldt_general` / `minkowski_general_k` and add the
`_lattice` versions alongside (zero churn for downstream consumers), or
to refactor — replacing the bodies of the existing theorems with the
`simpa` wrappers above and renaming the new generic forms to take the
unadorned name. The conservative choice (zero churn) is recommended for
the first lattice-generalisation PR; refactor is a follow-up scope.

## 3. Mathlib v4.26.0 API surface inventory

All citations verified by `grep -n` on the existing repo (the in-tree
`MinkowskiFundamentalTheorem.lean` already uses every API in the list
below for its k = 1 lattice generalisation).

### 3.1 `ZSpan` (in `Mathlib.Algebra.Module.ZLattice.Basic`)

* `ZSpan.fundamentalDomain : Module.Basis ι ℝ E → Set E`  — opens
  `[0,1)`-box in the chosen basis. Already used in this slug for
  `stdFundDomain` (`MinkowskiFundamentalTheorem.lean:595`).
* `ZSpan.fundamentalDomain_measurableSet`  — `MeasurableSet`-ness of the
  fundamental domain. Already used (`:600`).
* `ZSpan.isAddFundamentalDomain' : ∀ (b : Module.Basis (Fin n) ℝ (Fin n → ℝ))
    (μ : Measure (Fin n → ℝ)), IsAddFundamentalDomain
      (Submodule.span ℤ (Set.range b)).toAddSubgroup
      (ZSpan.fundamentalDomain b) μ`  — the fundamental-domain witness
  for the spanned `ℤ`-submodule. Already used (`:605`, `:672`).
* `ZSpan.volume_fundamentalDomain : volume (ZSpan.fundamentalDomain b)
    = ENNReal.ofReal |(Matrix.of b).det|`  — the covolume formula.
  Already used (`:620`, `:673`).
* `ZSpan.measure_fundamentalDomain_ne_zero : ∀ {μ}, volume
    (ZSpan.fundamentalDomain b) ≠ 0`  — supporting positivity. Already
  used (`MinkowskiFundamentalTheoremOQ04.lean:86`).

### 3.2 `MeasureTheory.IsAddFundamentalDomain` (Mathlib's lintegral/tsum API)

* `IsAddFundamentalDomain.exists_ne_zero_vadd_eq`  — the k = 1
  pigeonhole already used at `MinkowskiTheoremOQ04.lean:145`.
* `IsAddFundamentalDomain.lintegral_eq_tsum''`  — the lintegral ↔ tsum
  bridge used in `volume_eq_setLIntegral_indicator_tsum`
  (`MinkowskiTheoremOQ04.lean:202` and the proof body).
* `IsAddFundamentalDomain.measure_zero_of_invariant`  — supporting
  measurability machinery; no direct use here.

### 3.3 `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`

Statement (paraphrased; lives in `Mathlib.MeasureTheory.Group.GeometryOfNumbers`):

```lean
theorem exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {L : AddSubgroup E} [Countable L] [DiscreteTopology L]
    {F : Set E} (hF : IsAddFundamentalDomain L F μ)
    {s : Set E} (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : Convex ℝ s)
    (h_vol : μ F * 2 ^ (Module.finrank ℝ E) < μ s) :
    ∃ x : L, x ≠ 0 ∧ (x : E) ∈ s
```

Already used at `MinkowskiFundamentalTheorem.lean:670` (the lattice
form, `b`-parameterised) and at `MinkowskiTheoremOQ04.lean:382` (the
`stdLattice` specialisation). The k = 1 lattice form is therefore
**already discharged in-repo without any of S23's work**.

### 3.4 The countability instance (Mathlib)

For each application site:

```lean
haveI : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
  change Countable (Submodule.span ℤ (Set.range b)); infer_instance
```

The pattern is already used twice in this repo
(`MinkowskiFundamentalTheorem.lean:668` and the `stdLattice` variant at
`MinkowskiTheoremOQ04.lean:110, 136, 206, 661`).

## 4. Mechanical substitution table for `blichfeldt_general` → `blichfeldt_general_lattice`

The body of `blichfeldt_general` (`MinkowskiTheoremOQ04.lean:259–~380`)
requires the following uniform substitutions:

| Current (S22 source) | Lattice-generalised target | Notes |
| --- | --- | --- |
| `stdLattice n` (~25 occurrences) | `Submodule.span ℤ (Set.range b)` | Substitution is purely syntactic; rebind once at the top of the proof and reuse. |
| `stdBasis n` (1 occurrence inside `Countable` proof) | `b` | Already a parameter; remove the call to `stdBasis`. |
| `stdLattice_isAddFundamentalDomain n` | `ZSpan.isAddFundamentalDomain' b volume` | Direct rename per §3.1. |
| `stdLattice_covolume n` (gives `volume F = 1`) | `(rfl : volume (ZSpan.fundamentalDomain b) = volume (ZSpan.fundamentalDomain b))` — *not used*; instead, drop the rewrite step entirely and quote `volume (ZSpan.fundamentalDomain b)` as the covolume term. | The volume identity `volume F = 1` is the **only** place the proof relies on `stdLattice`-specific content; abstracting it leaves the rest of the proof unchanged. |
| `stdFundDomain n` (~3 occurrences) | `ZSpan.fundamentalDomain b` | Direct rename. |
| `(k : ENNReal) < volume s` hypothesis | `(k : ENNReal) * volume (ZSpan.fundamentalDomain b) < volume s` | The new hypothesis form parallels the existing k = 1 lattice form (§3.3); coincides with the old hypothesis at `stdBasis n` since covolume = 1 there. |
| `volume_eq_setLIntegral_indicator_tsum` (`:187`) | A `_lattice` version of the same identity, or the existing one specialised to `b`. | The existing `volume_eq_setLIntegral_indicator_tsum` uses `stdLattice` and `stdFundDomain` only as conveniences; the underlying Mathlib API (`IsAddFundamentalDomain.lintegral_eq_tsum''`) is already generic in the basis. **Recommended**: generalise this helper first (small PR), then use it inside `blichfeldt_general_lattice`. |

The recommended **implementation order** for the lattice generalisation
PR(s):

1. **PR-A**: Generalise `volume_eq_setLIntegral_indicator_tsum` to
   `volume_eq_setLIntegral_indicator_tsum_lattice` (or just add a
   `_lattice` version alongside). ≤ ~30 LOC.
2. **PR-B**: Add `blichfeldt_general_lattice` with the substitutions
   from §4. ≤ ~80 LOC (the bulk is the existing body of
   `blichfeldt_general`).
3. **PR-C**: Add `minkowski_general_k_lattice` as a parameter-lifted
   copy of `minkowski_general_k`. ≤ ~50 LOC.
4. **PR-D** (optional follow-up): refactor existing `blichfeldt_general`
   / `minkowski_general_k` to `simpa`-wrappers, or leave them as
   parallel direct proofs.

PR-A is the entry point that minimises mutual-rebase risk; PR-B can be
opened against the head of PR-A. PR-C is independent of A/B (depends
only on B).

## 5. Volume-hypothesis normalisation

The Minkowski-side hypothesis form has three equivalent presentations in
the existing repo; the lattice generalisation should pick one. The k = 1
lattice proof at `MinkowskiFundamentalTheorem.lean:670` uses

```lean
ENNReal.ofReal |(Matrix.of b).det| * 2 ^ n < volume s
```

i.e. the covolume appears as `ENNReal.ofReal |det|`. The k + 1 form
should use the **measure-theoretic covolume**
`volume (ZSpan.fundamentalDomain b)` directly, because `ZSpan.volume_fundamentalDomain`
gives `volume F = ENNReal.ofReal |det|` as a theorem; downstream
consumers can rewrite freely. Concretely:

```lean
-- Recommended canonical form (S23):
h_vol : (k : ENNReal) * (2 : ENNReal) ^ n
        * volume (ZSpan.fundamentalDomain b) < volume s

-- Equivalent via ZSpan.volume_fundamentalDomain:
h_vol : (k : ENNReal) * (2 : ENNReal) ^ n
        * ENNReal.ofReal |(Matrix.of b).det| < volume s
```

The first is preferred because it's the form that drops out of the
`blichfeldt_general_lattice` k + 1 hypothesis after the half-scaling
step `T = (1/2) • s`.

## 6. Anti-scope (NOT included in S23)

* `minkowski_general_k_symm` (the ±-symmetric pair form, deferred since
  Iter 18) — independent of the lattice generalisation; requires the
  sign-selection argument outlined in `minkowski-general-k-spec.md` §6.
  Cleanly orthogonal: ship S23 first, then take symm separately.
* `minkowski_five_points` (k = 4 named-points corollary) — uniform
  extrapolation of `minkowski_four_points`. Can be added on top of
  S23's lattice form or independently. ~55 LOC.
* `blichfeldt_general_pairwise_finset` / `minkowski_general_k_pairwise_finset`
  — wrapper-square closers combining pairwise (Iter 19 / Iter 22-B)
  with Finset transport (Iter 17 / Iter 20). Independent of S23.
* Build verification of the existing Iters 13–22 chain — orthogonal
  infra task gated on the `proofs/.lake` recursive self-symlink repair
  (mechanic territory).
* The Export-check section `#check` cleanup
  (`#check BlichfeldtTheorem.minkowski_general_k_pairwise` missing per
  the 2026-05-13 STATE-SYNC) — bundles into PR-B / PR-C above, not a
  solo PR.

## 7. Why this PR is doc-only

Two reasons:

1. **Build pending convention is on pause.** State.md records 9
   consecutive `(build pending)` PRs between 2026-05-08 and 2026-05-09
   (S13–S22), each gated on a single CI green pass against the
   `proofs/.lake` infra repair. Adding a 10th `(build pending)` PR
   without the infra fix in place would compound the merge-time
   risk and would not unblock anything. PR-A/-B/-C above are the
   ACT iterations; this S23 spec PR is the PREP that makes those PRs
   mechanical.
2. **The spec is the load-bearing artifact.** The S18 spec
   (`minkowski-general-k-spec.md`) was followed exactly by PR #17533
   (Iter 18 ACT). The same pattern is appropriate here: write the
   substitution table, sign off on the canonical hypothesis form,
   then a follow-up implementation iteration ships the Lean diff
   with the spec already in-tree as the reference.

## 8. Honest-status block

* **Mathematical progress in this PR**: zero. This is a PREP spec —
  bookkeeping that consolidates the lattice-generalisation roadmap
  scattered across state.md, `minkowski-general-k-spec.md`, and
  `MinkowskiFundamentalTheorem.lean:661`. No theorem in
  `proofs/Proofs/` changes; no new sorries; no axiomCount delta;
  no leanFiles delta.
* **Open conjecture status**: unchanged. The slug's status
  (`axiomatized`) and badge (`axiom`) flip to `verified` / `original`
  remains gated on Docker CI green for the post-S14 chain — orthogonal
  to S23. Adding the lattice generalisation does not advance or set
  back CI status.
* **Risk surface**: zero Lean edits, zero JSON `leanFiles` mutations,
  zero `meta.json` mutations. The state.md session-log entry adds
  ~30 LOC; the `currentState.focus` / `nextAction` refresh adds
  ~5 LOC of JSON. Total diff bounded above by the size of this
  spec (~360 LOC) + state.md (~30 LOC) + JSON (~6 LOC).
