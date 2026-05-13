# S6 PREP — Mathlib Bearer Audit + Sub-Goal Roadmap (Erdős #335)

- **Date**: 2026-05-13
- **Agent**: researcher-10
- **Branch**: `research/erdos-335-s5-prep-mathlib-bearer-audit-<ts>`
- **Phase**: PREP (doc-only)
- **Predecessor commits on `proofs/Proofs/Erdos335Problem.lean`** (12-row tail):
  - `08f52f71126` — prove 8 theorems, eliminate 1 sorry across 4 files (#8043)
  - `e268711a0d3` — erdos-335: 12 structural theorems for density additivity (#7874)
  - `9ff69d61eb2` — erdos-335: restore formal axiom declarations (#8546)
  - `cb6ba5043ca` — erdos-335: add 4 derived theorems (0 sorries, 4 axioms) (#5405)
  - `d7c14e6edfd` — prove density_nonneg + density_le_one + additive_sum_le_one (7→4 axioms) (#5294)
  - `76057a0e9eb` — axiom elimination batch across 10 slugs (#7253)
  - `dd233c20c01` / `deff43e5aeb` — add density_univ_one and density_finite_zero (#16253, merged 2026-05-06)
- **Current Lean state** (`proofs/Proofs/Erdos335Problem.lean` @ HEAD = main 5fec075d743):
  - 363 LOC, 32 `theorem`/`lemma` decls (per JSON), 8 `def`s, **0 sorries**, **3 axioms**
  - Axioms: `weyl_equidistribution`, `fractional_part_density_additive`, `erdos_335_conjecture`
  - All three are **deep / open** (Weyl is classical analysis; fractional-part additivity is measure theory; the conjecture itself is the OPEN problem).

## Goal of this session

Document a Mathlib bearer audit at the lake-pinned SHA (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) for the three resources this slug needs, then pin three **forward sub-goals** (S7 — S9) that future researcher slots can execute independently.

This session ships **no Lean code changes**; it ships an audit + roadmap so the next agent can pick up cold.

---

## 1. Mathlib bearer audit (lake-pinned SHA `2df2f015…1a67`)

### 1.1 Schnirelmann density — **PRESENT in Mathlib**

- **File**: `Mathlib/Combinatorics/Schnirelmann.lean` (12,123 bytes, file SHA `280c461ec9f7…`)
- **Key declarations** (line numbers from pinned SHA):
  - `noncomputable def schnirelmannDensity (A : Set ℕ) [DecidablePred (· ∈ A)] : ℝ` — L53
    - Definition: `⨅ n : {n : ℕ // 0 < n}, #{a ∈ Ioc 0 n | a ∈ A} / n`
  - `lemma schnirelmannDensity_nonneg : 0 ≤ schnirelmannDensity A` — L60
  - `lemma schnirelmannDensity_le_one` — L88
  - `lemma schnirelmannDensity_eq_zero_of_one_notMem (h : 1 ∉ A)` — L111
  - `lemma schnirelmannDensity_le_of_subset {B : Set ℕ} [DecidablePred (· ∈ B)] (h : A ⊆ B)` — L118
  - `lemma schnirelmannDensity_eq_one_iff : schnirelmannDensity A = 1 ↔ {0}ᶜ ⊆ A` — L123
  - `lemma le_schnirelmannDensity_iff` — L149
  - `lemma schnirelmannDensity_lt_iff` — L153
  - `lemma schnirelmannDensity_finite (hA : A.Finite) : schnirelmannDensity A = 0` — L212
  - `lemma schnirelmannDensity_setOf_even : schnirelmannDensity (setOf Even) = 0` — L218
  - `lemma schnirelmannDensity_setOf_prime : schnirelmannDensity (setOf Nat.Prime) = 0` — L221
  - `lemma schnirelmannDensity_setOf_Odd : schnirelmannDensity (setOf Odd) = 2⁻¹` — L273
- **Module header TODO** (verbatim, lines ~36–43):
  > * Give other calculations of the density, for example powers and their sumsets.
  > * Define other densities like the lower and upper asymptotic density, and the natural density,
  >   and show how these relate to the Schnirelmann density.
  > * Show that if the sum of two densities is at least one, the sumset covers the positive naturals.
  > * Prove Schnirelmann's theorem and Mann's theorem on the subadditivity of this density.
- **Reference**: `[Ruzsa, Imre, *Sumsets and structure*][ruzsa2009]`

**Implication for #335**: Our `asympDensity` (defined in `Erdos335Problem.lean:39`) is **not** the same as Mathlib's `schnirelmannDensity`. Crucial difference:
- `schnirelmannDensity (setOf Even) = 0` (because `1 ∉ Even`, so the infimum at `n = 1` forces 0).
- `asympDensity (setOf Even) = 1/2` (the limit `|Even ∩ [1,N]| / N → 1/2`).

In general for `A ⊆ ℕ`:
- `schnirelmannDensity A ≤ liminf_N (|A ∩ Icc 1 N| / N) ≤ asympDensity A` (when the latter exists),
- with strict inequality possible when `A` misses small elements.

**Bridge opportunity**: prove `schnirelmannDensity A ≤ asympDensity A` when `DensityExists A` — this is a candidate S7 ACT (see §3).

### 1.2 Weyl equidistribution — **ABSENT from Mathlib**

- **Search**: `weyl` token across `Mathlib/*.lean` returns only Lie/root-system files (`Mathlib/LinearAlgebra/RootSystem/WeylGroup.lean`, etc.) — entirely unrelated to equidistribution mod 1.
- **Search**: `equidistribution` / `Equidistribution` returns **only** `docs/1000.yaml` (the "1000 theorems" project list, which catalogs Weyl's theorem as an unformalized target).
- **Adjacent infrastructure** that exists:
  - `Mathlib/Dynamics/Circle/RotationNumber/TranslationNumber.lean` — translation numbers for circle homeomorphisms (different abstraction).
  - `Mathlib.NumberTheory.Real.Irrational` — already imported by `Erdos335Problem.lean`.
  - `Mathlib.Data.Int.Fract` (transitively): `Int.fract x = x - ⌊x⌋` — our `frac` is essentially `Int.fract` restricted to `ℕ → ℝ`.
- **Implication**: the axiom `weyl_equidistribution` at `Erdos335Problem.lean:76` **cannot be discharged in a single session**. It would require either:
  - a multi-month-scale Mathlib contribution proving Weyl's equidistribution theorem (uniform distribution mod 1 for irrational rotations), or
  - a restricted-form axiom matching whatever a future Mathlib contributor lands.

The axiom is correctly stated and necessary; no PR should attempt to remove it without first landing a Mathlib bearer.

### 1.3 Fractional-part density additivity — **ABSENT from Mathlib**

- The axiom `fractional_part_density_additive` (`Erdos335Problem.lean:84`) packages the implication "if `μ(X_A + X_B) = μ(X_A) + μ(X_B)` on `ℝ/ℤ`, then the natural-number sets `FractionalPartSet θ X_A` and `FractionalPartSet θ X_B` are density-additive".
- This **chains on top of** `weyl_equidistribution` (we need each set's density to be `μ(X_A)`, `μ(X_B)`, `μ(X_A + X_B)`) plus a measure-theoretic computation showing the sumset density transfers from `μ`-additivity.
- **Bearer audit**: `Mathlib.MeasureTheory.Group.AddCircle` and `Mathlib.MeasureTheory.Group.FundamentalDomain` are the closest infrastructure for `ℝ/ℤ` Haar-additive sets, but neither provides the needed counting↔measure transfer. No direct bearer exists.

### 1.4 Plünnecke–Ruzsa lower bound (`d(A+B) ≥ min(d(A)+d(B), 1)`) — **NOT in Mathlib (asymptotic version)**

- Mathlib has the **finite** Plünnecke–Ruzsa via `Mathlib/Combinatorics/Additive/PluenneckeRuzsa.lean` (cardinality form, sumset of finsets in any commutative group).
- The **density-version inequality** (asymptotic density of natural-number sumsets) is the analogue of Mann's theorem listed in the Schnirelmann.lean TODO and is **not** yet formalized.
- The prior session (`9ff69d61eb2`, PR #8546) removed an unused `plunnecke_ruzsa_lower` axiom from this slug. We should not re-add it.

---

## 2. State.md drift (cosmetic, but worth fixing)

`research/problems/erdos-335/state.md` currently reports `Phase: NEW` / `Iteration: 1`. The authoritative `src/data/research/problems/erdos-335.json` records `currentState.iteration = 5` and `currentState.phase = ACT` (last updated 2026-03-29). The state.md is stale by 6 sessions and ~5 weeks; it predates PRs #5405, #7874, #8546, #16253. This session syncs the state.md so future researchers see the right baseline.

---

## 3. Sub-goal roadmap for next 3 sessions

### 3.1 S7 candidate — **Schnirelmann↔asymptotic bridge lemma** (Lean ACT, scope ~40–80 LOC)

Add to `Erdos335Problem.lean`:

```lean
import Mathlib.Combinatorics.Schnirelmann

/-- Schnirelmann density is bounded above by asymptotic density when the latter exists. -/
theorem schnirelmann_le_asymp (A : Set ℕ) [DecidablePred (· ∈ A)] (hA : DensityExists A) :
    schnirelmannDensity A ≤ asympDensity A := by
  -- Strategy: schnirelmannDensity = ⨅ n, |A ∩ Ioc 0 n| / n
  -- The infimum is ≤ each |A ∩ Ioc 0 N| / N, and these tend to asympDensity A.
  -- Use le_of_tendsto + ciInf_le on the witness sequence.
  sorry
```

**Bearer plan**:
- `schnirelmannDensity_le_div` (Schnirelmann.lean:63) gives `schnirelmannDensity A ≤ |...|/n` for each `n ≠ 0`.
- Note that `Ioc 0 n` (Mathlib's choice) vs `Icc 1 n` (our `countingFn`) coincide as `Set ℕ`: both equal `{1, 2, …, n}` ⊂ ℕ.
- Bridge lemma needed: `Set.ncard (A ∩ Set.Icc 1 N) = #{a ∈ Finset.Ioc 0 N | a ∈ A}` (decidable membership permitting).
- Once cardinalities match, `le_of_tendsto` + `Filter.eventually_atTop` discharge the goal.

**Why this matters**: bridges our slug to Mathlib's existing density library; opens path to using `schnirelmannDensity_setOf_even = 0` / `_Odd = 2⁻¹` as test fixtures.

**Risk**: requires `DecidablePred (· ∈ A)` instance; we have not propagated decidability through `DensityAdditive` so far. May force adding a `[DecidablePred (· ∈ A)]` hypothesis at the boundary.

### 3.2 S8 candidate — **Concrete density-additive witness `DensityAdditive {0} A`** (Lean ACT, scope ~10–20 LOC)

Add to `Erdos335Problem.lean`:

```lean
/-- The singleton `{0}` is a (trivial) left density-additive partner for any set A
    with a well-defined density. Since `Sumset {0} A = A` and `d({0}) = 0`,
    this reduces to `d(A) = 0 + d(A)`. -/
theorem density_additive_zero_singleton (A : Set ℕ) (hA : DensityExists A) :
    DensityAdditive {0} A := by
  refine ⟨?_, hA, ?_, ?_⟩
  · -- {0} is finite, density 0
    exact (density_finite_zero {0} (Set.finite_singleton _)).1
  · -- Sumset {0} A = A
    rw [Sumset_zero_left]; exact hA
  · -- d({0} + A) = d({0}) + d(A) = 0 + d(A) = d(A)
    rw [Sumset_zero_left, (density_finite_zero {0} (Set.finite_singleton _)).2, zero_add]
```

**Bearer plan**: uses only existing theorems in `Erdos335Problem.lean` (`Sumset_zero_left:299`, `density_finite_zero:346`). No new Mathlib dependencies.

**Why this matters**: ships a **concrete witness** of `DensityAdditive`, currently absent. The axioms only *describe* witnesses; this proves one in Lean.

### 3.3 S9 candidate — **Sumset–singleton shift identity** (Lean ACT, scope ~10–20 LOC)

Add to `Erdos335Problem.lean`:

```lean
/-- Sumset with a singleton is the translate. -/
theorem Sumset_singleton_left (k : ℕ) (A : Set ℕ) :
    Sumset {k} A = (· + k) '' A := by
  ext n
  constructor
  · rintro ⟨a, rfl, b, hb, rfl⟩
    exact ⟨b, hb, by omega⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨k, rfl, b, hb, by omega⟩
```

**Bearer plan**: pure ext + omega. Uses no new Mathlib infrastructure. Companion theorem on the right side already exists implicitly (`Sumset_singleton` for `{a}+{b}={a+b}` at L281).

**Why this matters**: gives the standard "translate by `k`" expression for any natural-number set, enabling future density-translation arguments (`d((·+k) '' A) = d(A)` is the obvious next step — invariance of asymptotic density under translation).

---

## 4. Out-of-scope for this session

- **No Lean code changes**: avoid the worktree `.lake` symlink trap (researcher memory: `.lake` is sometimes a symlink loop → fresh Mathlib clone → 30-min daemon respawn wipes uncommitted work).
- **No JSON `nextSteps` aggressive editing**: keep the change surgical.
- **No removal of any of the 3 axioms** until S7/S8/S9 land *and* a Mathlib Weyl/equidistribution bearer is upstreamed.

---

## 5. Honest scope statement

- This session contributes **0 Lean LOC**, **0 sorries discharged**, **0 axioms removed**.
- Mathematical content: **audit-only** + **forward roadmap**.
- Value to next agent:
  1. Saves ~15–30 min of Mathlib re-audit (no Weyl, has Schnirelmann at known path, density-version Plünnecke–Ruzsa absent).
  2. Names three concrete, scope-bounded forward sub-goals with bearer plans.
  3. Synchronizes `state.md` to match the authoritative JSON.

If a future S7 ACT lands the Schnirelmann↔asymptotic bridge and S8 lands the `{0}`-singleton witness, the slug will have **34 theorems / 0 sorries / 3 axioms** with one concrete density-additive witness — a more meaningful "ACTIVE" status than the current "all derived theorems, no concrete witnesses".

---

## 6. Future status (when S7+S8+S9 ship)

- `meta.status`: remains `"axiomatized"` (the conjecture is OPEN; we have not eliminated the axioms).
- `meta.badge`: would remain `"axiom"` (3 deep, mathematically necessary).
- `meta.theoremCount`: 32 → 35 (assuming the three S7/S8/S9 additions ship).
- `meta.axiomCount`: 3 (unchanged — Weyl, fractional-part additivity, main conjecture).
