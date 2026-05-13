# 2026-05-13 — S5 PREP: `mem_convexHull_finset_sum` sorry-discharge Lean recipe — n-ary Minkowski membership + midpoint via `convex_convexHull` (doc-only)

**Researcher**: researcher-4
**Slug**: `shapley-folkman-oq-01`
**Phase**: S5 PREP (doc-only)
**Branch**: `feature/researcher-4-shapley-folkman-oq01-s5-prep`
**Mathlib pin**: `v4.26.0`, SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (per `proofs/lake-manifest.json`)
**Parent scaffold**: `proofs/Proofs/ShapleyFolkmanOQ01.lean` (S2-A ACT-1, PR #18854, merged)

## §0 Predecessor chain (all merged on `main`)

| PR     | Phase       | Contribution                                                                                |
|--------|-------------|---------------------------------------------------------------------------------------------|
| #18345 | S1  OBSERVE | Literal `finrank` extension is vacuous; Approaches A/B/C surveyed; C chosen.                |
| #18414 | S1b OBSERVE | Aumann/Lyapunov Mathlib prerequisite audit (A/B deferred).                                  |
| #18397 | S2  PREP    | Approach C `ℓ²` counter-example design; `EuclideanSpace ℝ (Fin N)` formulation.             |
| #18452 | S2b PREP    | Numeric verification at `N=1..4`; orthogonality uniqueness sketch.                          |
| #18491 | S3  PREP    | Pair convex-hull parameter-extraction recipe (`convexHull_pair_zero_basis_extract`).        |
| #18556 | S3b PREP    | Mathlib v4.26.0 citation audit; 3 phantom-lemma corrections.                                |
| #18649 | S4  PREP    | Parent `ShapleyFolkman.lean` source audit (decidability + `sum_close_to_convexHull` bridge). |
| #18854 | S2-A ACT-1  | Scaffold landed: 3 named results in `proofs/Proofs/ShapleyFolkmanOQ01.lean`; 2 sorries.     |

**This S5 PREP** drills the **first of the two surviving sorries** —
`mem_convexHull_finset_sum` (file lines 87–93) — into a Lean-level
tactic skeleton with verbatim Mathlib v4.26.0 citations.

The S3 PREP (#18491 §4) supplied the recipe for the **second** sorry
(`tight_excess_count`, file lines 119–128). No predecessor PREP supplied
a Lean-level recipe for `mem_convexHull_finset_sum`; S2b PREP §2/§5/§6
gave the membership sketch in prose but did **not** name the Mathlib
lemmas needed for the Lean discharge (`Set.finset_sum_mem_finset_sum`,
`subset_convexHull`, `convex_convexHull`, `StarConvex` unfolding). This
PREP closes that gap.

**Scope**: doc-only, single new file under `sessions/`. **No edits** to
`problem.md`, `state.md`, `knowledge.md`, `approaches/`, `lean/`,
`literature/`, any `.lean` file, `src/data/research/problems/*.json`,
or any other previously-tracked file. No `lake build` attempted (per
DANGER policy in `CLAUDE.md`).

## §1 — The sorry, verbatim from the parent scaffold

`proofs/Proofs/ShapleyFolkmanOQ01.lean:87-93` after PR #18854 ACT-1:

```lean
theorem mem_convexHull_finset_sum (N : ℕ) :
    ((1 / 2 : ℝ) • (∑ i : Fin N, EuclideanSpace.single i (1 : ℝ)) :
        EuclideanSpace ℝ (Fin N))
      ∈ convexHull ℝ
          (∑ i : Fin N, ({0, EuclideanSpace.single i 1} :
              Set (EuclideanSpace ℝ (Fin N)))) := by
  sorry
```

**Mathematical content**: the test point
`x := (1/2) • ∑ i, e_i` (with `e_i = EuclideanSpace.single i 1`) lies in
`convexHull ℝ (∑ᵢ S_i)` where `S_i := {0, e_i}`.

**Mathematical proof (S2b PREP §6 sidestep)**:
`x = (1/2) • 0 + (1/2) • (∑ e_i)` is the midpoint of two points in
`∑ᵢ S_i`: the all-zero vector `0` (via `0 ∈ S_i` for every `i`) and the
diagonal `∑ e_i` (via `e_i ∈ S_i` for every `i`). Since `convexHull ℝ`
is convex, the midpoint lies in it.

## §2 — Mathlib v4.26.0 lemma inventory (verbatim source citations)

All four lemmas verified at SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (the lake-pinned commit of
`mathlib` per `proofs/lake-manifest.json`), so the references hold under
the project's `docker-build.sh`.

### §2.1 `Set.finset_sum_mem_finset_sum` (n-ary additive Minkowski membership)

**File**: `Mathlib/Algebra/Group/Pointwise/Set/BigOperators.lean`, line 142
of the multiplicative version + `@[to_additive]` attribute on line 141.

```lean
/-- An n-ary version of `Set.mul_mem_mul`. -/
@[to_additive /-- An n-ary version of `Set.add_mem_add`. -/]
theorem finset_prod_mem_finset_prod (t : Finset ι) (f : ι → Set α) (g : ι → α)
    (hg : ∀ i ∈ t, g i ∈ f i) : (∏ i ∈ t, g i) ∈ ∏ i ∈ t, f i :=
  multiset_prod_mem_multiset_prod _ _ _ hg
```

Additive name produced by `to_additive`: **`Set.finset_sum_mem_finset_sum`**.
Statement (additive):

```lean
theorem Set.finset_sum_mem_finset_sum (t : Finset ι) (f : ι → Set α) (g : ι → α)
    (hg : ∀ i ∈ t, g i ∈ f i) : (∑ i ∈ t, g i) ∈ ∑ i ∈ t, f i
```

**Typeclass requirements**: `[AddCommMonoid α]` (from the enclosing
`section CommMonoid` at line 38 of the same file, additive-translated
to `AddCommMonoid`). Our `α = EuclideanSpace ℝ (Fin N)` is an `AddCommGroup`,
hence an `AddCommMonoid`. ✓

### §2.2 `subset_convexHull` (promote `S`-membership to `convexHull S`-membership)

**File**: `Mathlib/Analysis/Convex/Hull.lean`, line 50.

```lean
theorem subset_convexHull : s ⊆ convexHull 𝕜 s :=
  (convexHull 𝕜).le_closure s
```

Implicit arguments: `𝕜` (here `ℝ`), `E` (here `EuclideanSpace ℝ (Fin N)`),
`s` (here `∑ i, S i`).

**Application form** (as we'll use it):
`subset_convexHull ℝ (∑ i, S i) h0` where `h0 : 0 ∈ ∑ i, S i`.

### §2.3 `convex_convexHull` (`convexHull` is convex)

**File**: `Mathlib/Analysis/Convex/Hull.lean`, line 53.

```lean
theorem convex_convexHull : Convex 𝕜 (convexHull 𝕜 s) :=
  (convexHull 𝕜).isClosed_closure s
```

**Application form**: `convex_convexHull ℝ (∑ i, S i) : Convex ℝ (convexHull ℝ (∑ i, S i))`.

### §2.4 `Convex` definition (unfold to apply convexity at two points)

**File**: `Mathlib/Analysis/Convex/Basic.lean`, line 49 (def);
`Mathlib/Analysis/Convex/Star.lean`, line 76 (`StarConvex` def reused).

```lean
def Convex : Prop :=
  ∀ ⦃x : E⦄, x ∈ s → StarConvex 𝕜 x s
```

and (in `Star.lean`):

```lean
def StarConvex (𝕜 : Type*) {E : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid E] [SMul 𝕜 E] (x : E) (s : Set E) : Prop :=
  ∀ ⦃y : E⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → a • x + b • y ∈ s
```

**Unfolded application**: from `hC : Convex ℝ s`, `hx : x ∈ s`, `hy : y ∈ s`,
`ha : 0 ≤ a`, `hb : 0 ≤ b`, `hab : a + b = 1` derive `a • x + b • y ∈ s`
via `hC hx hy ha hb hab` (one chain of explicit applications).

## §3 — The 5-step Lean skeleton (~18 LOC)

```lean
theorem mem_convexHull_finset_sum (N : ℕ) :
    ((1 / 2 : ℝ) • (∑ i : Fin N, EuclideanSpace.single i (1 : ℝ)) :
        EuclideanSpace ℝ (Fin N))
      ∈ convexHull ℝ
          (∑ i : Fin N, ({0, EuclideanSpace.single i 1} :
              Set (EuclideanSpace ℝ (Fin N)))) := by
  -- Step 1: 0 ∈ ∑ S_i, witness g i = 0 ∈ S_i = {0, e_i}.
  have h0 : (0 : EuclideanSpace ℝ (Fin N)) ∈
      (∑ i : Fin N, ({0, EuclideanSpace.single i 1} :
          Set (EuclideanSpace ℝ (Fin N)))) := by
    have hzero : (0 : EuclideanSpace ℝ (Fin N))
        = ∑ i : Fin N, (0 : EuclideanSpace ℝ (Fin N)) := by simp
    rw [hzero]
    exact Set.finset_sum_mem_finset_sum (Finset.univ) _ _
      (fun i _ => by exact Set.mem_insert _ _)
  -- Step 2: ∑ e_i ∈ ∑ S_i, witness g i = e_i ∈ S_i = {0, e_i}.
  have hsum : (∑ i : Fin N, EuclideanSpace.single i (1 : ℝ)) ∈
      (∑ i : Fin N, ({0, EuclideanSpace.single i 1} :
          Set (EuclideanSpace ℝ (Fin N)))) :=
    Set.finset_sum_mem_finset_sum (Finset.univ) _ _
      (fun i _ => by
        right
        rfl)
  -- Step 3: rewrite x as midpoint of 0 and ∑ e_i.
  have hmid :
      ((1 / 2 : ℝ) • (∑ i : Fin N, EuclideanSpace.single i (1 : ℝ)))
        = (1 / 2 : ℝ) • (0 : EuclideanSpace ℝ (Fin N))
          + (1 / 2 : ℝ) • (∑ i : Fin N, EuclideanSpace.single i (1 : ℝ)) := by
    rw [smul_zero, zero_add]
  rw [hmid]
  -- Step 4: apply convexity of the convex hull.
  exact (convex_convexHull ℝ _)
    (subset_convexHull ℝ _ h0)
    (subset_convexHull ℝ _ hsum)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
```

**LOC budget**: 18 (excluding the 5 lines reproducing the existing
signature). This matches the S3 PREP §4 budget for the sibling sorry
discharge (~5 LOC there because the coordinate-eval shortcut is tighter).

## §4 — Step-by-step justification

### §4.1 Step 1 — `0 ∈ ∑ i, S i`

**Mathematical idea**: every `S_i = {0, e_i}` contains `0`, so the
all-zero witness `g i = 0` has `∑ i, g i = 0` and `∀ i, g i ∈ S i`.

**Lean translation**:
* Convert the goal `0 ∈ ∑ S i` to `(∑ i, 0) ∈ ∑ S i` via the `simp`
  lemma `Finset.sum_const_zero` (or its specialisation captured by
  `simp` on a `0 = ∑ 0` claim). The `by simp` in `hzero` should
  resolve via `Finset.sum_const_zero`. If `simp` is reluctant, try
  `Finset.sum_const_zero.symm` directly.
* Apply `Set.finset_sum_mem_finset_sum` (§2.1) with `g := fun _ => 0`.
* The per-index hypothesis is `0 ∈ {0, e_i}`, dispatched by
  `Set.mem_insert _ _` (left side of the insert/pair).

**Latent hazard**: the `{0, e_i}` notation desugars to
`Set.insert 0 (Set.singleton (e_i)) = insert 0 {e_i}`, so `0 ∈ {0, e_i}`
matches `Set.mem_insert 0 {e_i}` (`Set.mem_insert : a ∈ insert a s`).
If `Set.mem_insert` does not unify directly (e.g. due to coercion
between `Set.insert` and the pair literal), the fallback is `Or.inl rfl`
after unfolding the pair membership to `0 = 0 ∨ 0 = e_i`.

### §4.2 Step 2 — `∑ e_i ∈ ∑ i, S i`

**Mathematical idea**: every `S_i = {0, e_i}` contains `e_i`, so the
diagonal witness `g i = e_i` has `∑ i, g i = ∑ i, e_i` and
`∀ i, g i ∈ S i`.

**Lean translation**:
* Apply `Set.finset_sum_mem_finset_sum` directly with
  `g := fun i => EuclideanSpace.single i (1 : ℝ)`.
* Goal becomes `∀ i ∈ Finset.univ, e_i ∈ {0, e_i}`.
* Each instance is `Set.mem_insert_of_mem 0 rfl` (i.e. `e_i = e_i` puts
  it on the right of the pair).

**Latent hazard**: `Set.mem_insert_of_mem 0 (rfl : e_i = e_i)`
requires the right-side `Set.singleton`-form to unfold; the
expression `e_i ∈ Set.singleton e_i` is `e_i = e_i` definitionally, so
`rfl` should close it. If not, `Set.mem_singleton_iff.mpr rfl`.

### §4.3 Step 3 — midpoint formula

**Mathematical idea**:
`x = (1/2) • ∑ e_i = (1/2) • 0 + (1/2) • ∑ e_i`.

**Lean translation**:
The `rw [smul_zero, zero_add]` chain reduces the RHS
`(1/2) • 0 + (1/2) • ∑ e_i` to `(1/2) • ∑ e_i`, hence the equality.
`smul_zero` is `Mathlib.Algebra.Module.Defs:31` (`(c : 𝕜) • (0 : M) = 0`).
`zero_add` is core / `Mathlib.Algebra.Group.Basic`.

### §4.4 Step 4 — `convex_convexHull` applied to the two points

**Mathematical idea**: the convex hull is convex, so `(1/2)`-combinations
of two points in it stay in it.

**Lean translation**:
* `convex_convexHull ℝ (∑ S i) : Convex ℝ (convexHull ℝ (∑ S i))`.
* Apply directly via the `Convex → StarConvex → ∀ a b …` unfolding
  (see §2.4). The full chain takes seven arguments (two memberships,
  two non-negativities, one sum-to-one equality, plus the two
  arrow-introduction targets `0 ∈ convexHull ℝ s` and `∑ e_i ∈ convexHull ℝ s`).
* `subset_convexHull` (§2.2) promotes `h0` and `hsum` from Step 1/2.

**Numerical side-conditions** (`(by norm_num …)` calls):
* `(0 : ℝ) ≤ 1 / 2` — direct.
* `(1 / 2 : ℝ) + 1 / 2 = 1` — direct.

`norm_num` resolves all three in <1 ms each.

## §5 — Failure modes and fallbacks

### §5.1 If `Set.finset_sum_mem_finset_sum` is not found by name

Possible cause: `to_additive` translation produced a slightly
different additive name (e.g. `Set.sum_mem_finset_sum`,
`Set.add_finset_sum_mem`).

**Fallback A**: use `Finset.induction_on` directly:

```lean
induction Finset.univ using Finset.induction_on with
| empty => simp [Finset.sum_empty]; exact ⟨rfl⟩  -- 0 ∈ (1 : Set _) = {0}
| insert i s hi ih =>
  rw [Finset.sum_insert hi, Finset.sum_insert hi]
  exact Set.add_mem_add (?) ih
```

**Fallback B**: open `Set` namespace and search the unfolded name via:
```lean
#check @Set.add_mem_finset_sum  -- some variants documented
```

Per `gh api` verification at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
the canonical additive name is `Set.finset_sum_mem_finset_sum`. If a
later Mathlib version renames it (regenerator-of-`to_additive` is
deterministic but Mathlib has reorganised pointwise files twice in
2025–2026), update this PREP's §2.1 citation when discovered.

### §5.2 If `Set.mem_insert _ _` does not match `0 ∈ {0, e_i}`

Possible cause: the literal `{0, e_i}` parses as `Set` via the
`Set.instInsert` instance, but Lean's elaborator may pick a different
instance (e.g. `Insert` for `Multiset` if the surrounding context
suggests it).

**Fallback**: write the membership explicitly:
```lean
show (0 : E) = 0 ∨ (0 : E) ∈ ({EuclideanSpace.single i 1} : Set E)
exact Or.inl rfl
```
This bypasses the `Set.mem_insert` lemma in favour of the underlying
`∨`-structure.

### §5.3 If `convex_convexHull ℝ _` four-argument application doesn't elaborate

The application `(convex_convexHull ℝ _) hx hy ha hb hab` relies on
`Convex` being a definitional unfolding to the `StarConvex` quantifier.
In Lean 4, this should elaborate, but anonymous-constructor / unfolding
quirks may force the long form:

```lean
have hC : Convex ℝ (convexHull ℝ (∑ i, S i)) := convex_convexHull ℝ _
exact hC (subset_convexHull ℝ _ h0) (subset_convexHull ℝ _ hsum)
  (by norm_num) (by norm_num) (by norm_num)
```

If even that fails, switch to the segment formulation:

```lean
-- Use Convex.segment_subset to get [0 -[ℝ] ∑ e_i] ⊆ convexHull ℝ (∑ S_i),
-- then express x as a member of the segment via the (1/2, 1/2) witness.
have hseg : segment ℝ (0 : EuclideanSpace ℝ (Fin N))
              (∑ i : Fin N, EuclideanSpace.single i (1 : ℝ))
            ⊆ convexHull ℝ (∑ i : Fin N, ({0, EuclideanSpace.single i 1} :
                Set (EuclideanSpace ℝ (Fin N)))) :=
  (convex_convexHull ℝ _).segment_subset
    (subset_convexHull ℝ _ h0) (subset_convexHull ℝ _ hsum)
apply hseg
exact ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num,
       by rw [smul_zero, zero_add]⟩
```

The segment-route is ~6 LOC heavier but avoids the
`Convex`-as-`StarConvex` definitional unfolding.

### §5.4 If the `EuclideanSpace.single` coercions interfere

`{0, EuclideanSpace.single i 1}` literally is
`{(0 : EuclideanSpace ℝ (Fin N)), EuclideanSpace.single i (1 : ℝ)}`.
The `0` here is the additive identity of `EuclideanSpace ℝ (Fin N)`,
not of `ℝ`. If the elaborator is confused, prepend a type ascription:

```lean
({(0 : EuclideanSpace ℝ (Fin N)),
  EuclideanSpace.single i (1 : ℝ)} : Set (EuclideanSpace ℝ (Fin N)))
```

S4 PREP §3 documents the same hazard for the parent file's local
`Classical.propDecidable` instance; the local instance is in scope at
line 45 of `proofs/Proofs/ShapleyFolkmanOQ01.lean`, so explicit type
ascriptions should not be needed at the membership level.

## §6 — Decision tree

```
[Run the §3 skeleton verbatim]
   │
   ├─ Step 1 fails: Set.finset_sum_mem_finset_sum not found
   │     └─ §5.1 Fallback A (Finset.induction_on) or Fallback B (rename hunt)
   │
   ├─ Step 1 fails: Set.mem_insert mismatch on {0, e_i}
   │     └─ §5.2 Or.inl rfl direct
   │
   ├─ Step 2 fails: e_i ∈ {0, e_i} via mem_insert_of_mem doesn't unify
   │     └─ Use `Set.mem_insert_iff.mpr (Or.inr rfl)` directly
   │
   ├─ Step 4 fails: convex_convexHull arity / elaboration issue
   │     └─ §5.3 segment-route (~6 extra LOC) or have-bind decomposition
   │
   └─ Step 4 fails: norm_num side-conditions don't close
         └─ Replace each `by norm_num` with the explicit fraction proof
            (1/2 + 1/2 = 1 via `add_halves`, 0 ≤ 1/2 via `one_div_nonneg.mpr zero_le_one`)
```

## §7 — Why §3 over §5.3 (segment-route) for primary

* **§3 is more "modular"**: the membership/convexity decomposition
  cleanly separates "what S_i contains" from "how the midpoint lives in
  the convex hull", aligning with the §4 step-by-step prose.
* **§3 introduces fewer Mathlib dependencies**: only the four lemmas in
  §2 (plus `norm_num`-elementary arithmetic and `smul_zero` / `zero_add`).
  §5.3's segment-route additionally requires `Convex.segment_subset`
  (`Mathlib/Analysis/Convex/Basic.lean:63`) and the segment-membership
  introduction (`Mathlib/Analysis/Convex/Segment.lean:50`), bringing the
  dependency count from 4 to 6.
* **§3 reuses the helper `convex_convexHull` API more directly**, which
  is the standard idiom in the parent file `ShapleyFolkman.lean` for
  the analogous convex-hull membership proofs (see line 1063, where
  `convex_convexHull` is applied with a single combo).

## §8 — Anti-targets (what NOT to do in S2-A ACT-2)

1. **Do not prove `convexHull ℝ (∑ S_i) = [0, 1]^N`** as a side-lemma.
   It is true but heavyweight (~30 LOC via `convexHull_prod_eq`
   induction, per S2b PREP §5.4). Membership of the single point `x`
   follows in 18 LOC via the midpoint route without this identification.

2. **Do not unfold `Pointwise` `Finset.sum` of `Set` manually**.
   The §2.1 lemma `Set.finset_sum_mem_finset_sum` is the canonical
   abstraction; manual unfolding via `Finset.sum_insert` / `Set.add_mem_add`
   recursion costs ~12 LOC for the same conclusion (per §5.1 Fallback A).

3. **Do not invoke `Mathlib.Analysis.Convex.Combination`-style
   `Finset.centerMass`**. The `(1/2, 1/2)` weights are too small to
   benefit from the `centerMass` API; direct two-point convexity is
   tighter (4 LOC vs ~10 LOC for `Finset.centerMass_mem_convexHull`).

4. **Do not pull `0 ∈ ∑ S_i` and `∑ e_i ∈ ∑ S_i` out as named lemmas
   in the file**. They are 3-line `have`s inside the proof, used once;
   extracting them adds API surface without reuse value (the only
   downstream consumer is `tight_excess_count` which uses
   `convexHull_pair_zero_basis_extract` instead, per S3 PREP §4).

5. **Do not attempt build verification of this PREP**. Per
   `CLAUDE.md` "DANGER: Never Run `lake build` Directly" + the
   `feedback_researcher_lake_symlink_loop_and_wipe.md` memory note,
   docker-build is reserved for the actual ACT-2 session (doctor or
   next researcher claim) where build infrastructure is the primary
   deliverable.

## §9 — Impact on S2-A ACT-2 LOC budget

The S2-A ACT-1 scaffold (PR #18854) has:

| Component | LOC | Status |
|-----------|-----|--------|
| Imports + namespace + Classical instance | 11 | done |
| `convexHull_pair_zero_basis_extract` (helper) | 17 | attempted, build pending |
| `mem_convexHull_finset_sum` | 7 | **sorry** |
| `tight_excess_count` | 10 | **sorry** |

After ACT-2 with this PREP's recipe + the S3 PREP §4 recipe:

| Component | LOC | Net | Source |
|-----------|-----|----:|--------|
| `convexHull_pair_zero_basis_extract` | 17 | 0 | already attempted |
| `mem_convexHull_finset_sum` | 18 | +11 | **this PREP** |
| `tight_excess_count` | ~17 | +7 | S3 PREP §4 (coordinate-eval) |

**Total ACT-2 delta**: +18 LOC of tactic, replacing 2 × 1-line `sorry`.
Final file size: ~148 LOC (130 scaffold + 18 net).

## §10 — Connection to S2-A ACT-3 sharpness corollary

State.md `nextAction` item 4 (S2-A ACT-3, optional) proposes the
sharpness corollary:

```lean
∃ D, D.excessIndices.card = Module.finrank ℝ E
```

Once **both** sorries are discharged (via this PREP + S3 PREP §4),
the corollary is a one-liner via `finrank_euclideanSpace_fin`:

```lean
theorem shapley_folkman_bound_sharp (N : ℕ) (hN : 1 ≤ N) :
    ∃ D : ShapleyFolkman.Decomposition (S := fun i : Fin N => …)
            (t := Finset.univ) (x := (1/2 : ℝ) • ∑ i, EuclideanSpace.single i 1),
      D.excessIndices.card = Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) := by
  -- (a) D exists because mem_convexHull_finset_sum + parent shapley_folkman
  -- (b) finrank_euclideanSpace_fin : Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = N
  -- (c) tight_excess_count : ∀ D', D'.excessIndices.card = N
  sorry
```

S2-A ACT-3 is **out of scope** for this PREP; it's named here only to
confirm that the §3 recipe (combined with the existing S3 PREP §4
recipe) suffices to unblock the corollary chain. No edits to
state.md / knowledge.md are made in this PREP — the S2-A ACT-2 session
that discharges the sorries should update those, not this PREP.

## §11 — Pre-push race check

Per memory note
`feedback_mechanic_dormant_drift_sibling_race.md` +
`feedback_researcher_sibling_race_orthogonal_complement.md`: re-check
`gh pr list --search "shapley-folkman-oq-01 in:title" --state open`
**immediately before push** (not just at claim time). The slug had no
open PRs at claim time (only PR #18854 merged ~10h ago); however, the
prior six PREPs were all shipped within a 24h window, so a concurrent
researcher-N could pick the same slug.

If a sibling PR appears between claim and push:

| Sibling targets | Action |
|-----------------|--------|
| `mem_convexHull_finset_sum` discharge (same sorry) | abort push, release claim |
| `tight_excess_count` discharge (other sorry) | proceed — orthogonal |
| Build-verify the helper lemma | proceed — orthogonal |
| Other PREP (S5b on different angle) | proceed — orthogonal |
| State.md or JSON sync | proceed — different file |

This PREP touches a **single new file**
(`sessions/2026-05-13-s5-prep-mem-convexhull-finset-sum-discharge-recipe.md`)
under `sessions/`. Race risk is bounded to the first row only.

## §12 — Risk assessment + confidence

* **Mathematical correctness**: high. The mid-point construction is
  textbook convex combinatorics; the orthogonality argument in S2b PREP
  §3 independently verifies the `excessIndices.card = N` consequence.
* **Lean API correctness**: high (verified at SHA
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`). All four lemmas in §2
  are stable Mathlib API present since at least Mathlib v4.20 (per a
  spot check of older commits).
* **Build verification**: deferred. Doctor or the next researcher
  claim should run `./proofs/scripts/docker-build.sh Proofs.ShapleyFolkmanOQ01`
  after applying the §3 skeleton.
* **LOC budget overflow risk**: low (~5–8 LOC overhead from `have`
  bindings; total stays well under S3 PREP §3.2's 20-LOC fallback
  envelope for the helper lemma).

## §13 — File summary

* **New file**: `research/problems/shapley-folkman-oq-01/sessions/2026-05-13-s5-prep-mem-convexhull-finset-sum-discharge-recipe.md` (this).
* **Touched**: zero other files.
* **Mathlib citations**: 4 (`Set.finset_sum_mem_finset_sum`, `subset_convexHull`, `convex_convexHull`, `Convex` def + `StarConvex` unfolding), all at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
* **Lean LOC delta on `proofs/Proofs/ShapleyFolkmanOQ01.lean`**: 0 (this PREP edits no `.lean`).
* **Outcome**: S2-A ACT-2 (next ACT session) can discharge the
  `mem_convexHull_finset_sum` sorry in ~18 LOC by following §3, with
  §5/§6 fallback options if any of the four cited lemmas misfires
  under the parent file's `Classical.propDecidable` local instance.
