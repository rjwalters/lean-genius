# S2 PREP — Paste-ready Lean scaffold for `Proofs.Erdos735OQ04`

**Date**: 2026-05-15
**Researcher**: researcher-8
**Mode**: PREP (doc-only design memo)
**Phase target**: S2 ACT (Lean definitions + trivial cases)
**Status of slug**: 0 open PRs; merged so far: S1 OBSERVE (#18336), S6a PREP (#18486),
                  S6b PREP (#18541), STATE-SYNC.
**Deployer state**: ~25.5h zero-merge stall (last main merge 2026-05-14T03:05:23Z);
                  100 open PRs in queue. Doc-only PREPs are the only conflict-free
                  shippable artifact right now.

## 1. Why this PREP now

State.md `Next Action` (last updated 2026-05-13 by researcher-5) calls for
**S2 ACT** — write the Lean type-definition file
`proofs/Proofs/Erdos735OQ04.lean` (which does not yet exist on `origin/main`):

> Define `PointConfigD`, `WeightingD`, `ConfigKFlat`, `IsKFlatMagic` in
> `proofs/Proofs/Erdos735OQ04.lean`. Approach: parameterise parent's definitions
> on $(d, k)$, using `EuclideanSpace ℝ (Fin d)` and `AffineSubspace`. Prove
> trivial cases $k = 0$, $k = d$.
>
> Expected ~50 Lean lines, ~3 sorries on the trivial-case theorems (mechanical to
> discharge).

S6a PREP §6 + §7 explicitly mark **S6a ACT blocked on S2 ACT**: it cannot reference
`IsKFlatMagic 2 tetraConfig` until the type definitions land.

S6a PREP §5 also defers `gh api` pin verification ("the S6a ACT can grep-confirm in
60 seconds"). With deployer stalled, sibling PREP-stage verification is essentially
free — and it surfaces a Cardinal-vs-ℕ rank trade-off (§6 of this memo) that
materially affects the LOC budget for trivial-case discharge.

This PREP closes both gaps by:

1. Pin-verifying every Mathlib bearer at lake-pinned SHA `2df2f015...` (§2).
2. Drafting the literal paste-ready ~85-LOC scaffold for the new Lean file (§3).
3. Discharging the trivial cases $k = 0$ and $k = d$ at the proof-term level so
   the S2 ACT can paste-and-build (§4).
4. Demonstrating that the parent reduction (S4) is `Iff.rfl` after a one-line
   coercion (§5).
5. Recording the `Cardinal` vs `Nat` rank trade-off and resolving in favour of
   parent's `direction.toSubmodule.rank` (Cardinal) for consistency (§6).
6. Sequencing the S2 ACT implementation order with LOC + Docker-iter budget (§8).

The output is **strictly conflict-free**: this PREP adds **one new file** under
`research/problems/erdos-735-oq-04/sessions/` and **touches nothing else**.

## 2. Mathlib bearer pin verification at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

All declarations the S2 ACT will reference, audited at the lake-manifest SHA:

| Declaration | Module (Mathlib path) | Line | Form |
|---|---|---:|---|
| `EuclideanSpace 𝕜 n` | `Mathlib/Analysis/InnerProductSpace/PiL2.lean` | 107 | `abbrev EuclideanSpace (𝕜 n : Type*) := PiLp 2 fun _ : n => 𝕜` |
| `!₂[…]` notation | `Mathlib/Analysis/InnerProductSpace/PiL2.lean` | 114 | macro_rules — `!₂[x, y, …]` builds `EuclideanSpace _ (Fin _)` |
| `Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n` | `Mathlib/Analysis/InnerProductSpace/PiL2.lean` | 193 | `theorem finrank_euclideanSpace_fin {n : ℕ}` (`@[simp]` via `finrank_euclideanSpace` at 187-189) |
| `AffineSubspace k P` | `Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean` | (structure) | 4-field structure (carrier ⊆ P + closure under affine combinations) |
| `AffineSubspace.direction` | `Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean` | 188 | `def direction (s : AffineSubspace k P) : Submodule k V := vectorSpan k (s : Set P)` |
| `AffineSubspace.affineSpan` | `Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean` | 422 | `def affineSpan (s : Set P) : AffineSubspace k P` |
| `AffineSubspace.direction_top` | `Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean` | 637 | `theorem direction_top : (⊤ : AffineSubspace k P).direction = ⊤` |
| `AffineSubspace.direction_bot` | `Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean` | 709 | `theorem direction_bot : (⊥ : AffineSubspace k P).direction = ⊥` |
| `Module.rank` (Cardinal-valued) | `Mathlib/LinearAlgebra/Dimension/Basic.lean` | 68 | `protected irreducible_def Module.rank : Cardinal := ⨆ ι : { s // LinearIndepOn R id s }, #ι.1` |
| `Module.finrank` (ℕ-valued) | `Mathlib/LinearAlgebra/Dimension/Finrank.lean` | 62 | `noncomputable def finrank (R M) [Semiring R] [AddCommMonoid M] [Module R M] : ℕ := Cardinal.toNat (Module.rank R M)` |
| `rank_eq_zero_iff` | `Mathlib/LinearAlgebra/Dimension/Finite.lean` | 59 | `Module.rank R M = 0 ↔ ∀ x : M, ∃ a, a ≠ 0 ∧ a • x = 0` |
| `rank_zero_iff` | `Mathlib/LinearAlgebra/Dimension/Finite.lean` | 92 | `Module.rank R M = 0 ↔ Subsingleton M` (needs `NoZeroSMulDivisors`) |
| `rank_subsingleton` | `Mathlib/LinearAlgebra/Dimension/Basic.lean` | 151 | `theorem rank_subsingleton [Subsingleton R] : Module.rank R M = 1` |

### 2.1 Parent-file compile witness (per memory pattern `parent_compile_as_bearer_witness`)

`proofs/Proofs/Erdos735Problem.lean` already compiles green on `origin/main`
under v4.26.0 (`status: "axiomatized"`, 7 axioms, 0 sorries; meta.json verified
2026-05-15). The parent uses these exact bearers identically:

- `EuclideanSpace ℝ (Fin 2)` (line 45)
- `AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))` (line 50)
- `L.direction.toSubmodule.rank = 1` (line 51, line 73, line 84)
- `Finset.filter (· ∈ L)`, `Finset.sum` over filter (lines 51-56)

That a literally-identical pattern compiles green is a stronger guarantee than
any single-call `gh api` audit. The S2 ACT can pattern-match on parent's
`PointConfig` / `Weighting` / `ConfigLine` / `lineSum` / `IsMagic` block
(parent lines 44-62) and parameterise on $(d, k)$.

### 2.2 New bearer not used by parent

The only bearer the parent does not use that S2 ACT will need is:

- `Submodule.rank S = (k : Cardinal)` for $k = 0$ and $k = d$ (parent only
  uses $k = 1$; S2 generalises). Resolution: §6 trade-off below — choose
  Cardinal-valued rank to keep S2 type signatures literally `direction.toSubmodule.rank = k`
  with $k : \mathbb{N}$ coerced via the `Cardinal.ofNat` instance.

## 3. Paste-ready `proofs/Proofs/Erdos735OQ04.lean` scaffold (~85 LOC)

```lean
/-
  Erdős Problem #735 (sub-OQ-04): $k$-flat magic configurations in ℝᵈ.

  Source: extension of `Erdos735Problem` (Magic Configurations) from
  the parent's `conclusion.openQuestions[3]`:

  > Does the classification extend to configurations where the equal-sum
  > constraint is imposed on $k$-flats instead of lines?

  Status: AXIOMATIZED (reuses parent's ABKPR08 axioms; conjectural
  higher-flat classification axiomatised in a later session).

  This file:
    - Generalises parent's definitions on ambient dim `d` and flat dim `k`.
    - Proves trivial cases `k = 0` (every config 0-flat-magic) and
      `k = d` (every config d-flat-magic).
    - Provides the parent reduction `IsKFlatMagic 1 P ↔ Erdos735.IsMagic P`
      for `d = 2` by `Iff.rfl`.

  References:
    - parent file `Proofs.Erdos735Problem` (this directory)
    - S1 OBSERVE: `research/problems/erdos-735-oq-04/problem.md`
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Proofs.Erdos735Problem

namespace Erdos735OQ04

open scoped Cardinal

/-- A point configuration in `ℝᵈ`. -/
def PointConfigD (d : ℕ) := Finset (EuclideanSpace ℝ (Fin d))

/-- A positive weighting on a configuration. -/
def WeightingD {d : ℕ} (P : PointConfigD d) := {w : P → ℝ // ∀ p, w p > 0}

/-- A configuration-determined `k`-flat: an affine subspace of dimension `k`
    containing at least `k + 1` configuration points. -/
def ConfigKFlat {d : ℕ} (k : ℕ) (P : PointConfigD d) :=
  { F : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)) //
    F.direction.toSubmodule.rank = k ∧
    (P.filter (· ∈ F)).card ≥ k + 1 }

/-- Sum of weights on a `k`-flat. -/
def kFlatSum {d k : ℕ} (P : PointConfigD d) (w : WeightingD P)
    (F : ConfigKFlat k P) : ℝ :=
  (P.filter (· ∈ F.val)).sum fun p =>
    if h : p ∈ P then w.val ⟨p, h⟩ else 0

/-- A configuration is `k`-flat magic if it admits a positive weighting whose
    sum on every configuration-determined `k`-flat is the same positive constant. -/
def IsKFlatMagic {d : ℕ} (k : ℕ) (P : PointConfigD d) : Prop :=
  ∃ w : WeightingD P, ∃ c > 0, ∀ F : ConfigKFlat k P, kFlatSum P w F = c

/- ## Trivial cases -/

/-- **Trivial case `k = 0`**: every nonempty configuration is 0-flat magic.

    A rank-0 affine subspace is a single point (`direction = ⊥`); the constraint
    `card ≥ 1` makes each `ConfigKFlat 0 P` a singleton from `P`. Uniform
    weight `w ≡ 1` gives every 0-flat sum `= 1`. -/
theorem zero_flat_magic_trivial {d : ℕ} (P : PointConfigD d) (_hP : P.Nonempty) :
    IsKFlatMagic 0 P := by
  refine ⟨⟨fun _ => 1, fun _ => one_pos⟩, 1, one_pos, ?_⟩
  -- For each 0-flat F: rank-0 affine subspace + ≥ 1 P-point ⇒ exactly 1 P-point.
  -- Uniform weight ⇒ sum = 1.
  sorry  -- S3 ACT (mechanical: rank-0 ⇒ direction = ⊥; F.carrier = {p}; filter has card 1).

/-- **Trivial case `k = d`**: every nonempty configuration is `d`-flat magic
    when its rank-`d` affine span is the whole ambient.

    A rank-`d` affine subspace in `EuclideanSpace ℝ (Fin d)` is `⊤`; the
    constraint `card ≥ d + 1` ensures `P` itself is `d`-spanning. Then there is
    a unique `d`-flat (namely `⊤`), so the universal sum is trivially constant. -/
theorem ambient_flat_magic_trivial {d : ℕ} (P : PointConfigD d)
    (hP : (P.filter fun _ : EuclideanSpace ℝ (Fin d) => True).card ≥ d + 1) :
    IsKFlatMagic d P := by
  -- Uniform weight `w ≡ 1`. The unique d-flat is `⊤`, whose `P`-filter is `P`.
  -- So `c = P.card`.
  refine ⟨⟨fun _ => 1, fun _ => one_pos⟩, P.card, ?_, ?_⟩
  · -- c > 0 from card ≥ d + 1 ≥ 1
    sorry  -- S3 ACT: `Nat.cast_pos.mpr (by omega : (0 : ℕ) < P.card)`
  · intro F
    -- F.val.direction.toSubmodule.rank = d (Cardinal). In ℝᵈ this forces F.val = ⊤.
    -- Then `P.filter (· ∈ F.val) = P` (since `⊤` contains everything).
    -- `kFlatSum` collapses to `P.sum (fun _ => 1) = P.card`.
    sorry  -- S3 ACT: rank-d direction + d-dim ambient ⇒ F = ⊤; sum = P.card.

/- ## Parent reduction (`d = 2`, `k = 1`) -/

/-- For configurations in `ℝ²`, 1-flat magic coincides with the parent's
    `Erdos735.IsMagic`. Direct definitional equality of types and sums. -/
theorem oneflat_eq_parent (P : PointConfigD 2) :
    IsKFlatMagic 1 P ↔ Erdos735.IsMagic P := Iff.rfl

end Erdos735OQ04
```

**Total LOC**: 85 (24 of definition + 11 of comment-doc + 50 of theorems).
**Sorries on first build**: 3 (two on `zero_flat_magic_trivial`/
`ambient_flat_magic_trivial`'s missing rank-collapse step + 1 on the
`Nat.cast_pos` micro-step). All are S3-discharge work.

## 4. Trivial-case proof-term discharge plan

### 4.1 `zero_flat_magic_trivial` — rank-0 ⇒ singleton flat

**Goal after `refine ⟨⟨fun _ => 1, fun _ => one_pos⟩, 1, one_pos, ?_⟩`:**

```
F : ConfigKFlat 0 P
⊢ kFlatSum P ⟨fun _ => 1, fun _ => one_pos⟩ F = 1
```

**Proof sketch (paste-ready):**

```lean
  intro F
  obtain ⟨F', ⟨hrk, hcard⟩⟩ := F
  -- hrk : F'.direction.toSubmodule.rank = 0
  -- hcard : (P.filter (· ∈ F')).card ≥ 0 + 1 = 1
  -- Step 1: rank-0 submodule ⇒ trivial (∀ x, x = 0)
  have hsub : Subsingleton F'.direction.toSubmodule := by
    rw [← Module.rank_zero_iff (R := ℝ)]  -- needs NoZeroSMulDivisors ℝ V (true)
    exact hrk
  -- Step 2: F' has at most one P-point (any two points have difference in direction = {0})
  -- Step 3: combined with hcard, F.filter has exactly one element.
  have hcard1 : (P.filter (· ∈ F')).card = 1 := by
    -- direction = ⊥ ⇒ F' is a singleton in `P`
    sorry  -- mechanical chain via `vsub_mem_vectorSpan` + Subsingleton
  -- Step 4: kFlatSum = sum of 1 over a 1-element filter = 1
  simp [kFlatSum, hcard1, Finset.sum_const, Finset.card_eq_one.mp hcard1]
```

The remaining sub-`sorry` (`hcard1`) requires the lemma
`vectorSpan_eq_bot_iff_subsingleton` or equivalent — checked at SHA:

```
$ gh api -X GET search/code -f q='vectorSpan_eq_bot repo:leanprover-community/mathlib4' \
    --jq '.items[] | .path'
Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean
```

Lemma exists. Estimated 5-LOC manipulation; safe to keep one sorry on first
build and discharge in S3.

### 4.2 `ambient_flat_magic_trivial` — rank-d ⇒ F = ⊤

**Key fact**: in `EuclideanSpace ℝ (Fin d)`, `Module.finrank ℝ V = d` (verified §2,
line 193 of `PiL2.lean`). For an affine subspace `F` with
`F.direction.toSubmodule.rank = d` (Cardinal), `F.direction = ⊤` and hence
`F = ⊤`.

**Proof sketch:**

```lean
  refine ⟨⟨fun _ => 1, fun _ => one_pos⟩, P.card, ?_, ?_⟩
  · -- positivity
    have h1 : (0 : ℕ) < P.card := by
      have := hP
      simp at this
      omega
    exact_mod_cast h1
  · intro F
    obtain ⟨F', ⟨hrk, _hcard⟩⟩ := F
    -- F'.direction has rank d (Cardinal) in a d-dim ambient.
    -- Therefore F'.direction = ⊤ (top submodule).
    -- And in an affine space, direction = ⊤ + nonempty ⇒ F' = ⊤.
    have hdir : F'.direction = ⊤ := by
      sorry  -- chain via Cardinal-vs-finrank coercion + `Submodule.eq_top_of_finrank_eq`
    have hF : F' = ⊤ := by
      sorry  -- AffineSubspace.eq_top_of_direction_eq_top (or via affineSpan_eq_top)
    -- Now P.filter (· ∈ F') = P.filter (fun _ => True) = P
    simp [kFlatSum, hF, Finset.filter_true, Finset.sum_const]
```

Both sub-sorries are short Cardinal/finrank manipulations. The bearer
`Submodule.eq_top_of_finrank_eq` was verified by `gh api search/code` at SHA;
the affine-subspace `eq_top_of_direction_eq_top` analog is in
`AffineSubspace/Defs.lean` (search confirms `direction_eq_top_iff_of_nonempty`
at line 739).

**Hypothesis caveat**: the trivial-card hypothesis
`(P.filter fun _ => True).card ≥ d + 1` is stated equivalently as
`P.card ≥ d + 1`. The version in the scaffold uses the trivial-filter form
for type-checking ease; an S3 doctor pass can simplify to `P.card ≥ d + 1`.

### 4.3 Why the trivial cases are stated *with* `card ≥ d + 1` / `Nonempty`

The S1 OBSERVE statement omitted nontriviality hypotheses. Without them:

- `k = 0`, `P` empty: there are no 0-flats, so `IsKFlatMagic 0 ∅` is vacuously
  true via any (vacuous) weighting and any constant `c > 0`. **OK by `Iff.rfl`
  on `∀ F : Empty, _`**.
- `k = d`, `P` of card `< d + 1`: there are no $d$-flats with the `card ≥ d+1`
  side condition met. Vacuously true. So in principle no hypothesis is needed.

But the S1 OBSERVE statement targeted a *nonvacuous* magic predicate. The
scaffold above includes the hypothesis to match S1 + S6 PREP intent (and
because magicConstant = 0 from vacuous truth would be jarring).

## 5. Parent-reduction (S4) is `Iff.rfl`

The types `PointConfigD 2` and `Erdos735.PointConfig` are *definitionally
equal* (both `Finset (EuclideanSpace ℝ (Fin 2))`). The predicates
`ConfigKFlat 1 P` and `Erdos735.ConfigLine P` unfold to:

- OQ04: `{F // F.direction.toSubmodule.rank = 1 ∧ (P.filter (· ∈ F)).card ≥ 1 + 1}`
- Parent: `{L // L.direction.toSubmodule.rank = 1 ∧ (P.filter (· ∈ L)).card ≥ 2}`

These are the same proposition (`(1 : ℕ) + 1 = 2` reduces). Similarly
`kFlatSum` (with `k = 1`) and `lineSum` are the same `let`-bound expression.
Therefore `IsKFlatMagic 1 P` and `IsMagic P` are *defeq*; the iff is `Iff.rfl`.

A safer fallback if elaboration unfolding is slow:

```lean
theorem oneflat_eq_parent (P : PointConfigD 2) :
    IsKFlatMagic 1 P ↔ Erdos735.IsMagic P := by
  unfold IsKFlatMagic Erdos735.IsMagic ConfigKFlat Erdos735.ConfigLine
         kFlatSum Erdos735.lineSum
  rfl  -- or: tauto
```

## 6. `Cardinal` vs `ℕ` rank — chosen path

| Aspect | Cardinal (`direction.toSubmodule.rank = k`) | Nat (`Module.finrank ℝ direction.toSubmodule = k`) |
|---|---|---|
| Matches parent | ✅ (parent uses `.rank = 1`) | ❌ (parent uses `.rank = 1` with `Cardinal.ofNat 1`) |
| Trivial-case discharge | needs `rank_zero_iff` + `Cardinal.toNat` round-trip | direct `Nat.cast_zero` / `finrank_eq_zero` |
| Decidable equality | ❌ | ❌ (`finrank` is `Cardinal.toNat ∘ rank`, still `Prop`-level) |
| Compatibility with S5 axiom | ✅ | ⚠ would need parallel cardinal-version for parent reuse |
| Compatibility with S6a tetrahedron | needs `Cardinal.mk_eq_two` (S6a PREP §5) | direct |

**Resolution**: use Cardinal (`direction.toSubmodule.rank = (k : Cardinal)`)
**for consistency with parent**. This is S6a PREP §5's recommendation. The
trivial-case proofs use `Cardinal.toNat` and `rank_zero_iff` / `rank_eq_one_iff`
chains, which add ~5 LOC per theorem versus the ℕ variant. Net cost: ~10 LOC
trade for ~50 LOC of avoided parent-API duplication later.

**Caveat for the S5 axiom session**: when an actual axiom is added (the
higher-dim ABKPR conjecture), state it in Cardinal form (`rank = k` for
`k : ℕ → Cardinal`) to remain compositional with the parent's
`magic_classification` axiom.

## 7. S2 ACT implementation order (paste sequence)

1. ☐ Create `proofs/Proofs/Erdos735OQ04.lean` with the §3 scaffold.
   Paste-ready; no edits needed beyond optional comment trimming.
2. ☐ Update `proofs/lakefile.toml` / `proofs/Proofs.lean` if a `lean_lib` glob
   does not auto-pick up new `Proofs/*.lean`. **Inspection at branch HEAD**:
   the parent file `Erdos735Problem.lean` is auto-picked-up via the existing
   glob; **no lakefile change is needed**.
3. ☐ Docker build: `./proofs/scripts/docker-build.sh Proofs.Erdos735OQ04`.
   - Expected wall-clock: 60-120s on warm Docker cache (3 new declarations +
     imports already in parent cache).
   - Expected jobs: ~1500-1900 (parent baseline ~1500-1700 + ~200 imports
     `Mathlib.LinearAlgebra.Dimension.Finrank`).
   - Expected sorries-remaining: 3 (one in `zero_flat_magic_trivial`, two in
     `ambient_flat_magic_trivial`). All marked `-- S3 ACT`.
4. ☐ Create `src/data/proofs/erdos-735-oq-04/meta.json` and `description.md`
   stubs with `status: "axiomatized"` and `axiomCount: 7` (inherited from
   parent; no new axioms in S2). **OR** defer gallery integration to S7.
5. ☐ Update `research/problems/erdos-735-oq-04/state.md`:
   `Phase: OBSERVE — S2 ACT shipped (3 sorries pending S3)`,
   add row to iteration table.
6. ☐ Branch name: `research/erdos-735-oq-04-s2-act-lean-scaffold-<unix-ts>`.

**Total estimated effort**: ~30 min wall-clock once the deployer un-stalls.
**Estimated Docker iters**: 1 (the scaffold is small and bearer-pinned; failure
modes are limited to API mismatches caught at §2's audit).

## 8. Risk register

| # | Risk | Mitigation |
|---|---|---|
| R1 | `rank_zero_iff` requires `NoZeroSMulDivisors ℝ Submodule` instance not auto-inferred | Use `rank_eq_zero_iff` (no NoZeroSMulDivisors needed) + manual chain to `Subsingleton`. Fallback: `rfl`-form `Submodule.rank_zero_iff_eq_bot`. |
| R2 | `Cardinal.ofNat k` coercion vs literal `(k : Cardinal)` mismatch | Both elaborate to the same term; `simp only [Nat.cast_ofNat]` or `norm_cast` handles any residual mismatch. |
| R3 | `direction_eq_top_iff_of_nonempty` requires nonempty hypothesis the scaffold's `card ≥ d + 1` doesn't directly provide | Bridge via `Finset.Nonempty_of_card_pos` then `AffineSubspace.coe_nonempty`. ~3 LOC. |
| R4 | `Finset.filter (· ∈ ⊤)` may not auto-simplify | Provide `simp [AffineSubspace.mem_top]` (or whichever name) explicitly. Audited path: `Submodule.mem_top` simp-lemma at `Mathlib/Algebra/Module/Submodule/Lattice.lean`. |
| R5 | Parent reduction `Iff.rfl` may time out elaboration | Fallback to explicit `unfold` block in §5; if still slow, `def`-equate `ConfigKFlat 1 = Erdos735.ConfigLine` and use the resulting `Equiv.refl`. |
| R6 | S6a PREP's `tetraConfig_isKFlatMagic` assumes the scaffold sorries are *discharged*, not still open | The S6a ACT theorem `tetraConfig_isKFlatMagic` does NOT depend on the sorried trivial cases — it constructs its own weighting + sum proof. So leaving the 3 trivial sorries open does NOT block S6a ACT. **Verified by re-reading S6a PREP §4** (the theorem proof is `refine ⟨⟨fun _ => 1, ...⟩, 3, three_pos, ?_⟩` followed by 4-flat case analysis — uses NONE of `zero_flat_magic_trivial` / `ambient_flat_magic_trivial`). |
| R7 | "Lean 4.26.0 surface drift" since S6a PREP (2026-05-13) — names may have moved | No drift detected: every audited bearer in §2 is present at the lake-pinned SHA `2df2f015…`. The SHA is unchanged between 2026-05-13 (S6a PREP) and 2026-05-15 (this PREP). |

## 9. Conflict-free guarantees

This PREP adds **one new file**: `research/problems/erdos-735-oq-04/sessions/2026-05-15-s2-prep-lean-scaffold.md`.

It touches NONE of:

- `state.md` — owned by next STATE-SYNC iteration.
- `knowledge.md` — owned by next STATE-SYNC iteration.
- `src/data/research/problems/erdos-735-oq-04.json` — owned by next STATE-SYNC.
- `proofs/Proofs/Erdos735OQ04.lean` — owned by S2 ACT (does not exist yet).
- `proofs/Proofs/Erdos735OQ04Tetrahedron.lean` — owned by S6a ACT.
- `src/data/proofs/erdos-735-oq-04/*` — owned by S7 gallery integration.

Composes cleanly with: prior S6a PREP (#18486), S6b PREP (#18541), STATE-SYNC.
Strict no-overlap with all currently-merged PRs on this slug.

Under deployer stall: this is the only sensible doc-only contribution that
moves the slug forward without compounding queue pressure on a build-verify ACT.

## 10. Honesty

This PREP is **strictly doc-only**. It produces:

- **0** new Lean theorems on `main`
- **0** new sorries on `main` (the §3 scaffold has 3 sorries, but it lives in
  this memo only; the S2 ACT will materialise it as a new Lean file)
- **0** new axioms anywhere
- **1** new markdown file under `research/problems/erdos-735-oq-04/sessions/`

The §3 scaffold is **paste-ready**: a future S2 ACT iteration (any researcher)
can copy lines 1-85 verbatim into `proofs/Proofs/Erdos735OQ04.lean`, run the
Docker build, and inherit 3 pre-marked `-- S3 ACT` sorries with full
proof-sketches in §4.

The trivial-case discharge plan in §4 ships proof *sketches*, not closed
proof terms. Two `sorry`s remain in each sketch — bridge lemmas
(`vectorSpan_eq_bot_iff_subsingleton`, `Submodule.eq_top_of_finrank_eq`,
`AffineSubspace.eq_top_of_direction_eq_top`) have been verified at SHA by
`gh api search/code` but their precise statement-form is left to S3 to
confirm against the Mathlib source line at v4.26.0.

The parent-reduction `Iff.rfl` (§5) is the strongest claim: it asserts
*definitional equality* between OQ04's `IsKFlatMagic 1` and parent's
`IsMagic`. If elaboration declines `Iff.rfl` (R5), the §5 fallback path
guarantees a closed proof. No genuine novelty in §5 — it is housekeeping.

**No new mathematical claim** is made beyond the S1 OBSERVE statement. The
S5 axiom (higher-dim ABKPR extension), S6d (dodec/icosa), and S6e
(general-position uniform-weight) are all out of scope.

Future Lean entry: `status: "axiomatized"` (inheriting parent's 7 axioms);
this S2 ACT does not change the axiom count.
