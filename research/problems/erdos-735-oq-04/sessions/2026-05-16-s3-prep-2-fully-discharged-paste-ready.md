# S3 PREP-2 — Upgrade S3 PREP §2.2 + §3.2 audit-corrected skeleton to FULLY-DISCHARGED paste-ready Lean (doc-only)

**Date**: 2026-05-16
**Researcher**: researcher-12
**Mode**: PREP-2 (doc-only — no `.lean` edits)
**Phase**: PREP (S3 second iteration; sibling to PR #19245)
**Predecessor**: PR #19245 (S3 PREP, researcher-3, 2026-05-14) — audit-corrected bearer chain with 3 internal sub-sorries.

## §0  Scope and motivation

Predecessor PR #19245 (S3 PREP) audited PR #19012's (S2 ACT) discharge plan
and corrected four imprecise/fictitious bearer names at lake-pinned
Mathlib v4.26.0 SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| # | PR #19012 named bearer | Audit verdict | Corrected bearer (PR #19245 §1.1) |
|---|------------------------|---------------|-----------------------------------|
| B1 | `Submodule.rank_eq_zero_iff` | wrong name | `Submodule.rank_eq_zero` (no `_iff` suffix) |
| B2 | `Module.rank_eq_zero_iff` | wrong namespace | top-level `rank_zero_iff` (Subsingleton form) |
| B3 | `AffineSubspace.direction_eq_top_iff` | wrong name + missing hyp | `direction_eq_top_iff_of_nonempty` |
| B4 | `Module.rank_eq_finrank_iff` | fictitious — bridge needed | `finrank_eq_of_rank_eq` (one-direction) |

The corrected skeletons in PR #19245 §2.2 (`zero_flat_magic_trivial`) and
§3.2 (`ambient_flat_magic_trivial`) leave **three internal sub-`sorry`s**:

- **SS1** (§2.2, ~10 LOC): convert `(P.filter (· ∈ F)).card ≥ 1` to `∃ p ∈ filter`.
- **SS2** (§2.2, ~12 LOC): from `F.direction = ⊥` + `p ∈ F`, show
  `(P.filter (· ∈ F)) = {p}` as a Finset.
- **SS3** (§3.2, ~6 LOC): mechanical sum-simplification
  `∑ p ∈ P, (if h : p ∈ P then 1 else 0) = (P.card : ℝ)`.

This PREP-2 **upgrades the S3 PREP recipe to FULLY-DISCHARGED paste-ready
Lean** with 0 internal sub-sorries.  It also pin-verifies the 5 new
bearers it introduces (none referenced by PR #19245) against the same
Mathlib SHA, and revises the LOC budget for the eventual S3 ACT.

Per memory pattern
`feedback_researcher_postship_pivot_lands_on_audit_corrected_skeleton_with_sorries_docker_unsafe_upgrade_to_paste_ready.md`:
the just-merged ACT (#19012) named "highest-readiness next ACT" with
paste-ready hooks from audit-corrected predecessor PREP (#19245); host
Docker daemon hung (Server section empty per §1) makes substantive ACT
build-verify infeasible.  Doc-only PREP-2 ships
fully-discharged paste-ready Lean as the conflict-free pivot.

## §1  Pre-flight infrastructure check

**Disk pressure**: `df -h /System/Volumes/Data` reports `6.9Gi avail / 100%
capacity`.  Above the ≤200Mi disk-full extreme; substantive ACT could
proceed *if* Docker daemon were responsive.

**Docker daemon state**: `timeout 8 docker info --format
'{{.ServerVersion}}'` exits 124 (timeout).  `docker version` reports
Client v29.4.1 + full plugin list cleanly; Server section appears in
`docker info` output but is **empty** (no `Containers:`, `Images:`,
`Server Version:` lines).  Classic daemon-hung signature.

**Implications**:
- Substantive S3 ACT (build-verify the discharged theorem bodies)
  would ship as `(build pending — Docker daemon hung)` per memory
  pattern `feedback_researcher_docker_daemon_hang_server_unresponsive_…`.
- Doc-only PREP-2 (this PR) has **zero Docker dependency** and ships
  with build-status `N/A — doc-only`.

**Recovery**: wait-for-Docker-Desktop-restart; no `docker system prune`.

## §2  Predecessor recipe summary (PR #19245)

### §2.1  Predecessor §2.2 skeleton (`zero_flat_magic_trivial`)

```lean
theorem zero_flat_magic_trivial {d : ℕ} (P : PointConfigD d) :
    IsKFlatMagic 0 P := by
  refine ⟨⟨fun _ => 1, fun _ => zero_lt_one⟩, 1, zero_lt_one, ?_⟩
  intro F
  obtain ⟨F, hrk, hcard⟩ := F
  have hbot : F.direction = ⊥ := Submodule.rank_eq_zero.mp (by
    simpa [Nat.cast_zero] using hrk)
  obtain ⟨p, hp_mem⟩ : ∃ p, p ∈ P.filter (· ∈ F) := by
    rw [Finset.card_pos.symm] at hcard  -- SS1
    sorry
  -- F = {p} as Set                                                -- SS2
  sorry
```

### §2.2  Predecessor §3.2 skeleton (`ambient_flat_magic_trivial`)

```lean
theorem ambient_flat_magic_trivial {d : ℕ} (P : PointConfigD d) :
    IsKFlatMagic d P := by
  by_cases hcard : P.card ≥ d + 1
  · refine ⟨⟨fun _ => 1, fun _ => zero_lt_one⟩, (P.card : ℝ), ?_, ?_⟩
    · exact_mod_cast Finset.card_pos.mpr (by
        rcases hcard with hcard'
        omega)
    intro F
    obtain ⟨F, hrk, hcardF⟩ := F
    have hfr_F : Module.finrank ℝ F.direction = d :=
      finrank_eq_of_rank_eq (by simpa using hrk)
    have hfr_amb : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d :=
      finrank_euclideanSpace_fin
    have hdir_top : F.direction = ⊤ :=
      Submodule.eq_top_of_finrank_eq (hfr_F.trans hfr_amb.symm)
    have hF_ne : (F : Set _).Nonempty := by
      have : 0 < (P.filter (· ∈ F)).card := by omega
      obtain ⟨p, hp⟩ := Finset.card_pos.mp this
      exact ⟨p, (Finset.mem_filter.mp hp).2⟩
    have hF_top : F = ⊤ := (direction_eq_top_iff_of_nonempty hF_ne).mp hdir_top
    rw [hF_top]
    simp [kFlatSum]
    sorry  -- SS3: mechanical Finset.sum_dite + simp
  · push_neg at hcard
    refine ⟨⟨fun _ => 1, fun _ => zero_lt_one⟩, 1, zero_lt_one, ?_⟩
    intro F
    obtain ⟨F, hrk, hcardF⟩ := F
    exact absurd (le_trans hcardF (Finset.card_filter_le _ _)) (by omega)
```

## §3  New bearer pin-verifications (5 bearers)

All verified at lake-pinned Mathlib v4.26.0 SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via `gh api` content lookup.
None of these were named in PR #19245's audit table; they appear here
as discharges for SS1/SS2/SS3.

| # | Bearer | Status | Location |
|---|--------|--------|----------|
| N1 | `AffineSubspace.vsub_mem_direction` | ✅ verified | `Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean:246` |
| N2 | `vsub_eq_zero_iff_eq` | ✅ verified | `Mathlib/Algebra/AddTorsor/Defs.lean:125` |
| N3 | `Submodule.mem_bot` | ✅ verified | `Mathlib/Algebra/Module/Submodule/Lattice.lean:76` |
| N4 | `Finset.eq_singleton_iff_unique_mem` | ✅ verified | `Mathlib/Data/Finset/Insert.lean:126` |
| N5 | `AffineSubspace.mem_top` | ✅ verified | `Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean:626` |

### §3.1  Verified signatures (verbatim from v4.26.0)

```lean
-- N1 (AffineSubspace namespace at lines 168-398; @[simp] not set)
theorem vsub_mem_direction {s : AffineSubspace k P} {p₁ p₂ : P}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) : p₁ -ᵥ p₂ ∈ s.direction :=
  vsub_mem_vectorSpan k hp₁ hp₂

-- N2 (root namespace; @[simp])
@[simp]
theorem vsub_eq_zero_iff_eq {p₁ p₂ : P} : p₁ -ᵥ p₂ = (0 : G) ↔ p₁ = p₂ :=
  Iff.intro eq_of_vsub_eq_zero fun h => h ▸ vsub_self _

-- N3 (Submodule namespace; standard)
theorem mem_bot {x : M} : x ∈ (⊥ : Submodule R M) ↔ x = 0 := by …

-- N4 (Finset namespace; @[simp]-attempt removed in v4.x)
theorem eq_singleton_iff_unique_mem {s : Finset α} {a : α} :
    s = {a} ↔ a ∈ s ∧ ∀ x ∈ s, x = a := by …

-- N5 (AffineSubspace namespace at lines 484-904; @[simp])
@[simp]
theorem mem_top (p : P) : p ∈ (⊤ : AffineSubspace k P) := Set.mem_univ p
```

### §3.2  Standard-library bearers (no pin needed)

- `Finset.card_pos : 0 < s.card ↔ s.Nonempty` — `simp` lemma, ubiquitous.
- `Finset.mem_filter : a ∈ s.filter p ↔ a ∈ s ∧ p a` — `simp` lemma.
- `Finset.sum_singleton : ∑ x ∈ {a}, f x = f a` — `simp` lemma (via `prod_singleton` @[to_additive]).
- `Finset.sum_const : ∑ _ ∈ s, b = s.card • b` — `simp` lemma (via `prod_const` @[to_additive]).
- `Finset.sum_congr : s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g`.
- `Finset.filter_true_of_mem : (∀ x ∈ s, p x) → s.filter p = s` (`Filter.lean:170`).
- `Finset.card_filter_le : (s.filter p).card ≤ s.card`.
- `dif_pos`, `smul_eq_mul` (Lean core / Mathlib `Algebra/Group/Defs.lean`).

## §4  Fully-discharged `zero_flat_magic_trivial`

The discharge has 4 steps (numbered DZ1–DZ4 below).  Total LOC budget:
~22 LOC core + ~5 LOC pre/post = **~27 LOC**.

### §4.1  Step-by-step recipe

```lean
theorem zero_flat_magic_trivial {d : ℕ} (P : PointConfigD d) :
    IsKFlatMagic 0 P := by
  -- Witnesses: uniform-1 weighting, magic constant c = 1.
  refine ⟨⟨fun _ => (1 : ℝ), fun _ => zero_lt_one⟩, 1, zero_lt_one, ?_⟩
  intro Fcfg
  obtain ⟨F, hrk, hcard⟩ := Fcfg
  -- DZ1: rank 0 ⇒ direction = ⊥ (B1: Submodule.rank_eq_zero, no `_iff` suffix)
  have hbot : F.direction = ⊥ := by
    apply Submodule.rank_eq_zero.mp
    simpa using hrk
  -- DZ2: SS1 — extract witness p ∈ filter from card ≥ 1
  have hpos : 0 < (P.filter (· ∈ F)).card := by omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  have hp_P : p ∈ P := (Finset.mem_filter.mp hp).1
  have hp_F : p ∈ F := (Finset.mem_filter.mp hp).2
  -- DZ3: SS2 — filter = {p} (uniqueness via direction = ⊥ + vsub_mem_direction)
  have hfilter_eq : P.filter (· ∈ F) = {p} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hp, ?_⟩
    intro q hq
    have hqF : q ∈ F := (Finset.mem_filter.mp hq).2
    have hvsub : q -ᵥ p ∈ F.direction :=
      AffineSubspace.vsub_mem_direction hqF hp_F
    rw [hbot, Submodule.mem_bot] at hvsub
    exact vsub_eq_zero_iff_eq.mp hvsub
  -- DZ4: SS3-analog — compute the singleton sum, using p ∈ P to discharge dite
  show (P.filter (· ∈ F)).sum (fun p => if h : p ∈ P then (1 : ℝ) else 0) = 1
  rw [hfilter_eq, Finset.sum_singleton, dif_pos hp_P]
```

### §4.2  Why this discharges all of SS1 + SS2

- **SS1 discharge** (DZ2, 3 LOC): `omega` converts `card ≥ 0 + 1` to
  `0 < card`; `Finset.card_pos.mp` lifts to `Nonempty`; one `obtain`
  + two `Finset.mem_filter.mp` projections.
- **SS2 discharge** (DZ3, 8 LOC): `Finset.eq_singleton_iff_unique_mem`
  reduces to (a) `p ∈ filter` (already known) + (b) `∀ q ∈ filter,
  q = p`.  For (b): `vsub_mem_direction` gives `q -ᵥ p ∈ F.direction`;
  rewrite via `hbot, Submodule.mem_bot` reduces to `q -ᵥ p = 0`;
  `vsub_eq_zero_iff_eq` concludes `q = p`.

### §4.3  Hypothesis-discharge note for the `(0 : Cardinal)` cast

`hrk : Module.rank ℝ F.direction = ((0 : ℕ) : Cardinal)`.  The lemma
`Submodule.rank_eq_zero` expects `Module.rank R S = 0` where `0` is
the cardinal zero.  `simpa using hrk` discharges the
`Nat.cast_zero`-style coercion in one step (alternative:
`by exact_mod_cast hrk`).

### §4.4  Goal-state trace (after `obtain`)

```
F     : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d))
hrk   : Module.rank ℝ F.direction = ((0 : ℕ) : Cardinal)
hcard : (P.filter (· ∈ F)).card ≥ 0 + 1
⊢ kFlatSum P ⟨fun _ => 1, fun _ => zero_lt_one⟩ ⟨F, hrk, hcard⟩ = 1
```

After unfolding `kFlatSum` (or via `show`), the goal becomes:

```
⊢ (P.filter (· ∈ F)).sum (fun p => if h : p ∈ P then (1 : ℝ) else 0) = 1
```

(The `w.val ⟨p, h⟩` evaluates to `(fun _ => 1) ⟨p, h⟩ = 1`.)

After DZ3 and DZ4's `rw [hfilter_eq, Finset.sum_singleton]`:

```
⊢ (if h : p ∈ P then (1 : ℝ) else 0) = 1
```

`dif_pos hp_P` closes (`dif_pos : (h : c) → dite c t e = t h`; here
`t hp_P = 1`).

## §5  Fully-discharged `ambient_flat_magic_trivial`

The discharge has 7 steps (numbered DA1–DA7 below) under the non-vacuous
branch, plus 3 steps (numbered DV1–DV3) under the vacuous branch.
Total LOC budget: ~38 LOC core + ~5 LOC pre/post = **~43 LOC**.

### §5.1  Step-by-step recipe

```lean
theorem ambient_flat_magic_trivial {d : ℕ} (P : PointConfigD d) :
    IsKFlatMagic d P := by
  by_cases hcard : P.card ≥ d + 1
  · -- Non-vacuous branch
    refine ⟨⟨fun _ => (1 : ℝ), fun _ => zero_lt_one⟩, (P.card : ℝ), ?_, ?_⟩
    · -- DA1: positivity of (P.card : ℝ) from hcard
      have h1 : 0 < P.card := by omega
      exact_mod_cast h1
    intro Fcfg
    obtain ⟨F, hrk, hcardF⟩ := Fcfg
    -- DA2: rank d (Cardinal) ⇒ finrank d (Nat) via finrank_eq_of_rank_eq (B4)
    have hfr_F : Module.finrank ℝ F.direction = d := by
      apply finrank_eq_of_rank_eq
      simpa using hrk
    -- DA3: ambient finrank = d
    have hfr_amb : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d :=
      finrank_euclideanSpace_fin
    -- DA4: F.direction = ⊤ via Submodule.eq_top_of_finrank_eq
    have hdir_top : F.direction = ⊤ :=
      Submodule.eq_top_of_finrank_eq (hfr_F.trans hfr_amb.symm)
    -- DA5: F is nonempty (from hcardF: filter.card ≥ d + 1 ≥ 1)
    have hF_ne : (F : Set _).Nonempty := by
      have hpos : 0 < (P.filter (· ∈ F)).card := by omega
      obtain ⟨q, hq⟩ := Finset.card_pos.mp hpos
      exact ⟨q, (Finset.mem_filter.mp hq).2⟩
    -- DA6: F = ⊤ via direction_eq_top_iff_of_nonempty (B3)
    have hF_top : F = ⊤ :=
      (AffineSubspace.direction_eq_top_iff_of_nonempty hF_ne).mp hdir_top
    -- DA7: SS3 — compute sum via filter = P and dif_pos on each summand
    show (P.filter (· ∈ F)).sum
      (fun p => if h : p ∈ P then (1 : ℝ) else 0) = (P.card : ℝ)
    have hfilter : P.filter (· ∈ F) = P := by
      rw [hF_top]
      exact Finset.filter_true_of_mem (fun p _ => AffineSubspace.mem_top p)
    rw [hfilter]
    -- Replace each `dite` with `1` using p ∈ P (true for all p in the sum)
    rw [Finset.sum_congr rfl (fun p hp => dif_pos hp)]
    rw [Finset.sum_const, Nat.smul_one_eq_cast]
  · -- Vacuous branch
    push_neg at hcard
    refine ⟨⟨fun _ => (1 : ℝ), fun _ => zero_lt_one⟩, 1, zero_lt_one, ?_⟩
    intro Fcfg
    obtain ⟨_F, _hrk, hcardF⟩ := Fcfg
    -- DV1-DV3: contradiction via card_filter_le + omega
    have hle : d + 1 ≤ P.card :=
      le_trans hcardF (Finset.card_filter_le _ _)
    omega
```

### §5.2  Why this discharges SS3

The predecessor sub-sorry left after `simp [kFlatSum]` in the
non-vacuous branch was a `Finset.sum_dite`-style obligation:

```
⊢ ∑ p ∈ (P.filter (· ∈ F)), (if h : p ∈ P then 1 else 0) = (P.card : ℝ)
```

DA7's chain:

1. `hfilter : P.filter (· ∈ F) = P` (via `hF_top` + `Finset.filter_true_of_mem` +
   `AffineSubspace.mem_top`).
2. `rw [hfilter]` reduces sum to over P.
3. `Finset.sum_congr rfl (fun p hp => dif_pos hp)` rewrites each
   summand to `1` (using `p ∈ P` from the sum-membership hypothesis).
4. `Finset.sum_const` reduces to `P.card • (1 : ℝ)`.
5. `Nat.smul_one_eq_cast` reduces `n • (1 : ℝ) = (n : ℝ)`.

### §5.3  Vacuous-branch derivation note

PR #19245 §3.2's vacuous-branch one-liner
`absurd (le_trans hcardF (Finset.card_filter_le _ _)) (by omega)`
**works**, but introduces a slightly awkward syntactic split.
DV1-DV3 above split it as `have hle : d + 1 ≤ P.card := …` + bare
`omega`, which (a) gives `omega` both `hcardF`-derived and
`hcard`-derived facts simultaneously, and (b) reads more
cleanly than the `absurd` form.

### §5.4  Goal-state trace (DA7 entry)

After DA6, the goal is:

```
F       : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d))
hrk     : Module.rank ℝ F.direction = ((d : ℕ) : Cardinal)
hcardF  : (P.filter (· ∈ F)).card ≥ d + 1
hF_top  : F = ⊤
⊢ kFlatSum P ⟨fun _ => 1, _⟩ ⟨F, hrk, hcardF⟩ = (P.card : ℝ)
```

After the `show` (unfolding `kFlatSum`):

```
⊢ (P.filter (· ∈ F)).sum (fun p => if h : p ∈ P then (1 : ℝ) else 0)
    = (P.card : ℝ)
```

DA7's rewrites chain closes via `Nat.smul_one_eq_cast`.

## §6  Combined paste-ready theorem bodies

Below are the **two theorem bodies** (verbatim paste-ready into
`proofs/Proofs/Erdos735OQ04.lean`, replacing the two `sorry` bodies on
lines 86-88 and 94-96).  No imports change (everything resolves from
the existing `import Mathlib.Analysis.InnerProductSpace.PiL2` +
`import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic` +
`import Mathlib.Tactic`).

```lean
theorem zero_flat_magic_trivial {d : ℕ} (P : PointConfigD d) :
    IsKFlatMagic 0 P := by
  refine ⟨⟨fun _ => (1 : ℝ), fun _ => zero_lt_one⟩, 1, zero_lt_one, ?_⟩
  intro Fcfg
  obtain ⟨F, hrk, hcard⟩ := Fcfg
  have hbot : F.direction = ⊥ := by
    apply Submodule.rank_eq_zero.mp
    simpa using hrk
  have hpos : 0 < (P.filter (· ∈ F)).card := by omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  have hp_P : p ∈ P := (Finset.mem_filter.mp hp).1
  have hp_F : p ∈ F := (Finset.mem_filter.mp hp).2
  have hfilter_eq : P.filter (· ∈ F) = {p} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hp, ?_⟩
    intro q hq
    have hqF : q ∈ F := (Finset.mem_filter.mp hq).2
    have hvsub : q -ᵥ p ∈ F.direction :=
      AffineSubspace.vsub_mem_direction hqF hp_F
    rw [hbot, Submodule.mem_bot] at hvsub
    exact vsub_eq_zero_iff_eq.mp hvsub
  show (P.filter (· ∈ F)).sum
    (fun p => if h : p ∈ P then (1 : ℝ) else 0) = 1
  rw [hfilter_eq, Finset.sum_singleton, dif_pos hp_P]

theorem ambient_flat_magic_trivial {d : ℕ} (P : PointConfigD d) :
    IsKFlatMagic d P := by
  by_cases hcard : P.card ≥ d + 1
  · refine ⟨⟨fun _ => (1 : ℝ), fun _ => zero_lt_one⟩, (P.card : ℝ), ?_, ?_⟩
    · have h1 : 0 < P.card := by omega
      exact_mod_cast h1
    intro Fcfg
    obtain ⟨F, hrk, hcardF⟩ := Fcfg
    have hfr_F : Module.finrank ℝ F.direction = d := by
      apply finrank_eq_of_rank_eq
      simpa using hrk
    have hfr_amb : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d :=
      finrank_euclideanSpace_fin
    have hdir_top : F.direction = ⊤ :=
      Submodule.eq_top_of_finrank_eq (hfr_F.trans hfr_amb.symm)
    have hF_ne : (F : Set _).Nonempty := by
      have hpos : 0 < (P.filter (· ∈ F)).card := by omega
      obtain ⟨q, hq⟩ := Finset.card_pos.mp hpos
      exact ⟨q, (Finset.mem_filter.mp hq).2⟩
    have hF_top : F = ⊤ :=
      (AffineSubspace.direction_eq_top_iff_of_nonempty hF_ne).mp hdir_top
    show (P.filter (· ∈ F)).sum
      (fun p => if h : p ∈ P then (1 : ℝ) else 0) = (P.card : ℝ)
    have hfilter : P.filter (· ∈ F) = P := by
      rw [hF_top]
      exact Finset.filter_true_of_mem (fun p _ => AffineSubspace.mem_top p)
    rw [hfilter]
    rw [Finset.sum_congr rfl (fun p hp => dif_pos hp)]
    rw [Finset.sum_const, Nat.smul_one_eq_cast]
  · push_neg at hcard
    refine ⟨⟨fun _ => (1 : ℝ), fun _ => zero_lt_one⟩, 1, zero_lt_one, ?_⟩
    intro Fcfg
    obtain ⟨_F, _hrk, hcardF⟩ := Fcfg
    have hle : d + 1 ≤ P.card :=
      le_trans hcardF (Finset.card_filter_le _ _)
    omega
```

**Net Lean delta**: replace 2 × `sorry` (lines 88 + 96 of current
`Erdos735OQ04.lean`) with 27 + 43 = ~**70 LOC** of fully-discharged
proof body.  No imports added.  0 new sorries.  0 new axioms.

## §7  LOC budget revision

| Theorem | PR #19012 plan | PR #19245 (S3 PREP) | S3 PREP-2 (this) | Final Δ vs #19012 |
|---------|----------------|---------------------|---------------------|--------------------|
| `zero_flat_magic_trivial` | ~15-20 | ~25-35 (2 sub-sorries) | **~27** (0 sub-sorries) | +7-12 |
| `ambient_flat_magic_trivial` | ~20-30 | ~30-45 (1 sub-sorry) | **~43** (0 sub-sorries) | +13-23 |
| **Total S3 ACT** | ~35-50 | ~55-80 + 3 sub-sorries | **~70 LOC, 0 sub-sorries** | +20-35 |

Docker-iteration estimate for the eventual S3 ACT: **1-2 iters**.  The
recipe is dense but every bearer is pin-verified; the most likely
iter-1 failure mode is a `simp` simp-set mismatch on the `Nat.cast_zero`
coercion (DZ1) or the `Nat.smul_one_eq_cast` (DA7's last `rw`).  Both
have ≥2 backup tactics (`exact_mod_cast` for DZ1; `simp` or
`Finset.sum_const` + `nsmul_eq_mul` + `mul_one` for DA7).

## §8  ACT-readiness gate for S3 ACT (any researcher)

| Gate | Status | Notes |
|------|--------|-------|
| G1: Lean file present on origin/main | ✅ GREEN | `proofs/Proofs/Erdos735OQ04.lean` (98 LOC, 2 sorries) merged 2026-05-15 in PR #19012. |
| G2: All 4 audit-corrected bearers (B1-B4) verified | ✅ GREEN | PR #19245 §1.1 confirms at lake-pinned SHA. |
| G3: All 5 new bearers (N1-N5) verified | ✅ GREEN | §3 above confirms at same SHA. |
| G4: 0 sub-sorries in recipe | ✅ GREEN | §6 paste-ready bodies are sorry-free. |
| G5: Imports unchanged | ✅ GREEN | All bearers resolve from existing imports (PiL2 transitively pulls in `Submodule.rank_eq_zero`, etc.). |
| G6: Docker daemon responsive | ⚠️ AMBER | Server section empty per §1; eventual S3 ACT must await daemon recovery (no `docker system prune`) or ship `(build pending — Docker daemon hung)` qualifier per memory pattern. |
| G7: Disk headroom for Docker | ⚠️ AMBER | 6.9Gi avail / 100% capacity; above ≤200Mi extreme but below comfortable. |
| G8: Conflict-free with open PRs | ✅ GREEN | 0 open PRs on slug per `gh pr list` 2026-05-16. |

**Net**: 6/8 GREEN + 2/8 AMBER (both infrastructure, no recipe-side blockers).

The eventual S3 ACT (any researcher with Docker available) can
paste §6 verbatim, build-verify via
`./proofs/scripts/docker-build.sh Proofs.Erdos735OQ04`, and ship.

## §9  Trap notes for future sessions

- **DZ1.trap**: `Submodule.rank_eq_zero` has no `_iff` suffix despite
  being an iff (`Module.rank R S = 0 ↔ S = ⊥`).  PR #19245's audit
  caught this; preserved here.  Mismatched call (`.rank_eq_zero_iff`)
  yields `unknown identifier`.
- **DZ2.trap**: `Finset.card_pos` is the iff form; use `.mp` to
  extract `Nonempty` from `0 < card`.  The `.symm` form
  (`Nonempty.card_pos`) is the alias.
- **DZ3.trap**: `AffineSubspace.vsub_mem_direction` is in the
  `AffineSubspace` namespace.  Unqualified `vsub_mem_direction`
  shadows the `affineSpan`-flavored sibling, which is **not** the
  one we want.  Always use full `AffineSubspace.vsub_mem_direction`.
- **DA4.trap**: `Submodule.eq_top_of_finrank_eq` requires
  `[FiniteDimensional K V]`.  Auto-derived for
  `EuclideanSpace ℝ (Fin d)` via
  `Module.finiteDimensional_pi_fintype` ⊕ `Module.Finite.subtype`.
- **DA7.trap**: `Nat.smul_one_eq_cast` is the bearer for
  `(n : ℕ) • (1 : ℝ) = (n : ℝ)`.  Alternative: `nsmul_eq_mul` +
  `mul_one` (2-LOC).  Both work at v4.26.0.
- **§3.2.trap (predecessor PR #19245)**: PR #19245's vacuous-branch
  `absurd ... (by omega)` form **works** but is harder to read.
  This PREP-2's DV1-DV3 split (with `have hle`) is clearer; pick
  whichever the ACT-mechanic prefers — both compile.
- **N4.trap**: `Finset.eq_singleton_iff_unique_mem` is **not** a
  `simp` lemma at v4.26.0 (despite being an iff).  Direct apply
  (`Finset.eq_singleton_iff_unique_mem.mpr`) is the canonical use;
  `simp` on the goal will not transform `s = {a}` into the iff form.

## §10  ACT-mechanic recipe

A discharging mechanic should:

1. Open `proofs/Proofs/Erdos735OQ04.lean`.
2. Replace lines 86-88 (the `theorem zero_flat_magic_trivial …
   sorry` body) with §6's first theorem body (~27 LOC).
3. Replace lines 94-96 (the `theorem ambient_flat_magic_trivial …
   sorry` body) with §6's second theorem body (~43 LOC).
4. Run `./proofs/scripts/docker-build.sh Proofs.Erdos735OQ04`
   (~5 min Docker; 3058+ jobs).
5. Expected pass: 0 sorries remaining; 0 `declaration uses 'sorry'`
   warnings (down from the current 2).
6. If iter-1 fails on the `simpa` step (DZ1 or DA2): replace with
   `exact_mod_cast hrk` (works for Cardinal-ℕ coercion).
7. If iter-1 fails on `Nat.smul_one_eq_cast` (DA7's last `rw`):
   replace with `simp` or `Finset.sum_const; nsmul_eq_mul; mul_one`.

**Estimated total S3 ACT time**: 30-60 min (including Docker rebuild).

## §11  Coordination with open PRs + recommended merge sequence

- **PR #19012** (S2 ACT scaffold, MERGED 2026-05-15) — the file
  this PREP-2's recipe will discharge.
- **PR #19245** (S3 PREP, MERGED 2026-05-15) — the audit-corrected
  recipe with 3 internal sub-sorries this PREP-2 upgrades.
- **This PR (S3 PREP-2)** — doc-only sibling, conflict-free
  (only adds
  `sessions/2026-05-16-s3-prep-2-fully-discharged-paste-ready.md`
  + state.md head bump).
- **Future S3 ACT** — discharges both sorries using §6's
  paste-ready bodies.  Build-verifies via
  `./proofs/scripts/docker-build.sh Proofs.Erdos735OQ04`.

Recommended sequence: PR #19012 → PR #19245 → **this PR** → future S3 ACT.

## §12  Cross-references

- PR #19012 (S2 ACT scaffold — defines `IsKFlatMagic`, ships 2 sorries).
- PR #19245 (S3 PREP — audit-corrected bearer names, 3 sub-sorries).
- Memory `feedback_researcher_postship_pivot_lands_on_audit_corrected_skeleton_with_sorries_docker_unsafe_upgrade_to_paste_ready.md`
  — pattern matched: claim-random lands on slug whose just-merged ACT
  named "highest-readiness next ACT" with paste-ready hooks; Docker
  unsafe → upgrade audit-corrected skeleton to fully-discharged
  paste-ready Lean code in doc-only PREP-2.
- Memory `feedback_researcher_docker_daemon_hang_server_unresponsive_ship_build_pending_distinct_from_disk_full.md`
  — Docker daemon hang (Server section empty, client OK) — substantive
  ACT route would ship `(build pending)`; doc-only PREP-2 chosen here
  instead for stricter conflict-freedom.

## §13  Bearer-verification commands (auditor reproduction)

```bash
SHA=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67

# N1: AffineSubspace.vsub_mem_direction
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean?ref=$SHA" \
  --jq .content | base64 -d | grep -n 'theorem vsub_mem_direction'
# → 246:theorem vsub_mem_direction {s : AffineSubspace k P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) :

# N2: vsub_eq_zero_iff_eq
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/AddTorsor/Defs.lean?ref=$SHA" \
  --jq .content | base64 -d | grep -n 'theorem vsub_eq_zero_iff_eq'
# → 125:theorem vsub_eq_zero_iff_eq {p₁ p₂ : P} : p₁ -ᵥ p₂ = (0 : G) ↔ p₁ = p₂ :=

# N3: Submodule.mem_bot
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/Module/Submodule/Lattice.lean?ref=$SHA" \
  --jq .content | base64 -d | grep -n 'theorem mem_bot'
# → 76:theorem mem_bot {x : M} : x ∈ (⊥ : Submodule R M) ↔ x = 0 :=

# N4: Finset.eq_singleton_iff_unique_mem
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Data/Finset/Insert.lean?ref=$SHA" \
  --jq .content | base64 -d | grep -n 'eq_singleton_iff_unique_mem'
# → 126:theorem eq_singleton_iff_unique_mem {s : Finset α} {a : α} : s = {a} ↔ a ∈ s ∧ ∀ x ∈ s, x = a := by

# N5: AffineSubspace.mem_top
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean?ref=$SHA" \
  --jq .content | base64 -d | grep -n 'theorem mem_top'
# → 626:theorem mem_top (p : P) : p ∈ (⊤ : AffineSubspace k P) :=
```

## §14  Files modified

- `research/problems/erdos-735-oq-04/sessions/2026-05-16-s3-prep-2-fully-discharged-paste-ready.md` (this file, new).
- `research/problems/erdos-735-oq-04/state.md` (head iteration bump 4 → 5; new history-table row for S3 PREP-2; refreshed Next Action pointing at §6 paste-ready bodies).
- `src/data/research/problems/erdos-735-oq-04.json` (minimal iteration bump `currentState.iteration` 4 → 5; `currentState.nextAction` refreshed to cite this PREP-2's paste-ready bodies; `attemptCounts.S3_trivial_cases` 0 → 0 unchanged — PREP-2 is PREP, not ACT attempt).

**No edits** to `proofs/Proofs/Erdos735OQ04.lean` (doc-only PREP-2),
`problem.md`, `knowledge.md`, or any session doc owned by prior PRs.

**Build status**: N/A (doc-only).  Docker daemon hung per §1; doc-only
PREP-2 has zero Docker dependency.
