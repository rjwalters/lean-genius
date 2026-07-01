/-
# Erdős Problem #101 — Extremal Four-Point-Line Configurations are Steiner Systems

Follow-up to Erdős Problem #101 (`Erdos101Problem.lean`), open question OQ-02:
*"Can the Solymosi–Stojaković construction be improved to Ω(n² / polylog(n)),
or is there a barrier?"*

The parent file proves the sharp **pair-packing upper bound**

    fourPointLineCount P ≤ n(n-1)/12      (`improved_upper_bound`)

for any planar point set `P` on `n` points with no five collinear.  This bound is
attained exactly when the four-point lines **perfectly cover** the pairs of points,
i.e. when every 2-element subset of `P` lies on a (necessarily unique) four-point
line.  Such a configuration is precisely a **Steiner system `S(2,4,n)`** realized in
the plane.

This file records the classical **necessary conditions** that any such extremal
configuration must satisfy — a genuine arithmetic *barrier*:

* `extremal_covers_all_pairs` : attaining the bound ⇒ every pair of points lies on a
  four-point line (existence half of the Steiner property);
* `extremal_pair_covered_uniquely` : that line is unique (Steiner `S(2,4,n)`);
* `twelve_dvd_of_extremal`      : `12 ∣ n(n-1)`  (integrality of the block count);
* `three_dvd_of_extremal`       : `3 ∣ (n-1)`    (integrality of the replication number);
* **`extremal_forces_mod_twelve`** : `n ≡ 1 or 4 (mod 12)`.

These are exactly the divisibility conditions for the existence of a Steiner system
`S(2,4,n)` (Hanani).  So a plane configuration meeting the `n(n-1)/12` bound can only
exist for `n ≡ 1, 4 (mod 12)`; for all other `n` there is a hard combinatorial
obstruction *before* any geometry is invoked.

The extremal hypothesis is phrased as `6 * fourPointLineCount P = n.choose 2`, i.e.
the `6` pairs contributed by each four-point line exactly exhaust the `C(n,2)` pairs.

All results are axiom-free (0 sorries, 0 axioms).
-/

import Mathlib
import Proofs.Erdos101Problem

namespace Erdos101ExtremalSteiner

open Classical

/-! ## Part C — the pure arithmetic core

Given `3 ∣ (n-1)` (replication integer) and `12 ∣ n(n-1)` (block-count integer),
the residue of `n` mod `12` is forced to `1` or `4`.  Everything reduces mod `12`;
the nonlinear product `n(n-1)` is handled by `Nat.mul_mod` followed by a finite
residue case-split. -/

/-- If `3 ∣ (n-1)` and `12 ∣ n(n-1)` for `n ≥ 1`, then `n ≡ 1 or 4 (mod 12)`. -/
lemma mod12_of_extremal (n : ℕ) (hn : 1 ≤ n)
    (h3 : 3 ∣ (n - 1)) (h12 : 12 ∣ n * (n - 1)) :
    n % 12 = 1 ∨ n % 12 = 4 := by
  -- `n(n-1) ≡ 0 (mod 12)` as a plain modular fact.
  have e0 : n * (n - 1) % 12 = 0 := by omega
  -- Reduce the product modulo 12.
  have e1 : n * (n - 1) % 12 = (n % 12) * ((n - 1) % 12) % 12 := Nat.mul_mod _ _ _
  rw [e0] at e1
  -- Express `(n-1) mod 12` through `n mod 12`.
  have hb : (n - 1) % 12 = (n % 12 + 11) % 12 := by omega
  rw [hb] at e1
  -- The replication constraint modulo 3.
  have h3r : (n % 12) % 3 = 1 := by omega
  set r := n % 12 with hr
  have hrlt : r < 12 := by rw [hr]; exact Nat.mod_lt _ (by norm_num)
  -- Finite check over the 12 residues.
  interval_cases r <;> omega

/-! ## Part A — block-count integrality: `12 ∣ n(n-1)`

Each four-point line accounts for `C(4,2) = 6` pairs, so attaining the bound means
`6 · L = C(n,2) = n(n-1)/2`, whence `n(n-1) = 12 · L`. -/

/-- If the four-point lines attain the pair-packing bound `6·L = C(n,2)`, then
`12 ∣ n(n-1)`; the number of lines `L` is the block count of a `2-(n,4,1)` design. -/
lemma twelve_dvd_of_extremal (P : PlanarPointSet)
    (hExt : 6 * fourPointLineCount P = P.points.card.choose 2) :
    12 ∣ P.points.card * (P.points.card - 1) := by
  set n := P.points.card with hn_def
  have hchoose : n.choose 2 = n * (n - 1) / 2 := Nat.choose_two_right n
  -- `n(n-1)` is even.
  have heven : 2 ∣ n * (n - 1) := by
    rcases Nat.even_or_odd n with he | ho
    · exact he.two_dvd.mul_right _
    · have h1 : 2 ∣ (n - 1) := by
        rcases ho with ⟨k, hk⟩; omega
      exact h1.mul_left _
  -- `2 · C(n,2) = n(n-1)`.
  have h2 : 2 * n.choose 2 = n * (n - 1) := by
    rw [hchoose]; omega
  -- `n(n-1) = 2·(6L) = 12L`.
  refine ⟨fourPointLineCount P, ?_⟩
  rw [← h2, ← hExt]; ring

/-! ## Steiner property: attaining the bound perfectly covers the pairs

Rebuild the disjoint pair-packing of the parent's `improved_upper_bound`; when
`6·L = C(n,2)` the packing is *perfect*, so its blocks (the four-point lines)
cover every 2-subset of the point set. -/

/-- Membership unfolding for `fourCollinearFamily`. -/
private lemma mem_family_iff (P : PlanarPointSet) (S : Finset (ℝ × ℝ)) :
    S ∈ fourCollinearFamily P ↔
      S ⊆ P.points ∧ S.card = 4 ∧
      ∃ a b : ℝ × ℝ, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ ∀ p ∈ S, collinear a b p := by
  unfold fourCollinearFamily
  simp only [Finset.mem_filter, Finset.mem_powerset]

/-- **Extremal ⇒ every pair covered.**  If `6·L = C(n,2)`, then every 2-element
subset of `P.points` is contained in some four-point line.  (Existence half of the
Steiner `S(2,4,n)` property.) -/
theorem extremal_covers_all_pairs (P : PlanarPointSet) (hP : NoFiveCollinear P)
    (hExt : 6 * fourPointLineCount P = P.points.card.choose 2)
    (T : Finset (ℝ × ℝ)) (hT : T ∈ P.points.powersetCard 2) :
    ∃ S ∈ fourCollinearFamily P, T ⊆ S := by
  set F := fourCollinearFamily P with hF_def
  -- pair-set of each block
  set pairSet : Finset (ℝ × ℝ) → Finset (Finset (ℝ × ℝ)) :=
    fun S => S.powersetCard 2 with hps
  -- each block contributes exactly 6 pairs
  have hpair_card : ∀ S ∈ F, (pairSet S).card = 6 := by
    intro S hS
    have hprop := (mem_family_iff P S).mp hS
    show (S.powersetCard 2).card = 6
    rw [Finset.card_powersetCard, hprop.2.1]; decide
  -- pair-sets are pairwise disjoint (distinct blocks share ≤ 1 point)
  have hpair_disj : ∀ S₁ ∈ F, ∀ S₂ ∈ F, S₁ ≠ S₂ →
      Disjoint (pairSet S₁) (pairSet S₂) := by
    intro S₁ hS₁ S₂ hS₂ hne
    obtain ⟨hsub₁, hc₁, a₁, b₁, ha₁, hb₁, hab₁, hcol₁⟩ := (mem_family_iff P S₁).mp hS₁
    obtain ⟨hsub₂, hc₂, a₂, b₂, ha₂, hb₂, hab₂, hcol₂⟩ := (mem_family_iff P S₂).mp hS₂
    apply powersetCard2_disjoint
    exact four_collinear_overlap_small P hP S₁ S₂ hsub₁ hsub₂ hc₁ hc₂ hne
      a₁ b₁ hab₁ ha₁ hb₁ hcol₁ a₂ b₂ hab₂ ha₂ hb₂ hcol₂
  -- the union of pair-sets sits inside all 2-subsets of P.points
  have hbU_sub : F.biUnion pairSet ⊆ P.points.powersetCard 2 := by
    intro U hU
    rw [Finset.mem_biUnion] at hU
    obtain ⟨S, hS, hU_S⟩ := hU
    have hsub := (mem_family_iff P S).mp hS |>.1
    have h2 := Finset.mem_powersetCard.mp hU_S
    exact Finset.mem_powersetCard.mpr ⟨h2.1.trans hsub, h2.2⟩
  -- cardinalities
  have hbU_card : (F.biUnion pairSet).card = 6 * F.card := by
    rw [Finset.card_biUnion (fun S hS T hT hne => hpair_disj S hS T hT hne),
        Finset.sum_const_nat (fun S hS => hpair_card S hS)]
    ring
  have hLF : F.card = fourPointLineCount P := (fourPointLineCount_eq_family P).symm
  have hpc_card : (P.points.powersetCard 2).card = P.points.card.choose 2 :=
    Finset.card_powersetCard 2 P.points
  -- perfect packing: the union is *all* 2-subsets
  have hunion : F.biUnion pairSet = P.points.powersetCard 2 := by
    apply Finset.eq_of_subset_of_card_le hbU_sub
    rw [hpc_card, hbU_card, hLF, hExt]
  -- extract the covering block for T
  have hT' : T ∈ F.biUnion pairSet := by rw [hunion]; exact hT
  rw [Finset.mem_biUnion] at hT'
  obtain ⟨S, hS, hT_S⟩ := hT'
  exact ⟨S, hS, (Finset.mem_powersetCard.mp hT_S).1⟩

/-- **Extremal ⇒ each pair covered by a unique block** — the configuration is a
Steiner system `S(2,4,n)`. -/
theorem extremal_pair_covered_uniquely (P : PlanarPointSet) (hP : NoFiveCollinear P)
    (hExt : 6 * fourPointLineCount P = P.points.card.choose 2)
    (T : Finset (ℝ × ℝ)) (hT : T ∈ P.points.powersetCard 2) :
    ∃! S, S ∈ fourCollinearFamily P ∧ T ⊆ S := by
  obtain ⟨S, hS, hTS⟩ := extremal_covers_all_pairs P hP hExt T hT
  refine ⟨S, ⟨hS, hTS⟩, ?_⟩
  rintro S' ⟨hS', hTS'⟩
  by_contra hne
  -- T ⊆ S ∩ S' with |T| = 2 forces the blocks to share ≥ 2 points
  obtain ⟨hsub, hc, a, b, ha, hb, hab, hcol⟩ := (mem_family_iff P S).mp hS
  obtain ⟨hsub', hc', a', b', ha', hb', hab', hcol'⟩ := (mem_family_iff P S').mp hS'
  have hTcard : T.card = 2 := (Finset.mem_powersetCard.mp hT).2
  have hle := four_collinear_overlap_small P hP S' S hsub' hsub hc' hc
    hne a' b' hab' ha' hb' hcol' a b hab ha hb hcol
  have hTsub : T ⊆ S' ∩ S := Finset.subset_inter hTS' hTS
  have : (2 : ℕ) ≤ (S' ∩ S).card := hTcard ▸ Finset.card_le_card hTsub
  omega

/-! ## Part B — replication integrality: `3 ∣ (n-1)`

Fix a point `p`.  The pairs `{p,q}` (for `q ≠ p`) are perfectly covered, so the
`n-1` points `q ≠ p` are partitioned into the three-point sets `S \ {p}` ranging
over the four-point lines `S` through `p`.  Hence `3 ∣ (n-1)`. -/

/-- If the four-point lines attain the bound, then `3 ∣ (n-1)`: the replication
number `(n-1)/3` (four-point lines through any fixed point) is an integer. -/
theorem three_dvd_of_extremal (P : PlanarPointSet) (hP : NoFiveCollinear P)
    (hExt : 6 * fourPointLineCount P = P.points.card.choose 2) :
    3 ∣ (P.points.card - 1) := by
  -- pick a point p
  obtain ⟨p, hp⟩ := Finset.card_pos.mp P.size_pos
  set FP := fourCollinearThrough P p with hFP
  set eraseMap : Finset (ℝ × ℝ) → Finset (ℝ × ℝ) := fun S => S.erase p with hem
  -- membership facts for FP
  have hFP_prop : ∀ S ∈ FP, S ⊆ P.points ∧ S.card = 4 ∧ p ∈ S ∧
      ∃ a b : ℝ × ℝ, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ ∀ q ∈ S, collinear a b q := by
    intro S hS
    rw [hFP] at hS
    unfold fourCollinearThrough at hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    exact ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2⟩
  -- each block through p, minus p, has 3 points
  have herase_card : ∀ S ∈ FP, (eraseMap S).card = 3 := by
    intro S hS
    obtain ⟨_, hcard, hpS, _⟩ := hFP_prop S hS
    show (S.erase p).card = 3
    rw [Finset.card_erase_of_mem hpS, hcard]
  -- images land in P.points.erase p
  have herase_sub : ∀ S ∈ FP, eraseMap S ⊆ P.points.erase p := by
    intro S hS x hx
    obtain ⟨hsub, _, _, _⟩ := hFP_prop S hS
    have hxS := Finset.mem_of_mem_erase hx
    have hxne := Finset.ne_of_mem_erase hx
    exact Finset.mem_erase.mpr ⟨hxne, hsub hxS⟩
  -- pairwise disjoint (two lines through p sharing another point share ≥ 2 points)
  have herase_disj : ∀ S₁ ∈ FP, ∀ S₂ ∈ FP, S₁ ≠ S₂ →
      Disjoint (eraseMap S₁) (eraseMap S₂) := by
    intro S₁ hS₁ S₂ hS₂ hne
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    have hxne : x ≠ p := Finset.ne_of_mem_erase hx₁
    have hxS₁ := Finset.mem_of_mem_erase hx₁
    have hxS₂ := Finset.mem_of_mem_erase hx₂
    obtain ⟨hsub₁, hc₁, hp₁, a₁, b₁, ha₁, hb₁, hab₁, hcol₁⟩ := hFP_prop S₁ hS₁
    obtain ⟨hsub₂, hc₂, hp₂, a₂, b₂, ha₂, hb₂, hab₂, hcol₂⟩ := hFP_prop S₂ hS₂
    have hge : 2 ≤ (S₁ ∩ S₂).card := by
      have hpx : p ≠ x := fun h => hxne h.symm
      have hpair : ({p, x} : Finset (ℝ × ℝ)).card = 2 := Finset.card_pair hpx
      have hsub : ({p, x} : Finset (ℝ × ℝ)) ⊆ S₁ ∩ S₂ := by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hp₁, hp₂⟩
        · exact Finset.mem_inter.mpr ⟨hxS₁, hxS₂⟩
      calc (2 : ℕ) = ({p, x} : Finset (ℝ × ℝ)).card := hpair.symm
        _ ≤ (S₁ ∩ S₂).card := Finset.card_le_card hsub
    have hle := four_collinear_overlap_small P hP S₁ S₂ hsub₁ hsub₂ hc₁ hc₂ hne
      a₁ b₁ hab₁ ha₁ hb₁ hcol₁ a₂ b₂ hab₂ ha₂ hb₂ hcol₂
    omega
  -- coverage: every q ≠ p is reached (this is where extremality is used)
  have hcover : P.points.erase p ⊆ FP.biUnion eraseMap := by
    intro x hx
    have hxne : x ≠ p := Finset.ne_of_mem_erase hx
    have hxP : x ∈ P.points := Finset.mem_of_mem_erase hx
    -- the pair {p, x}
    have hpair_card : ({p, x} : Finset (ℝ × ℝ)).card = 2 :=
      Finset.card_pair (fun h => hxne h.symm)
    have hpair_sub : ({p, x} : Finset (ℝ × ℝ)) ⊆ P.points := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hp
      · exact hxP
    have hpair_mem : ({p, x} : Finset (ℝ × ℝ)) ∈ P.points.powersetCard 2 :=
      Finset.mem_powersetCard.mpr ⟨hpair_sub, hpair_card⟩
    obtain ⟨S, hS, hTS⟩ := extremal_covers_all_pairs P hP hExt _ hpair_mem
    have hpS : p ∈ S := hTS (by simp)
    have hxS : x ∈ S := hTS (by simp)
    have hS_FP : S ∈ FP := mem_fourCollinearThrough_of_mem_family P S hS p hpS
    rw [Finset.mem_biUnion]
    exact ⟨S, hS_FP, Finset.mem_erase.mpr ⟨hxne, hxS⟩⟩
  -- assemble: (n-1) = |P.points.erase p| = 3 * |FP|
  have hunion : FP.biUnion eraseMap = P.points.erase p := by
    apply Finset.Subset.antisymm _ hcover
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨S, hS, hxS⟩ := hx
    exact herase_sub S hS hxS
  have hcard_biU : (FP.biUnion eraseMap).card = 3 * FP.card := by
    rw [Finset.card_biUnion (fun S hS T hT hne => herase_disj S hS T hT hne),
        Finset.sum_const_nat (fun S hS => herase_card S hS)]
    ring
  have herase_p : (P.points.erase p).card = P.points.card - 1 :=
    Finset.card_erase_of_mem hp
  have hkey : P.points.card - 1 = 3 * FP.card := by
    rw [← herase_p, ← hunion, hcard_biU]
  exact ⟨FP.card, hkey⟩

/-! ## Main theorem -/

/-- **Extremal configurations satisfy the Steiner divisibility conditions.**

If a planar point set `P` on `n` points with no five collinear attains the sharp
pair-packing bound `fourPointLineCount P = n(n-1)/12` — equivalently
`6 · fourPointLineCount P = C(n,2)`, i.e. every pair of points lies on a four-point
line — then

    n ≡ 1  or  n ≡ 4   (mod 12).

These are exactly Hanani's necessary conditions for the existence of a Steiner
system `S(2,4,n)`.  Hence the `n(n-1)/12` upper bound is *unattainable* whenever
`n ≢ 1, 4 (mod 12)` — an arithmetic barrier that holds before any geometric input. -/
theorem extremal_forces_mod_twelve (P : PlanarPointSet) (hP : NoFiveCollinear P)
    (hExt : 6 * fourPointLineCount P = P.points.card.choose 2) :
    P.points.card % 12 = 1 ∨ P.points.card % 12 = 4 :=
  mod12_of_extremal _ P.size_pos
    (three_dvd_of_extremal P hP hExt) (twelve_dvd_of_extremal P hExt)

/-- Contrapositive convenience form: for `n ≢ 1, 4 (mod 12)` no no-five-collinear
configuration meets the pair-packing bound. -/
theorem not_extremal_of_mod_twelve (P : PlanarPointSet) (hP : NoFiveCollinear P)
    (hmod : P.points.card % 12 ≠ 1 ∧ P.points.card % 12 ≠ 4) :
    6 * fourPointLineCount P ≠ P.points.card.choose 2 := by
  intro hExt
  rcases extremal_forces_mod_twelve P hP hExt with h | h
  · exact hmod.1 h
  · exact hmod.2 h

end Erdos101ExtremalSteiner
