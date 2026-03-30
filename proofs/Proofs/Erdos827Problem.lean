/-
# Erdős Problem #827: Distinct Circumradii in General Position

Let n_k be the minimal number such that any n_k points in general position
in ℝ² must contain a subset of k points where all C(k,3) triples determine
circles of distinct radii.

Erdős (1975) asked whether n_k exists. He claimed n_k ≤ k + 2·C(k-1,2)·C(k-1,3)
in 1978, but the proof contained errors. Martinez and Roldán-Pensado corrected
the argument and showed n_k ≪ k⁹.

The problem asks to determine n_k more precisely.

Reference: https://erdosproblems.com/827

Axioms: 4 (minimalNk, minimalNk_valid, minimalNk_sharp,
  martinez_roldan_pensado)
Proved: nk_monotone (from valid + sharp + subset argument),
  nk_ge_k (from valid + parabola GP construction),
  nk_three (from valid + sharp + vacuous AllDistinctCircumradii for 3-sets)
Sorries: 0
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/- ## Points in General Position -/

/-- A point in the plane. -/
abbrev Point := ℝ × ℝ

/-- The squared distance between two points. -/
noncomputable def distSq (p q : Point) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Points are in general position: no three are collinear. -/
def GeneralPosition (S : Finset Point) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S,
    p ≠ q → q ≠ r → p ≠ r →
    (p.1 - r.1) * (q.2 - r.2) ≠ (q.1 - r.1) * (p.2 - r.2)

/- ## Circumradius -/

/-- The squared circumradius of three non-collinear points.
    For the circumcircle of triangle pqr, R² = (|pq|²·|qr|²·|rp|²) / (16·Area²). -/
noncomputable def circumRadiusSq (p q r : Point) : ℝ :=
  let a2 := distSq p q
  let b2 := distSq q r
  let c2 := distSq r p
  let area2 := ((p.1 - r.1) * (q.2 - r.2) - (q.1 - r.1) * (p.2 - r.2)) ^ 2
  a2 * b2 * c2 / (4 * area2)

/-- A subset of k points has all distinct circumradii: every two triples
    determine circles of different radii. -/
def AllDistinctCircumradii (S : Finset Point) : Prop :=
  ∀ p₁ ∈ S, ∀ q₁ ∈ S, ∀ r₁ ∈ S,
  ∀ p₂ ∈ S, ∀ q₂ ∈ S, ∀ r₂ ∈ S,
    p₁ ≠ q₁ → q₁ ≠ r₁ → p₁ ≠ r₁ →
    p₂ ≠ q₂ → q₂ ≠ r₂ → p₂ ≠ r₂ →
    ({p₁, q₁, r₁} : Finset Point) ≠ {p₂, q₂, r₂} →
    circumRadiusSq p₁ q₁ r₁ ≠ circumRadiusSq p₂ q₂ r₂

/- ## The Minimal Number n_k -/

/-- n_k exists: for each k, there is a threshold such that any set of
    that many points in general position contains a k-subset with all
    distinct circumradii. -/
def NkExists (k : ℕ) : Prop :=
  ∃ n : ℕ, ∀ S : Finset Point, GeneralPosition S → n ≤ S.card →
    ∃ T : Finset Point, T ⊆ S ∧ T.card = k ∧ AllDistinctCircumradii T

/-- n_k is the minimal such number. -/
axiom minimalNk : ℕ → ℕ

/-- minimalNk k is a valid threshold. -/
axiom minimalNk_valid (k : ℕ) (hk : 3 ≤ k) :
    ∀ S : Finset Point, GeneralPosition S → minimalNk k ≤ S.card →
      ∃ T : Finset Point, T ⊆ S ∧ T.card = k ∧ AllDistinctCircumradii T

/-- minimalNk k is minimal: there exist configurations with minimalNk k - 1
    points that avoid k-subsets with all distinct circumradii. -/
axiom minimalNk_sharp (k : ℕ) (hk : 3 ≤ k) :
    ∃ S : Finset Point, GeneralPosition S ∧ S.card = minimalNk k - 1 ∧
      ¬∃ T : Finset Point, T ⊆ S ∧ T.card = k ∧ AllDistinctCircumradii T

/- ## Main Problem -/

/-- Erdős Problem 827: Determine n_k. In particular, find the growth rate. -/
def ErdosProblem827 : Prop :=
  ∀ k : ℕ, 3 ≤ k → NkExists k

/- ## Known Bounds -/

/-- Martinez-Roldán-Pensado: n_k ≪ k⁹. -/
def MartinezBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 3 ≤ k →
    (minimalNk k : ℝ) ≤ C * k ^ 9

/-- Erdős's original (incorrect) claimed bound: n_k ≤ k + 2·C(k-1,2)·C(k-1,3). -/
noncomputable def erdosClaimedBound (k : ℕ) : ℕ :=
  k + 2 * (k - 1).choose 2 * (k - 1).choose 3

/-- Martinez and Roldán-Pensado proved the corrected polynomial bound. -/
axiom martinez_roldan_pensado : MartinezBound

/- ## Trivial Cases -/

/-- AllDistinctCircumradii is vacuously true for 3-element sets:
    there is only one unordered triple, so the "distinct triples"
    hypothesis is never satisfied. -/
theorem allDistinctCircumradii_of_card_three {T : Finset Point} (hT : T.card = 3) :
    AllDistinctCircumradii T := by
  intro p₁ hp₁ q₁ hq₁ r₁ hr₁ p₂ hp₂ q₂ hq₂ r₂ hr₂
    hpq₁ hqr₁ hpr₁ hpq₂ hqr₂ hpr₂ hneq
  exfalso; apply hneq
  -- Both {p₁,q₁,r₁} and {p₂,q₂,r₂} are 3-distinct-element subsets of T
  -- Since |T| = 3, each must equal T, so they're equal
  have mk_eq : ∀ (a b c : Point), a ∈ T → b ∈ T → c ∈ T →
      a ≠ b → b ≠ c → a ≠ c → ({a, b, c} : Finset Point) = T := by
    intro a b c ha hb hc hab hbc hac
    apply Finset.Subset.antisymm
    · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    · intro x hx; by_contra hxnot
      have hsub : ({a, b, c} : Finset Point) ⊆ T := by
        intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl <;> assumption
      have hcard : ({a, b, c} : Finset Point).card = 3 := by
        rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem,
            Finset.card_singleton]
        · exact Finset.not_mem_singleton.mpr hbc
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hab, hac⟩
      have := Finset.card_lt_card (show ({a, b, c} : Finset Point) ⊂ T from
        ⟨hsub, fun h => hxnot (h hx)⟩)
      omega
  exact (mk_eq p₁ q₁ r₁ hp₁ hq₁ hr₁ hpq₁ hqr₁ hpr₁).trans
        (mk_eq p₂ q₂ r₂ hp₂ hq₂ hr₂ hpq₂ hqr₂ hpr₂).symm

/-- For k = 3, any 3 points in general position form a triangle with
    exactly one circumradius, so n_3 = 3.

    Proof: nk_ge_k gives 3 ≤ minimalNk 3. For the upper bound, if
    minimalNk 3 > 3 then minimalNk_sharp gives a GP set of size ≥ 3
    with no good 3-subset. But any 3-element subset has
    AllDistinctCircumradii vacuously (only one triple). Contradiction. -/
theorem nk_three : minimalNk 3 = 3 := by
  have hge := nk_ge_k 3 (by omega)
  suffices h : minimalNk 3 ≤ 3 by omega
  by_contra hlt
  push_neg at hlt
  obtain ⟨S, hGP, hCard, hBad⟩ := minimalNk_sharp 3 (by omega)
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_smaller_set S 3 (by omega)
  exact hBad ⟨T, hTS, hTcard, allDistinctCircumradii_of_card_three hTcard⟩

/-- n_k is monotone non-decreasing.

    Proof: Assume for contradiction that n_{k₂} < n_{k₁}. By minimalNk_sharp,
    there exists a GP set S of size n_{k₁} - 1 with no good k₁-subset.
    Since |S| ≥ n_{k₂}, by minimalNk_valid there is a good k₂-subset T ⊆ S.
    Since k₁ ≤ k₂ = |T|, we can take T' ⊆ T of size k₁. AllDistinctCircumradii
    is inherited by subsets (fewer triples, same radii). So T' is a good k₁-subset
    of S, contradicting the sharpness of S. -/
theorem nk_monotone (k₁ k₂ : ℕ) (h : k₁ ≤ k₂) (hk : 3 ≤ k₁) :
    minimalNk k₁ ≤ minimalNk k₂ := by
  by_contra hlt
  push_neg at hlt
  have hk2 : 3 ≤ k₂ := le_trans hk h
  obtain ⟨S, hGP, hCard, hBad⟩ := minimalNk_sharp k₁ hk
  have hBig : minimalNk k₂ ≤ S.card := by omega
  obtain ⟨T, hTS, hTcard, hTgood⟩ := minimalNk_valid k₂ hk2 S hGP hBig
  obtain ⟨T', hT'T, hT'card⟩ := Finset.exists_smaller_set T k₁ (by omega)
  have hT'good : AllDistinctCircumradii T' := by
    intro p₁ hp₁ q₁ hq₁ r₁ hr₁ p₂ hp₂ q₂ hq₂ r₂ hr₂
    exact hTgood p₁ (hT'T hp₁) q₁ (hT'T hq₁) r₁ (hT'T hr₁)
      p₂ (hT'T hp₂) q₂ (hT'T hq₂) r₂ (hT'T hr₂)
  exact hBad ⟨T', Finset.Subset.trans hT'T hTS, hT'card, hT'good⟩

/- ## Parabola GP Construction -/

/-- Parabola point: i ↦ (i, i²). Points on y = x² are in general position. -/
noncomputable def parabolaPoint (i : ℕ) : Point := ((i : ℝ), (i : ℝ) ^ 2)

/-- The parabola map is injective: distinct naturals give distinct points. -/
theorem parabolaPoint_injective : Function.Injective parabolaPoint := by
  intro a b h
  simp only [parabolaPoint, Prod.mk.injEq] at h
  exact_mod_cast h.1

/-- A finite set of n points on the parabola y = x². -/
noncomputable def parabolaSet (n : ℕ) : Finset Point :=
  (Finset.range n).image parabolaPoint

/-- The parabola set has exactly n points. -/
theorem parabolaSet_card (n : ℕ) : (parabolaSet n).card = n := by
  simp [parabolaSet, Finset.card_image_of_injective _ parabolaPoint_injective]

/-- Points on the parabola y = x² are in general position.
    The collinearity determinant of (a,a²), (b,b²), (c,c²) factors as
    (a−c)(b−c)(b−a), which is nonzero for distinct a, b, c. -/
theorem parabolaSet_gp (n : ℕ) : GeneralPosition (parabolaSet n) := by
  intro p hp q hq r hr hpq hqr hpr
  simp only [parabolaSet, Finset.mem_image, Finset.mem_range] at hp hq hr
  obtain ⟨a, -, rfl⟩ := hp
  obtain ⟨b, -, rfl⟩ := hq
  obtain ⟨c, -, rfl⟩ := hr
  have hab : a ≠ b := fun h => hpq (congrArg parabolaPoint h)
  have hbc : b ≠ c := fun h => hqr (congrArg parabolaPoint h)
  have hac : a ≠ c := fun h => hpr (congrArg parabolaPoint h)
  dsimp only [parabolaPoint]
  intro heq
  have factored : ((a : ℝ) - c) * ((b : ℝ) - c) * ((b : ℝ) - a) = 0 := by
    have : ((a : ℝ) - c) * ((b : ℝ) ^ 2 - (c : ℝ) ^ 2) -
           ((b : ℝ) - c) * ((a : ℝ) ^ 2 - (c : ℝ) ^ 2) =
           ((a : ℝ) - c) * ((b : ℝ) - c) * ((b : ℝ) - a) := by ring
    linarith
  have h1 : (a : ℝ) ≠ c := by exact_mod_cast hac
  have h2 : (b : ℝ) ≠ c := by exact_mod_cast hbc
  have h3 : (b : ℝ) ≠ a := by exact_mod_cast hab.symm
  exact absurd factored (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h1) (sub_ne_zero.mpr h2))
    (sub_ne_zero.mpr h3))

/-- n_k ≥ k: you need at least k points to find a k-subset.
    If minimalNk k < k, the parabola GP set of size minimalNk k satisfies
    minimalNk_valid but can't contain a k-subset (too small). -/
theorem nk_ge_k (k : ℕ) (hk : 3 ≤ k) : k ≤ minimalNk k := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨T, hTS, hTcard, _⟩ := minimalNk_valid k hk (parabolaSet (minimalNk k))
    (parabolaSet_gp _) (by simp [parabolaSet_card])
  have := Finset.card_le_card hTS
  rw [parabolaSet_card] at this
  omega

/- ## Structural Properties -/

/-- Squared distance is symmetric. -/
theorem distSq_comm (p q : Point) : distSq p q = distSq q p := by
  simp only [distSq]; ring

/-- Squared distance from a point to itself is 0. -/
theorem distSq_self (p : Point) : distSq p p = 0 := by
  simp only [distSq]; ring

/-- Squared distance is non-negative. -/
theorem distSq_nonneg (p q : Point) : 0 ≤ distSq p q := by
  simp only [distSq]; positivity

/-- Squared distance is 0 iff points coincide. -/
theorem distSq_eq_zero_iff (p q : Point) :
    distSq p q = 0 ↔ p = q := by
  constructor
  · intro h
    simp only [distSq] at h
    have h1 : (p.1 - q.1) ^ 2 = 0 := by nlinarith [sq_nonneg (p.2 - q.2)]
    have h2 : (p.2 - q.2) ^ 2 = 0 := by nlinarith [sq_nonneg (p.1 - q.1)]
    have := sq_eq_zero_iff.mp h1
    have := sq_eq_zero_iff.mp h2
    ext <;> linarith
  · rintro rfl; exact distSq_self _

/-- General position is hereditary: subsets of GP sets are in GP. -/
theorem generalPosition_subset {S T : Finset Point} (hTS : T ⊆ S)
    (hGP : GeneralPosition S) : GeneralPosition T :=
  fun p hp q hq r hr => hGP p (hTS hp) q (hTS hq) r (hTS hr)

/-- AllDistinctCircumradii is hereditary: subsets inherit the property. -/
theorem allDistinctCircumradii_subset {S T : Finset Point} (hTS : T ⊆ S)
    (h : AllDistinctCircumradii S) : AllDistinctCircumradii T :=
  fun p₁ hp₁ q₁ hq₁ r₁ hr₁ p₂ hp₂ q₂ hq₂ r₂ hr₂ =>
    h p₁ (hTS hp₁) q₁ (hTS hq₁) r₁ (hTS hr₁) p₂ (hTS hp₂) q₂ (hTS hq₂) r₂ (hTS hr₂)

/-- NkExists is proved for all k ≥ 3 using the axioms. -/
theorem nkExists_of_axioms (k : ℕ) (hk : 3 ≤ k) : NkExists k :=
  ⟨minimalNk k, minimalNk_valid k hk⟩
