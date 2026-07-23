/-
  Erdős Problem #1039 — OQ-05: transfinite diameter / logarithmic capacity route.

  Source: https://erdosproblems.com/1039
  Status of parent problem: OPEN

  Parent setup.
  For a monic polynomial f(z) = ∏ᵢ (z - zᵢ) ∈ ℂ[z] with all roots zᵢ in the closed
  unit disc, let ρ(f) be the radius of the largest open disc contained in the
  sublevel set {z : |f(z)| < 1}.  Erdős, Herzog and Piranian asked whether
  ρ(f) ≫ 1/n.

  OQ-05 asks to relate ρ(f) to two potential-theoretic invariants of the root set:
  the **transfinite diameter** of the root multiset and the **logarithmic capacity**
  of the lemniscate complement.  Mathlib has essentially no capacity /
  transfinite-diameter API, so those objects have to be built.

  This file supplies **Key Lemma 1** of that programme: the finite discrete version
  of the transfinite diameter — the *n-point spread* — and its elementary,
  fully machine-checked, axiom-free properties.  It does **not** resolve the OPEN
  parent conjecture; it makes one of the two capacity-type quantities precise.

  For a tuple `z : Fin n → ℂ` we define
  * `spreadProduct z = ∏_{i<j} ‖zᵢ - zⱼ‖`   (the Vandermonde spread), and
  * `discreteDiameter z = spreadProduct z ^ (2 / (n(n-1)))`   (the n-point diameter,
    the finite-`n` truncation of the transfinite diameter
    `d(Z) = limₙ (max_{|Z|=n} ∏_{i<j}|zᵢ-zⱼ|)^{2/(n(n-1))}`).

  Main results (all axiom-free).
  1. `spreadProduct_nonneg` — the spread product is `≥ 0`.
  2. `spreadProduct_eq_norm_det_vandermonde` — it is the modulus of the Vandermonde
     determinant `∏_{i<j}(zⱼ - zᵢ)`, tying the spread to the discriminant.
  3. `spreadProduct_pos_iff` — the spread is strictly positive iff the roots are
     distinct (`Function.Injective z`); it vanishes exactly at a repeated root.
  4. `spreadProduct_le_two_pow` — for roots in the closed unit disc the spread is
     `≤ 2 ^ (#pairs)`, since every gap `‖zᵢ - zⱼ‖ ≤ 2`.
  5. `two_mul_pairCount` — `2 · #pairs = n(n-1)`, the Gauss count of ordered pairs.
  6. `discreteDiameter_nonneg` — the n-point diameter is `≥ 0`.
  7. `discreteDiameter_le_two` — for `n ≥ 2` unit-disc roots the n-point diameter is
     `≤ 2`, the classical fact `dₙ(K) ≤ diam(K)` (here `diam(closed unit disc) = 2`).
  This mirrors the axiom-free-lemma / axiomatized-literature split used by the
  sibling `Erdos1039Conformal` (OQ-03) file.
-/

import Mathlib

namespace Erdos1039TransfiniteDiameter

open Finset

variable {n : ℕ}

/-- **The Vandermonde spread product** `V(Z) = ∏_{i<j} ‖zᵢ - zⱼ‖`.
This is the finite-`n` numerator of the transfinite diameter of the root set. -/
noncomputable def spreadProduct (z : Fin n → ℂ) : ℝ :=
  ∏ i, ∏ j ∈ Finset.Ioi i, ‖z i - z j‖

/-- The number of ordered pairs `i < j` in `Fin n`. -/
def pairCount (n : ℕ) : ℕ := ∑ i : Fin n, (Finset.Ioi i).card

/-- **Gauss count of pairs:** `2 · #{i<j} = n(n-1)`. -/
theorem two_mul_pairCount (n : ℕ) : 2 * pairCount n = n * (n - 1) := by
  unfold pairCount
  simp only [Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun i => n - 1 - i) n]
  rw [Finset.sum_range_reflect (fun i => i) n]
  rw [mul_comm, Finset.sum_range_id_mul_two]

/-- The spread product is nonnegative (it is a product of norms). -/
theorem spreadProduct_nonneg (z : Fin n → ℂ) : 0 ≤ spreadProduct z := by
  unfold spreadProduct
  exact Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => norm_nonneg _

/-- **Discriminant identity:** the spread product is the modulus of the Vandermonde
determinant `det (zᵢʲ) = ∏_{i<j}(zⱼ - zᵢ)`. -/
theorem spreadProduct_eq_norm_det_vandermonde (z : Fin n → ℂ) :
    spreadProduct z = ‖(Matrix.vandermonde z).det‖ := by
  rw [Matrix.det_vandermonde, norm_prod]
  unfold spreadProduct
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [norm_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [norm_sub_rev]

/-- **Nondegeneracy:** the spread product is strictly positive iff the roots are
distinct.  It vanishes exactly when two roots coincide. -/
theorem spreadProduct_pos_iff (z : Fin n → ℂ) :
    0 < spreadProduct z ↔ Function.Injective z := by
  unfold spreadProduct
  constructor
  · -- positivity of the product forbids any repeated root
    intro hpos a b hab
    by_contra hne
    -- WLOG order the two indices so the offending gap sits in an `Ioi`
    rcases lt_or_gt_of_ne (fun h : a = b => hne (h ▸ rfl)) with hlt | hgt
    · have hzero : ∏ j ∈ Finset.Ioi a, ‖z a - z j‖ = 0 :=
        Finset.prod_eq_zero (Finset.mem_Ioi.mpr hlt) (by rw [hab, sub_self, norm_zero])
      have : ∏ i, ∏ j ∈ Finset.Ioi i, ‖z i - z j‖ = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ a) hzero
      rw [this] at hpos; exact lt_irrefl _ hpos
    · have hzero : ∏ j ∈ Finset.Ioi b, ‖z b - z j‖ = 0 :=
        Finset.prod_eq_zero (Finset.mem_Ioi.mpr hgt)
          (by rw [hab, sub_self, norm_zero])
      have : ∏ i, ∏ j ∈ Finset.Ioi i, ‖z i - z j‖ = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ b) hzero
      rw [this] at hpos; exact lt_irrefl _ hpos
  · intro hinj
    refine Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => ?_
    have hlt : i < j := Finset.mem_Ioi.mp hj
    have : z i ≠ z j := fun h => (ne_of_lt hlt) (hinj h)
    exact norm_pos_iff.mpr (sub_ne_zero.mpr this)

/-- Every gap between two unit-disc points is at most `2`. -/
private theorem gap_le_two {z : Fin n → ℂ} (h : ∀ i, ‖z i‖ ≤ 1) (i j : Fin n) :
    ‖z i - z j‖ ≤ 2 := by
  calc ‖z i - z j‖ ≤ ‖z i‖ + ‖z j‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add (h i) (h j)
    _ = 2 := by norm_num

/-- **Unit-disc bound:** for roots in the closed unit disc the spread product is at
most `2 ^ (#pairs)`. -/
theorem spreadProduct_le_two_pow {z : Fin n → ℂ} (h : ∀ i, ‖z i‖ ≤ 1) :
    spreadProduct z ≤ 2 ^ (pairCount n) := by
  unfold spreadProduct pairCount
  calc ∏ i, ∏ j ∈ Finset.Ioi i, ‖z i - z j‖
      ≤ ∏ i, ∏ j ∈ Finset.Ioi i, (2 : ℝ) := by
        refine Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j _ => norm_nonneg _)
          (fun i _ => Finset.prod_le_prod (fun j _ => norm_nonneg _)
            (fun j _ => gap_le_two h i j))
    _ = 2 ^ (∑ i : Fin n, (Finset.Ioi i).card) := by
        simp only [Finset.prod_const]
        rw [Finset.prod_pow_eq_pow_sum]

/-- **The n-point (discrete transfinite) diameter** of the root tuple,
`dₙ(Z) = V(Z)^{2/(n(n-1))}`, the finite truncation of the transfinite diameter. -/
noncomputable def discreteDiameter (z : Fin n → ℂ) : ℝ :=
  spreadProduct z ^ (2 / ((n : ℝ) * ((n : ℝ) - 1)))

/-- The n-point diameter is nonnegative. -/
theorem discreteDiameter_nonneg (z : Fin n → ℂ) : 0 ≤ discreteDiameter z :=
  Real.rpow_nonneg (spreadProduct_nonneg z) _

/-- **Strict positivity for distinct roots.**  If the tuple `z` is injective, its
`n`-point diameter is strictly positive — the spread product is then positive and a
positive base raised to any real power stays positive.  This sharpens
`discreteDiameter_nonneg` and is what makes `Real.log (discreteDiameter z)` and the
energy-bridge identity meaningful. -/
theorem discreteDiameter_pos (z : Fin n → ℂ) (hz : Function.Injective z) :
    0 < discreteDiameter z :=
  Real.rpow_pos_of_pos ((spreadProduct_pos_iff z).mpr hz) _

/-- **Positivity characterises distinctness** (for `n ≥ 2`): the `n`-point diameter is
strictly positive iff the roots are pairwise distinct.  The forward direction uses that
the normalising exponent `2/(n(n−1))` is nonzero for `n ≥ 2`, so a vanishing spread
product would force `dₙ = 0`. -/
theorem discreteDiameter_pos_iff {z : Fin n → ℂ} (hn : 2 ≤ n) :
    0 < discreteDiameter z ↔ Function.Injective z := by
  rw [← spreadProduct_pos_iff]
  unfold discreteDiameter
  have hepos : 0 < 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact div_pos (by norm_num) (mul_pos (by linarith) (by linarith))
  constructor
  · intro h
    rcases (spreadProduct_nonneg z).lt_or_eq with hpos | hz0
    · exact hpos
    · rw [← hz0, Real.zero_rpow (ne_of_gt hepos)] at h
      exact absurd h (lt_irrefl 0)
  · intro h
    exact Real.rpow_pos_of_pos h _

/-- The normalising exponent times the pair count is `1` (for `n ≥ 2`). -/
private theorem pairCount_mul_exp {n : ℕ} (hn : 2 ≤ n) :
    (pairCount n : ℝ) * (2 / ((n : ℝ) * ((n : ℝ) - 1))) = 1 := by
  have hn1 : (1 : ℕ) ≤ n := le_trans (by norm_num) hn
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn1, Nat.cast_one]
  have hprod : (2 : ℝ) * (pairCount n : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    have := two_mul_pairCount n
    have : ((2 * pairCount n : ℕ) : ℝ) = ((n * (n - 1) : ℕ) : ℝ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) this
    push_cast at this
    rw [hcast] at this
    linarith [this]
  have hne : (n : ℝ) * ((n : ℝ) - 1) ≠ 0 := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
      apply mul_pos <;> linarith
    exact ne_of_gt this
  have hD : (pairCount n : ℝ) * (2 / ((n : ℝ) * ((n : ℝ) - 1)))
      = (2 * (pairCount n : ℝ)) / ((n : ℝ) * ((n : ℝ) - 1)) := by ring
  rw [hD, hprod, div_self hne]

/-- **Classical spread bound `dₙ(K) ≤ diam(K)`:** for `n ≥ 2` roots in the closed
unit disc (`diam = 2`), the n-point diameter is at most `2`. -/
theorem discreteDiameter_le_two {z : Fin n → ℂ} (hn : 2 ≤ n)
    (h : ∀ i, ‖z i‖ ≤ 1) : discreteDiameter z ≤ 2 := by
  unfold discreteDiameter
  set e : ℝ := 2 / ((n : ℝ) * ((n : ℝ) - 1)) with he
  have he0 : 0 ≤ e := by
    rw [he]
    apply div_nonneg (by norm_num)
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    apply mul_nonneg <;> linarith
  -- spread ≤ 2^P as a real power
  have hbound : spreadProduct z ≤ (2 : ℝ) ^ ((pairCount n : ℝ)) := by
    have := spreadProduct_le_two_pow h
    rwa [Real.rpow_natCast]
  calc spreadProduct z ^ e
      ≤ ((2 : ℝ) ^ ((pairCount n : ℝ))) ^ e :=
        Real.rpow_le_rpow (spreadProduct_nonneg z) hbound he0
    _ = (2 : ℝ) ^ ((pairCount n : ℝ) * e) := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ = 2 := by rw [pairCount_mul_exp hn, Real.rpow_one]

/-! ## Transformation laws: scaling covariance and translation invariance

The discrete diameter transforms like a *length*: scaling every root by `c ∈ ℂ`
multiplies `dₙ` by `‖c‖`, and translating every root by a constant leaves `dₙ`
unchanged.  These are the finite-`n` shadows of the defining behaviour of
logarithmic capacity under affine maps — `cap(cK + a) = ‖c‖ · cap(K)` — and in
particular explain why the transfinite diameter of a disc of radius `R` (centred
anywhere) is `R`.  Both laws are exact and hold for *every* configuration; they
are `0`-axiom. -/

/-- **Spread product under scaling.**  Multiplying every root by `c` scales each of
the `#pairs = pairCount n` gap factors by `‖c‖`, so `V(cZ) = ‖c‖^{#pairs}·V(Z)`. -/
theorem spreadProduct_smul (c : ℂ) (z : Fin n → ℂ) :
    spreadProduct (fun i => c * z i) = ‖c‖ ^ pairCount n * spreadProduct z := by
  simp only [spreadProduct]
  have key : ∀ i : Fin n,
      (∏ j ∈ Finset.Ioi i, ‖c * z i - c * z j‖)
        = ‖c‖ ^ (Finset.Ioi i).card * ∏ j ∈ Finset.Ioi i, ‖z i - z j‖ := by
    intro i
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← norm_mul, mul_sub]
  rw [Finset.prod_congr rfl fun i _ => key i, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  rfl

/-- **Scaling covariance of the discrete diameter.**  For `n ≥ 2`, scaling every
root by `c` multiplies the `n`-point diameter by `‖c‖`: `dₙ(cZ) = ‖c‖·dₙ(Z)`.  The
exponent bookkeeping is `#pairs · 2/(n(n-1)) = 1` (`pairCount_mul_exp`), so the
`‖c‖^{#pairs}` from `spreadProduct_smul` normalises to a single factor of `‖c‖`. -/
theorem discreteDiameter_smul (hn : 2 ≤ n) (c : ℂ) (z : Fin n → ℂ) :
    discreteDiameter (fun i => c * z i) = ‖c‖ * discreteDiameter z := by
  unfold discreteDiameter
  rw [spreadProduct_smul,
    Real.mul_rpow (by positivity) (spreadProduct_nonneg z),
    ← Real.rpow_natCast (‖c‖) (pairCount n),
    ← Real.rpow_mul (norm_nonneg c),
    pairCount_mul_exp hn, Real.rpow_one]

/-- **Translation invariance of the spread product.**  Adding a constant `c` to
every root leaves each gap `zᵢ − zⱼ` unchanged, so `V(Z + c) = V(Z)`. -/
theorem spreadProduct_add_const (c : ℂ) (z : Fin n → ℂ) :
    spreadProduct (fun i => z i + c) = spreadProduct z := by
  simp only [spreadProduct]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  congr 1
  ring

/-- **Translation invariance of the discrete diameter.**  `dₙ(Z + c) = dₙ(Z)`: the
`n`-point diameter depends only on the pairwise gaps, which are translation
invariant. -/
theorem discreteDiameter_add_const (c : ℂ) (z : Fin n → ℂ) :
    discreteDiameter (fun i => z i + c) = discreteDiameter z := by
  unfold discreteDiameter
  rw [spreadProduct_add_const]

/- ## The logarithmic-energy bridge

The transfinite diameter is a *multiplicative* invariant, while logarithmic
capacity is governed by the *additive* logarithmic energy `∑_{i<j} log‖zᵢ − zⱼ‖`.
The two are related by `log`/`exp`; making that dictionary explicit is the first
concrete link between the discrete diameter of this file and the capacity side of
OQ-05. -/

/-- **Logarithmic energy sum (log-spread)** `∑_{i<j} log‖zᵢ − zⱼ‖` of the root
tuple — the additive potential-theoretic form of the spread product. -/
noncomputable def logSpread (z : Fin n → ℂ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.Ioi i, Real.log ‖z i - z j‖

/-- For distinct roots, `log` of the spread product is the logarithmic energy sum. -/
theorem log_spreadProduct (z : Fin n → ℂ) (hz : Function.Injective z) :
    Real.log (spreadProduct z) = logSpread z := by
  have hgap : ∀ i j : Fin n, i < j → ‖z i - z j‖ ≠ 0 := fun i j hlt =>
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun h => (ne_of_lt hlt) (hz h))
  unfold spreadProduct logSpread
  rw [Real.log_prod (fun i _ =>
        Finset.prod_ne_zero_iff.mpr fun j hj => hgap i j (Finset.mem_Ioi.mp hj))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.log_prod (fun j hj => hgap i j (Finset.mem_Ioi.mp hj))]

/-- **Energy bridge:** the n-point diameter is the exponential of the normalised
logarithmic energy of the root set,
`dₙ(Z) = exp((2/(n(n-1))) · ∑_{i<j} log‖zᵢ − zⱼ‖)`.
This is the multiplicative/additive dictionary connecting the (transfinite)
diameter to logarithmic potential theory — the precise sense in which the two
OQ-05 invariants are the same object viewed through `log`. -/
theorem discreteDiameter_eq_exp (z : Fin n → ℂ) (hz : Function.Injective z) :
    discreteDiameter z
      = Real.exp ((2 / ((n : ℝ) * ((n : ℝ) - 1))) * logSpread z) := by
  unfold discreteDiameter
  rw [Real.rpow_def_of_pos ((spreadProduct_pos_iff z).mpr hz), log_spreadProduct z hz,
    mul_comm]

/- ## Fekete monotonicity: the deletion identity

Fekete's theorem states that the `n`-point diameter `dₙ(K)` decreases in `n`.  Its
algebraic heart is a *deletion identity*: given an `(n+1)`-tuple, delete each point
in turn and multiply the `n+1` resulting spreads; the result is exactly
`spreadProduct z ^ (n-1)`, because each pair `zₐ, z_b` survives in precisely the
`n-1` deletions that remove neither `a` nor `b`.  Once one takes suprema over
configurations in a compact set this identity forces `d_{n+1} ≤ dₙ`.  Here we
formalize the identity itself (axiom-free); it holds for *every* tuple, distinct
roots or not. -/

/-- **Delete the `k`-th point** of an `(n+1)`-tuple, yielding an `n`-tuple by
composing with the order-embedding `Fin.succAbove k : Fin n ↪ Fin (n+1)`. -/
noncomputable def deleteAt (z : Fin (n + 1) → ℂ) (k : Fin (n + 1)) : Fin n → ℂ :=
  fun i => z (k.succAbove i)

/-- Deleting a point from a tuple with distinct entries keeps the entries distinct. -/
theorem deleteAt_injective {z : Fin (n + 1) → ℂ} (hz : Function.Injective z)
    (k : Fin (n + 1)) : Function.Injective (deleteAt z k) :=
  hz.comp (Fin.succAbove_right_injective)

/-- **Deletion reindexing:** the spread of the tuple with point `k` removed is the
product of `‖zₐ − z_b‖` over exactly those pairs `a < b` avoiding index `k`. -/
theorem spreadProduct_deleteAt (z : Fin (n + 1) → ℂ) (k : Fin (n + 1)) :
    spreadProduct (deleteAt z k)
      = ∏ a ∈ Finset.univ.erase k, ∏ b ∈ (Finset.Ioi a).erase k, ‖z a - z b‖ := by
  unfold spreadProduct deleteAt
  refine Finset.prod_bij (fun i _ => k.succAbove i) ?_ ?_ ?_ ?_
  · intro i _
    exact Finset.mem_erase.mpr ⟨Fin.succAbove_ne k i, Finset.mem_univ _⟩
  · intro a _ b _ hab
    exact Fin.succAbove_right_injective hab
  · intro a ha
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq (Finset.mem_erase.mp ha).1
    exact ⟨i, Finset.mem_univ _, hi⟩
  · intro i _
    refine Finset.prod_bij (fun j _ => k.succAbove j) ?_ ?_ ?_ ?_
    · intro j hj
      have hlt : i < j := Finset.mem_Ioi.mp hj
      exact Finset.mem_erase.mpr
        ⟨Fin.succAbove_ne k j, Finset.mem_Ioi.mpr ((Fin.succAbove_lt_succAbove_iff).mpr hlt)⟩
    · intro a _ b _ hab
      exact Fin.succAbove_right_injective hab
    · intro b hb
      obtain ⟨hbk, hblt⟩ := Finset.mem_erase.mp hb
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hbk
      refine ⟨j, ?_, hj⟩
      apply Finset.mem_Ioi.mpr
      have : k.succAbove i < k.succAbove j := by rw [hj]; exact Finset.mem_Ioi.mp hblt
      exact (Fin.succAbove_lt_succAbove_iff).mp this
    · intro j _; rfl

/-- The number of indices avoiding two distinct points of `Fin (n+1)` is `n-1`. -/
theorem card_filter_avoid {a b : Fin (n + 1)} (hab : a ≠ b) :
    (Finset.univ.filter (fun k => a ≠ k ∧ b ≠ k)).card = n - 1 := by
  have hset : (Finset.univ.filter (fun k => a ≠ k ∧ b ≠ k))
      = (Finset.univ.erase a).erase b := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    exact ⟨fun ⟨h1, h2⟩ => ⟨Ne.symm h2, Ne.symm h1⟩,
           fun ⟨h1, h2⟩ => ⟨Ne.symm h2, Ne.symm h1⟩⟩
  rw [hset]
  have hb_mem : b ∈ Finset.univ.erase a :=
    Finset.mem_erase.mpr ⟨fun h => hab h.symm, Finset.mem_univ _⟩
  rw [Finset.card_erase_of_mem hb_mem, Finset.card_erase_of_mem (Finset.mem_univ a)]
  simp [Finset.card_univ]

/-- **Fekete deletion identity** (combinatorial core of Fekete monotonicity):
`∏ₖ V(delete k Z) = V(Z)^{n-1}`.  Deleting each of the `n+1` points and multiplying
the resulting spreads recovers `spreadProduct z ^ (n-1)`, since each pair survives
exactly the `n-1` deletions removing neither endpoint.  Holds for every tuple. -/
theorem prod_spreadProduct_deleteAt (z : Fin (n + 1) → ℂ) :
    ∏ k, spreadProduct (deleteAt z k) = spreadProduct z ^ (n - 1) := by
  have hfactor : ∀ k : Fin (n + 1),
      spreadProduct (deleteAt z k)
        = ∏ a, ∏ b ∈ Finset.Ioi a, (if a ≠ k ∧ b ≠ k then ‖z a - z b‖ else 1) := by
    intro k
    rw [spreadProduct_deleteAt z k]
    rw [← Finset.filter_ne' Finset.univ k, Finset.prod_filter]
    refine Finset.prod_congr rfl (fun a _ => ?_)
    by_cases hak : a = k
    · simp [hak]
    · rw [if_pos hak, ← Finset.filter_ne' (Finset.Ioi a) k, Finset.prod_filter]
      refine Finset.prod_congr rfl (fun b _ => ?_)
      by_cases hbk : b = k
      · simp [hbk]
      · rw [if_pos hbk, if_pos ⟨hak, hbk⟩]
  calc ∏ k, spreadProduct (deleteAt z k)
      = ∏ k, ∏ a, ∏ b ∈ Finset.Ioi a, (if a ≠ k ∧ b ≠ k then ‖z a - z b‖ else 1) :=
        Finset.prod_congr rfl (fun k _ => hfactor k)
    _ = ∏ a, ∏ b ∈ Finset.Ioi a, ∏ k, (if a ≠ k ∧ b ≠ k then ‖z a - z b‖ else 1) := by
        rw [Finset.prod_comm]
        refine Finset.prod_congr rfl (fun a _ => ?_)
        rw [Finset.prod_comm]
    _ = ∏ a, ∏ b ∈ Finset.Ioi a, ‖z a - z b‖ ^ (n - 1) := by
        refine Finset.prod_congr rfl (fun a _ => Finset.prod_congr rfl (fun b hb => ?_))
        have hab : a ≠ b := ne_of_lt (Finset.mem_Ioi.mp hb)
        rw [← Finset.prod_filter, Finset.prod_const, card_filter_avoid hab]
    _ = (∏ a, ∏ b ∈ Finset.Ioi a, ‖z a - z b‖) ^ (n - 1) := by
        rw [Finset.prod_congr rfl (fun a _ => Finset.prod_pow (Finset.Ioi a) (n - 1) _)]
        rw [Finset.prod_pow]
    _ = spreadProduct z ^ (n - 1) := by rw [spreadProduct]

/-- **Additive (energy) form of the deletion identity.** For distinct roots the
logarithmic energies of the `n+1` deletions sum to `(n-1)` copies of the full
energy — the potential-theoretic shadow of `prod_spreadProduct_deleteAt` under
`log`, matching the energy bridge above. -/
theorem sum_logSpread_deleteAt (z : Fin (n + 1) → ℂ) (hz : Function.Injective z) :
    ∑ k, logSpread (deleteAt z k) = ((n - 1 : ℕ) : ℝ) * logSpread z := by
  have hpos : ∀ k : Fin (n + 1), 0 < spreadProduct (deleteAt z k) := fun k =>
    (spreadProduct_pos_iff _).mpr (deleteAt_injective hz k)
  have hposz : 0 < spreadProduct z := (spreadProduct_pos_iff z).mpr hz
  have key := congrArg Real.log (prod_spreadProduct_deleteAt z)
  rw [Real.log_prod (fun k _ => (hpos k).ne'), Real.log_pow] at key
  rw [← log_spreadProduct z hz]
  rw [← key]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [log_spreadProduct _ (deleteAt_injective hz k)]

/- ## Fekete monotonicity: the pointwise inequality

The deletion identity, in its additive form `sum_logSpread_deleteAt`, says the
`n+1` deletion energies average to `(n-1)/(n+1)` of the full energy.  Since some
term of a finite sum always meets the mean, at least one deletion has energy
`≥ (n-1)/(n+1) · logSpread z`, and the exponent bookkeeping
`2/(n(n-1)) · (n-1)/(n+1) = 2/((n+1)n)` turns that into the diameter comparison
`d_{n+1}(Z) ≤ dₙ(delete k Z)`.  This is the finite heart of Fekete's monotonicity
theorem `d_{n+1} ≤ dₙ`; the classical statement follows by taking suprema over
configurations in a compact set (which needs compactness API beyond this file). -/

/-- **Fekete monotonicity (pointwise form).** For every injective `(n+1)`-tuple of
roots with `n ≥ 2`, at least one `n`-point deletion has `n`-point diameter no
smaller than the `(n+1)`-point diameter of the whole tuple:
`∃ k, d_{n+1}(Z) ≤ dₙ(delete k Z)`.  Axiom-free consequence of the deletion
identity via "some term of a sum meets the mean". -/
theorem exists_deleteAt_discreteDiameter_ge (hn : 2 ≤ n)
    (z : Fin (n + 1) → ℂ) (hz : Function.Injective z) :
    ∃ k : Fin (n + 1), discreteDiameter z ≤ discreteDiameter (deleteAt z k) := by
  have hr2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hr0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hrm1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hrp1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  -- additive deletion identity, cast cleaned up
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hsum : ∑ k, logSpread (deleteAt z k) = ((n : ℝ) - 1) * logSpread z := by
    rw [sum_logSpread_deleteAt z hz, hcast]
  -- the constant "mean" term sums to the same total
  have hconst : (∑ _k : Fin (n + 1), ((n : ℝ) - 1) * logSpread z / ((n : ℝ) + 1))
      = ((n : ℝ) - 1) * logSpread z := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hcp : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcp]
    field_simp
  -- some deletion beats the mean
  have hle : (∑ _k : Fin (n + 1), ((n : ℝ) - 1) * logSpread z / ((n : ℝ) + 1))
      ≤ ∑ k, logSpread (deleteAt z k) := by rw [hconst, hsum]
  obtain ⟨k, -, hk⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hle
  refine ⟨k, ?_⟩
  have hzk : Function.Injective (deleteAt z k) := deleteAt_injective hz k
  rw [discreteDiameter_eq_exp z hz, discreteDiameter_eq_exp (deleteAt z k) hzk,
    Real.exp_le_exp]
  have hcp : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcp, add_sub_cancel_right]
  have hc : (0 : ℝ) < 2 / ((n : ℝ) * ((n : ℝ) - 1)) := div_pos (by norm_num) (mul_pos hr0 hrm1)
  have hstep := mul_le_mul_of_nonneg_left hk (le_of_lt hc)
  calc 2 / (((n : ℝ) + 1) * (n : ℝ)) * logSpread z
      = 2 / ((n : ℝ) * ((n : ℝ) - 1))
          * (((n : ℝ) - 1) * logSpread z / ((n : ℝ) + 1)) := by
        field_simp
    _ ≤ 2 / ((n : ℝ) * ((n : ℝ) - 1)) * logSpread (deleteAt z k) := hstep

/- ## Fekete monotonicity: the supremum-level statement

The pointwise inequality `exists_deleteAt_discreteDiameter_ge` lifts to the
classical **supremum** form once we take suprema over all configurations inside a
compact set.  We do this for the closed unit disc `{|z| ≤ 1}` — the setting of the
parent lemniscate problem, whose roots lie in the unit disc.  Define

    dₙ := sup { dₙ(Z) : Z an n-point configuration in the closed unit disc }.

Every `dₙ(Z) ≤ 2` (`discreteDiameter_le_two`), so the supremum exists, and the
pointwise deletion inequality forces `d_{n+1} ≤ dₙ`.  Hence `n ↦ dₙ` is
non-increasing (for `n ≥ 2`) and, being bounded below by `0`, converges — this is
the sense in which the transfinite diameter `d = infₙ dₙ` is a well-defined limit. -/

/-- The set of `n`-point discrete diameters `dₙ(Z)` achievable by configurations
`Z` in the **closed unit disc** `{|z| ≤ 1}`. -/
def unitDiscDiameters (n : ℕ) : Set ℝ :=
  { d | ∃ z : Fin n → ℂ, (∀ i, ‖z i‖ ≤ 1) ∧ discreteDiameter z = d }

/-- The **`n`-point transfinite diameter of the closed unit disc**,
`dₙ = sup_Z dₙ(Z)` over configurations `Z` in `{|z| ≤ 1}`. -/
noncomputable def transfiniteDiameterN (n : ℕ) : ℝ := sSup (unitDiscDiameters n)

/-- The all-zero configuration realises the diameter `0`, so `0 ∈ unitDiscDiameters n`
(for `n ≥ 2`, where a repeated point makes the configuration non-injective and hence
`dₙ = 0`).  In particular the set is non-empty. -/
theorem zero_mem_unitDiscDiameters (hn : 2 ≤ n) : (0 : ℝ) ∈ unitDiscDiameters n := by
  refine ⟨fun _ => 0, fun _ => by simp, ?_⟩
  have hni : ¬ Function.Injective (fun _ : Fin n => (0 : ℂ)) := by
    intro h
    have h01 : (⟨0, by omega⟩ : Fin n) = ⟨1, by omega⟩ := h rfl
    simp [Fin.ext_iff] at h01
  have hnpos : ¬ 0 < discreteDiameter (fun _ : Fin n => (0 : ℂ)) := fun h =>
    hni ((discreteDiameter_pos_iff hn).mp h)
  exact le_antisymm (not_lt.mp hnpos) (discreteDiameter_nonneg _)

/-- `unitDiscDiameters n` is non-empty (contains `0`) for `n ≥ 2`. -/
theorem unitDiscDiameters_nonempty (hn : 2 ≤ n) : (unitDiscDiameters n).Nonempty :=
  ⟨0, zero_mem_unitDiscDiameters hn⟩

/-- `unitDiscDiameters n` is bounded above by `2` (`discreteDiameter_le_two`), so its
supremum `transfiniteDiameterN n` exists. -/
theorem unitDiscDiameters_bddAbove (hn : 2 ≤ n) : BddAbove (unitDiscDiameters n) := by
  refine ⟨2, ?_⟩
  rintro d ⟨z, hz, rfl⟩
  exact discreteDiameter_le_two hn hz

/-- **Fekete monotonicity (supremum form).**  The `n`-point transfinite diameter of
the closed unit disc is non-increasing in `n`:  `d_{n+1} ≤ dₙ` for `n ≥ 2`.

For each `(n+1)`-configuration `Z` in the disc: if `Z` has distinct points, the
pointwise deletion inequality (`exists_deleteAt_discreteDiameter_ge`) supplies an
`n`-point sub-configuration — still inside the disc — of diameter `≥ d_{n+1}(Z)`,
which is bounded above by `dₙ`; if `Z` has a repeated point then `d_{n+1}(Z) = 0 ≤ dₙ`.
Taking the supremum over `Z` gives `d_{n+1} ≤ dₙ`.  Combined with `0 ≤ dₙ ≤ 2` this
makes the transfinite diameter `d = infₙ dₙ` a well-defined (monotone, bounded) limit. -/
theorem transfiniteDiameterN_succ_le (hn : 2 ≤ n) :
    transfiniteDiameterN (n + 1) ≤ transfiniteDiameterN n := by
  have hbddn : BddAbove (unitDiscDiameters n) := unitDiscDiameters_bddAbove hn
  refine csSup_le (unitDiscDiameters_nonempty (by omega)) ?_
  rintro d ⟨z, hzdisc, rfl⟩
  by_cases hz : Function.Injective z
  · -- distinct points: some deletion has diameter ≥ d_{n+1}(z), and lies in the disc
    obtain ⟨k, hk⟩ := exists_deleteAt_discreteDiameter_ge hn z hz
    have hmem : discreteDiameter (deleteAt z k) ∈ unitDiscDiameters n :=
      ⟨deleteAt z k, fun i => hzdisc _, rfl⟩
    exact le_trans hk (le_csSup hbddn hmem)
  · -- repeated point: d_{n+1}(z) = 0 ≤ dₙ
    have hnpos : ¬ 0 < discreteDiameter z := fun h =>
      hz ((discreteDiameter_pos_iff (by omega : 2 ≤ n + 1)).mp h)
    have hzero : discreteDiameter z = 0 :=
      le_antisymm (not_lt.mp hnpos) (discreteDiameter_nonneg _)
    rw [hzero]
    exact le_csSup hbddn (zero_mem_unitDiscDiameters hn)

/-- `0 ≤ dₙ ≤ 2` for the `n`-point transfinite diameter of the closed unit disc
(`n ≥ 2`): the monotone sequence of `transfiniteDiameterN_succ_le` is bounded, so its
infimum — the transfinite diameter of the disc — is well-defined. -/
theorem transfiniteDiameterN_mem_Icc (hn : 2 ≤ n) :
    transfiniteDiameterN n ∈ Set.Icc (0 : ℝ) 2 := by
  constructor
  · exact le_csSup (unitDiscDiameters_bddAbove hn) (zero_mem_unitDiscDiameters hn)
  · exact csSup_le (unitDiscDiameters_nonempty hn)
      (by rintro d ⟨z, hz, rfl⟩; exact discreteDiameter_le_two hn hz)

/-! ### The transfinite diameter of the closed unit disc as a limit

The sequence `dₙ = transfiniteDiameterN n` is non-increasing for `n ≥ 2`
(`transfiniteDiameterN_succ_le`) and bounded in `[0,2]`
(`transfiniteDiameterN_mem_Icc`). A bounded, monotone-decreasing real sequence
converges to its infimum, so the **transfinite diameter of the disc**
`d = infₙ dₙ = limₙ dₙ` is a well-defined real number in `[0,2]`. Its exact value
(`= 1`, the logarithmic capacity of the unit disc) requires the Fekete–Szegő
theorem and extremal root-of-unity configurations, and is not established here. -/

open Filter Topology

/-- The **transfinite diameter of the closed unit disc**, `d = ⨅ₙ dₙ`. Indexed as
`n ↦ d_{n+2}` so the entire sequence lies in the `n ≥ 2` monotone regime where
`transfiniteDiameterN_succ_le` applies. -/
noncomputable def transfiniteDiameter : ℝ := ⨅ n : ℕ, transfiniteDiameterN (n + 2)

/-- The shifted sequence `n ↦ d_{n+2}` is antitone — this is Fekete monotonicity
(`transfiniteDiameterN_succ_le`) packaged over the shifted index. -/
theorem transfiniteDiameterN_shift_antitone :
    Antitone (fun n : ℕ => transfiniteDiameterN (n + 2)) :=
  antitone_nat_of_succ_le (fun n => transfiniteDiameterN_succ_le (by omega))

/-- The shifted sequence `n ↦ d_{n+2}` is bounded below by `0`
(`transfiniteDiameterN_mem_Icc`), so its infimum exists. -/
theorem transfiniteDiameterN_shift_bddBelow :
    BddBelow (Set.range (fun n : ℕ => transfiniteDiameterN (n + 2))) := by
  refine ⟨0, ?_⟩
  rintro x ⟨n, rfl⟩
  exact (transfiniteDiameterN_mem_Icc (by omega)).1

/-- **The `n`-point diameters converge to the transfinite diameter.** Being an
antitone sequence bounded below, `d_{n+2} → ⨅ₙ d_{n+2} = d` as `n → ∞`. This makes
`transfiniteDiameter` a genuine limit, not merely an infimum. -/
theorem tendsto_transfiniteDiameterN :
    Tendsto (fun n : ℕ => transfiniteDiameterN (n + 2)) atTop
      (nhds transfiniteDiameter) :=
  tendsto_atTop_ciInf transfiniteDiameterN_shift_antitone transfiniteDiameterN_shift_bddBelow

/-- **The transfinite diameter of the disc lies in `[0,2]`.** As the infimum of the
`[0,2]`-valued sequence `dₙ`, it inherits both bounds. (The sharp value `d = 1` is
the deep Fekete–Szegő content, not established here.) -/
theorem transfiniteDiameter_mem_Icc : transfiniteDiameter ∈ Set.Icc (0 : ℝ) 2 := by
  constructor
  · exact le_ciInf (fun n => (transfiniteDiameterN_mem_Icc (by omega)).1)
  · exact ciInf_le_of_le transfiniteDiameterN_shift_bddBelow 0
      (transfiniteDiameterN_mem_Icc (by omega)).2

/-- Every finite-stage diameter dominates the transfinite diameter: `d ≤ d_{n+2}`
for all `n`.  The limit sits below the whole monotone sequence. -/
theorem transfiniteDiameter_le (n : ℕ) :
    transfiniteDiameter ≤ transfiniteDiameterN (n + 2) :=
  ciInf_le transfiniteDiameterN_shift_bddBelow n

/-! ### The first term is exact: `d₂ = 2`

The `2`-point diameter reduces to the single gap `d₂(z) = ‖z₀ - z₁‖`, whose
supremum over the closed unit disc is `2`, attained by the antipodal pair
`{1, -1}`.  This is the only stage of the sequence whose value is elementary
(the sharp `d = 1` for the disc is the deep Fekete–Szegő content); it pins the
top of the monotone sequence exactly and shows the uniform bound
`dₙ ≤ 2` is attained at `n = 2`. -/

/-- The spread product of a `2`-point configuration is the single gap
`‖z₀ - z₁‖` (the only pair `i < j` in `Fin 2`). -/
theorem spreadProduct_two (z : Fin 2 → ℂ) : spreadProduct z = ‖z 0 - z 1‖ := by
  unfold spreadProduct
  rw [Fin.prod_univ_two]
  have h0 : Finset.Ioi (0 : Fin 2) = {1} := by decide
  have h1 : Finset.Ioi (1 : Fin 2) = (∅ : Finset (Fin 2)) := by decide
  rw [h0, h1, Finset.prod_singleton, Finset.prod_empty, mul_one]

/-- The `2`-point diameter is exactly the gap `‖z₀ - z₁‖`: the normalising
exponent `2/(n(n-1))` equals `1` at `n = 2`. -/
theorem discreteDiameter_two (z : Fin 2 → ℂ) :
    discreteDiameter z = ‖z 0 - z 1‖ := by
  rw [discreteDiameter, spreadProduct_two]
  norm_num

/-- **`d₂ = 2`.**  The `2`-point transfinite diameter of the closed unit disc is
exactly `2`, attained by the antipodal configuration `{1, -1}`: the upper bound
`d₂ ≤ 2` (from `discreteDiameter_le_two`) is achieved, since
`d₂({1,-1}) = ‖1 - (-1)‖ = 2`. -/
theorem transfiniteDiameterN_two : transfiniteDiameterN 2 = 2 := by
  refine le_antisymm (transfiniteDiameterN_mem_Icc (le_refl 2)).2 ?_
  have hwit : discreteDiameter (![(1 : ℂ), -1]) = 2 := by
    rw [discreteDiameter_two]
    norm_num
  refine le_csSup (unitDiscDiameters_bddAbove (le_refl 2))
    ⟨![(1 : ℂ), -1], ?_, hwit⟩
  intro i
  fin_cases i <;> norm_num

/-- **The transfinite diameter of the disc is at most `2`, sharply.**  Since
`d = ⨅ₙ d_{n+2}` and the first term `d₂ = 2` (`transfiniteDiameterN_two`), the
bound `d ≤ 2` from `transfiniteDiameter_mem_Icc` is exactly the `n = 0` term of
the defining infimum. -/
theorem transfiniteDiameter_le_two_via_d2 :
    transfiniteDiameter ≤ 2 := by
  have := transfiniteDiameter_le 0
  rwa [transfiniteDiameterN_two] at this

/-! ### The second term is sandwiched: `√3 ≤ d₃ ≤ 2`

The `3`-point diameter is the geometric mean of the three pairwise gaps,
`d₃(z) = (‖z₀-z₁‖·‖z₀-z₂‖·‖z₁-z₂‖)^{1/3}` (the normalising exponent
`2/(n(n-1))` equals `1/3` at `n = 3`).  The equilateral triangle of cube roots of
unity `{1, ω, ω²}` with `ω = -1/2 + (√3/2)i` lies on the unit circle and has all
three gaps equal to `√3`, so its diameter is `((√3)³)^{1/3} = √3`.  This yields
the sharp **lower bound** `d₃ ≥ √3`; combined with Fekete monotonicity
`d₃ ≤ d₂ = 2` (`transfiniteDiameterN_succ_le`, `transfiniteDiameterN_two`) it
sandwiches the second term of the sequence in `[√3, 2]`.

The matching **upper bound** `d₃ = √3` — that no `3`-point configuration in the
closed unit disc beats the inscribed equilateral triangle — is a genuine extremal
optimisation (the `n = 3` case of the Fekete–Szegő theorem) and is *not*
established here; only the elementary lower bound is. -/

/-- The Euclidean norm of a complex number written in Cartesian form:
`‖x + yi‖ = √(x² + y²)`. -/
private theorem norm_mk_eq_sqrt (x y : ℝ) :
    ‖(⟨x, y⟩ : ℂ)‖ = Real.sqrt (x ^ 2 + y ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg (⟨x, y⟩ : ℂ)), ← Complex.normSq_eq_norm_sq,
    Complex.normSq_mk]
  congr 1
  ring

/-- The spread product of a `3`-point configuration is the product of its three
pairwise gaps `‖z₀-z₁‖·‖z₀-z₂‖·‖z₁-z₂‖` (the three pairs `i < j` in `Fin 3`). -/
theorem spreadProduct_three (z : Fin 3 → ℂ) :
    spreadProduct z = ‖z 0 - z 1‖ * ‖z 0 - z 2‖ * ‖z 1 - z 2‖ := by
  unfold spreadProduct
  rw [Fin.prod_univ_three]
  have h0 : Finset.Ioi (0 : Fin 3) = {1, 2} := by decide
  have h1 : Finset.Ioi (1 : Fin 3) = {2} := by decide
  have h2 : Finset.Ioi (2 : Fin 3) = (∅ : Finset (Fin 3)) := by decide
  rw [h0, h1, h2, Finset.prod_pair (by decide : (1 : Fin 3) ≠ 2),
    Finset.prod_singleton, Finset.prod_empty, mul_one]

/-- The `3`-point diameter is the geometric mean of the three pairwise gaps:
the normalising exponent `2/(n(n-1))` equals `1/3` at `n = 3`. -/
theorem discreteDiameter_three (z : Fin 3 → ℂ) :
    discreteDiameter z
      = (‖z 0 - z 1‖ * ‖z 0 - z 2‖ * ‖z 1 - z 2‖) ^ ((1 : ℝ) / 3) := by
  rw [discreteDiameter, spreadProduct_three]
  norm_num

/-- **`d₃ ≥ √3`.**  The `3`-point transfinite diameter of the closed unit disc is
at least `√3`, attained by the equilateral triangle of cube roots of unity
`{1, ω, ω²}` with `ω = -1/2 + (√3/2)i`: all three pairwise gaps equal `√3`, so its
`3`-point diameter is `((√3)³)^{1/3} = √3`.  Together with `d₃ ≤ d₂ = 2` this pins
the second term of the sequence into `[√3, 2]`. -/
theorem transfiniteDiameterN_three_ge : Real.sqrt 3 ≤ transfiniteDiameterN 3 := by
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  -- the equilateral triangle of cube roots of unity
  set z : Fin 3 → ℂ := ![1, ⟨-1/2, Real.sqrt 3/2⟩, ⟨-1/2, -(Real.sqrt 3/2)⟩]
    with hz_def
  have e0 : z 0 = 1 := by simp [hz_def]
  have e1 : z 1 = (⟨-1/2, Real.sqrt 3/2⟩ : ℂ) := by simp [hz_def]
  have e2 : z 2 = (⟨-1/2, -(Real.sqrt 3/2)⟩ : ℂ) := by simp [hz_def]
  -- the three pairwise gaps are all √3
  have g01 : ‖z 0 - z 1‖ = Real.sqrt 3 := by
    have hd : z 0 - z 1 = (⟨3/2, -(Real.sqrt 3/2)⟩ : ℂ) := by
      rw [e0, e1, Complex.ext_iff]
      norm_num [Complex.sub_re, Complex.sub_im]
    rw [hd, norm_mk_eq_sqrt,
      show ((3:ℝ)/2) ^ 2 + (-(Real.sqrt 3/2)) ^ 2 = (9 + Real.sqrt 3 ^ 2) / 4 by ring,
      hs2]
    norm_num
  have g02 : ‖z 0 - z 2‖ = Real.sqrt 3 := by
    have hd : z 0 - z 2 = (⟨3/2, Real.sqrt 3/2⟩ : ℂ) := by
      rw [e0, e2, Complex.ext_iff]
      norm_num [Complex.sub_re, Complex.sub_im]
    rw [hd, norm_mk_eq_sqrt,
      show ((3:ℝ)/2) ^ 2 + (Real.sqrt 3/2) ^ 2 = (9 + Real.sqrt 3 ^ 2) / 4 by ring,
      hs2]
    norm_num
  have g12 : ‖z 1 - z 2‖ = Real.sqrt 3 := by
    have hd : z 1 - z 2 = (⟨0, Real.sqrt 3⟩ : ℂ) := by
      rw [e1, e2, Complex.ext_iff]
      norm_num [Complex.sub_re, Complex.sub_im]
    rw [hd, norm_mk_eq_sqrt,
      show (0:ℝ) ^ 2 + Real.sqrt 3 ^ 2 = Real.sqrt 3 ^ 2 by ring, hs2]
  -- the diameter of this configuration is exactly √3
  have hdiam : discreteDiameter z = Real.sqrt 3 := by
    rw [discreteDiameter_three, g01, g02, g12,
      show Real.sqrt 3 * Real.sqrt 3 * Real.sqrt 3 = Real.sqrt 3 ^ (3 : ℕ) by ring,
      ← Real.rpow_natCast (Real.sqrt 3) 3,
      ← Real.rpow_mul (Real.sqrt_nonneg 3)]
    norm_num
  -- every vertex lies in the closed unit disc
  have n0 : ‖z 0‖ ≤ 1 := by rw [e0]; simp
  have n1 : ‖z 1‖ ≤ 1 := by
    rw [e1, norm_mk_eq_sqrt,
      show (-1/2:ℝ) ^ 2 + (Real.sqrt 3/2) ^ 2 = (1 + Real.sqrt 3 ^ 2) / 4 by ring, hs2,
      show ((1:ℝ) + 3) / 4 = 1 by norm_num, Real.sqrt_one]
  have n2 : ‖z 2‖ ≤ 1 := by
    rw [e2, norm_mk_eq_sqrt,
      show (-1/2:ℝ) ^ 2 + (-(Real.sqrt 3/2)) ^ 2 = (1 + Real.sqrt 3 ^ 2) / 4 by ring, hs2,
      show ((1:ℝ) + 3) / 4 = 1 by norm_num, Real.sqrt_one]
  have hmem : ∀ i, ‖z i‖ ≤ 1 := by
    intro i; fin_cases i
    · exact n0
    · exact n1
    · exact n2
  -- √3 is realised as the diameter of a disc configuration, hence ≤ the sSup
  have hin : Real.sqrt 3 ∈ unitDiscDiameters 3 := ⟨z, hmem, hdiam⟩
  exact le_csSup (unitDiscDiameters_bddAbove (by norm_num)) hin

/-- **The second term is sandwiched: `d₃ ∈ [√3, 2]`.**  The lower bound is
`transfiniteDiameterN_three_ge` (cube roots of unity); the upper bound is Fekete
monotonicity `d₃ ≤ d₂` (`transfiniteDiameterN_succ_le`) composed with the exact
first term `d₂ = 2` (`transfiniteDiameterN_two`).  The exact value `d₃ = √3` needs
the extremal upper bound and is not established here. -/
theorem transfiniteDiameterN_three_mem_Icc :
    transfiniteDiameterN 3 ∈ Set.Icc (Real.sqrt 3) 2 := by
  refine ⟨transfiniteDiameterN_three_ge, ?_⟩
  have h32 : transfiniteDiameterN 3 ≤ transfiniteDiameterN 2 :=
    transfiniteDiameterN_succ_le (le_refl 2)
  rwa [transfiniteDiameterN_two] at h32

/-! ### The third term `d₄ ≥ 4^{1/3}`: the square of fourth roots of unity

The `4`-point diameter is the geometric mean of the `6` pairwise gaps,
`d₄(z) = (∏_{i<j}‖zᵢ-zⱼ‖)^{1/6}` (the normalising exponent `2/(n(n-1))` equals
`1/6` at `n = 4`).  The square `{1, i, -1, -i}` of fourth roots of unity has four
side gaps equal to `√2` and two diagonal gaps equal to `2`, so its spread product
is `(√2)⁴·2² = 16` and its diameter is `16^{1/6} = 4^{1/3}`.  This yields the sharp
**lower bound** `d₄ ≥ 4^{1/3}`.

Together with `d₂ = 2 = 2^{1/(2-1)}` (`transfiniteDiameterN_two`) and
`d₃ ≥ √3 = 3^{1/(3-1)}` (`transfiniteDiameterN_three_ge`), the value `4^{1/3} =
4^{1/(4-1)}` makes the general pattern `dₙ ≥ n^{1/(n-1)}` (roots of unity,
Vandermonde discriminant `n^{n/2}`) visible; that general lower bound — which
gives `d = limₙ dₙ ≥ 1`, matching the logarithmic capacity of the disc — is the
next milestone (`spreadProduct` of the `n`-th roots of unity `= n^{n/2}` via the
derivative-at-a-root formula `∏_{j≠k}(ζᵏ-ζʲ) = n·ζ^{k(n-1)}`).  The matching
upper bound `d₄ = 4^{1/3}` needs the Fekete–Szegő extremal theorem and is not
established here. -/

/-- The spread product of a `4`-point configuration is the product of its six
pairwise gaps (the six pairs `i < j` in `Fin 4`). -/
theorem spreadProduct_four (z : Fin 4 → ℂ) :
    spreadProduct z = ‖z 0 - z 1‖ * ‖z 0 - z 2‖ * ‖z 0 - z 3‖ *
      (‖z 1 - z 2‖ * ‖z 1 - z 3‖) * ‖z 2 - z 3‖ := by
  unfold spreadProduct
  rw [Fin.prod_univ_four]
  have h0 : Finset.Ioi (0 : Fin 4) = {1, 2, 3} := by decide
  have h1 : Finset.Ioi (1 : Fin 4) = {2, 3} := by decide
  have h2 : Finset.Ioi (2 : Fin 4) = {3} := by decide
  have h3 : Finset.Ioi (3 : Fin 4) = (∅ : Finset (Fin 4)) := by decide
  rw [h0, h1, h2, h3,
    Finset.prod_insert (by decide : (1 : Fin 4) ∉ ({2, 3} : Finset (Fin 4))),
    Finset.prod_pair (by decide : (2 : Fin 4) ≠ 3),
    Finset.prod_pair (by decide : (2 : Fin 4) ≠ 3),
    Finset.prod_singleton, Finset.prod_empty, mul_one]
  ring

/-- The `4`-point diameter is the geometric mean of the six pairwise gaps:
the normalising exponent `2/(n(n-1))` equals `1/6` at `n = 4`. -/
theorem discreteDiameter_four (z : Fin 4 → ℂ) :
    discreteDiameter z = (‖z 0 - z 1‖ * ‖z 0 - z 2‖ * ‖z 0 - z 3‖ *
      (‖z 1 - z 2‖ * ‖z 1 - z 3‖) * ‖z 2 - z 3‖) ^ ((1 : ℝ) / 6) := by
  rw [discreteDiameter, spreadProduct_four]
  norm_num

/-- **`d₄ ≥ 4^{1/3}`.**  The `4`-point transfinite diameter of the closed unit disc
is at least `4^{1/3}`, attained by the square of fourth roots of unity
`{1, i, -1, -i}`: its four side gaps equal `√2` and its two diagonal gaps equal `2`,
so its spread product is `(√2)⁴·2² = 16` and its `4`-point diameter is
`16^{1/6} = 4^{1/3}`.  This is the third term of the sharp lower bound
`dₙ ≥ n^{1/(n-1)}` (after `d₂ = 2` and `d₃ ≥ √3`). -/
theorem transfiniteDiameterN_four_ge : (4 : ℝ) ^ ((1 : ℝ) / 3) ≤ transfiniteDiameterN 4 := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  -- the square of fourth roots of unity
  set z : Fin 4 → ℂ := ![1, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, -1⟩] with hz_def
  have e0 : z 0 = 1 := by simp [hz_def]
  have e1 : z 1 = (⟨0, 1⟩ : ℂ) := by simp [hz_def]
  have e2 : z 2 = (⟨-1, 0⟩ : ℂ) := by simp [hz_def]
  have e3 : z 3 = (⟨0, -1⟩ : ℂ) := by simp [hz_def]
  -- the four side gaps are √2, the two diagonal gaps are 2
  have g01 : ‖z 0 - z 1‖ = Real.sqrt 2 := by
    have hd : z 0 - z 1 = (⟨1, -1⟩ : ℂ) := by
      rw [e0, e1, Complex.ext_iff]; norm_num [Complex.sub_re, Complex.sub_im]
    rw [hd, norm_mk_eq_sqrt, show (1 : ℝ) ^ 2 + (-1 : ℝ) ^ 2 = 2 by norm_num]
  have g02 : ‖z 0 - z 2‖ = 2 := by
    have hd : z 0 - z 2 = (⟨2, 0⟩ : ℂ) := by
      rw [e0, e2, Complex.ext_iff]; norm_num [Complex.sub_re, Complex.sub_im]
    rw [hd, norm_mk_eq_sqrt, show (2 : ℝ) ^ 2 + (0 : ℝ) ^ 2 = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have g03 : ‖z 0 - z 3‖ = Real.sqrt 2 := by
    have hd : z 0 - z 3 = (⟨1, 1⟩ : ℂ) := by
      rw [e0, e3, Complex.ext_iff]; norm_num [Complex.sub_re, Complex.sub_im]
    rw [hd, norm_mk_eq_sqrt, show (1 : ℝ) ^ 2 + (1 : ℝ) ^ 2 = 2 by norm_num]
  have g12 : ‖z 1 - z 2‖ = Real.sqrt 2 := by
    have hd : z 1 - z 2 = (⟨1, 1⟩ : ℂ) := by
      rw [e1, e2, Complex.ext_iff]; norm_num [Complex.sub_re, Complex.sub_im]
    rw [hd, norm_mk_eq_sqrt, show (1 : ℝ) ^ 2 + (1 : ℝ) ^ 2 = 2 by norm_num]
  have g13 : ‖z 1 - z 3‖ = 2 := by
    have hd : z 1 - z 3 = (⟨0, 2⟩ : ℂ) := by
      rw [e1, e3, Complex.ext_iff]; norm_num [Complex.sub_re, Complex.sub_im]
    rw [hd, norm_mk_eq_sqrt, show (0 : ℝ) ^ 2 + (2 : ℝ) ^ 2 = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have g23 : ‖z 2 - z 3‖ = Real.sqrt 2 := by
    have hd : z 2 - z 3 = (⟨-1, 1⟩ : ℂ) := by
      rw [e2, e3, Complex.ext_iff]; norm_num [Complex.sub_re, Complex.sub_im]
    rw [hd, norm_mk_eq_sqrt, show (-1 : ℝ) ^ 2 + (1 : ℝ) ^ 2 = 2 by norm_num]
  -- the numeric identity `16^{1/6} = 4^{1/3}`
  have hnum : (16 : ℝ) ^ ((1 : ℝ) / 6) = (4 : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [show (16 : ℝ) = (4 : ℝ) ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast (4 : ℝ) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  -- the diameter of the square is exactly 4^{1/3}
  have hdiam : discreteDiameter z = (4 : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [discreteDiameter_four, g01, g02, g03, g12, g13, g23]
    have hp16 : Real.sqrt 2 * 2 * Real.sqrt 2 * (Real.sqrt 2 * 2) * Real.sqrt 2
        = (16 : ℝ) := by
      have e : Real.sqrt 2 * 2 * Real.sqrt 2 * (Real.sqrt 2 * 2) * Real.sqrt 2
          = (Real.sqrt 2 ^ 2) ^ 2 * 4 := by ring
      rw [e, hs2]; norm_num
    rw [hp16, hnum]
  -- every vertex lies in the closed unit disc
  have n0 : ‖z 0‖ ≤ 1 := by rw [e0]; simp
  have n1 : ‖z 1‖ ≤ 1 := by
    rw [e1, norm_mk_eq_sqrt, show (0 : ℝ) ^ 2 + (1 : ℝ) ^ 2 = 1 by norm_num, Real.sqrt_one]
  have n2 : ‖z 2‖ ≤ 1 := by
    rw [e2, norm_mk_eq_sqrt, show (-1 : ℝ) ^ 2 + (0 : ℝ) ^ 2 = 1 by norm_num, Real.sqrt_one]
  have n3 : ‖z 3‖ ≤ 1 := by
    rw [e3, norm_mk_eq_sqrt, show (0 : ℝ) ^ 2 + (-1 : ℝ) ^ 2 = 1 by norm_num, Real.sqrt_one]
  have hmem : ∀ i, ‖z i‖ ≤ 1 := by
    intro i; fin_cases i
    · exact n0
    · exact n1
    · exact n2
    · exact n3
  -- 4^{1/3} is realised as the diameter of a disc configuration, hence ≤ the sSup
  have hin : (4 : ℝ) ^ ((1 : ℝ) / 3) ∈ unitDiscDiameters 4 := ⟨z, hmem, hdiam⟩
  exact le_csSup (unitDiscDiameters_bddAbove (by norm_num)) hin

/-- **The third term is bounded below: `d₄ ≥ 4^{1/3}`, and `d₄ ∈ [4^{1/3}, 2]`.**  The
lower bound is `transfiniteDiameterN_four_ge` (square of fourth roots of unity); the
upper bound is Fekete monotonicity `d₄ ≤ d₂ = 2` (`transfiniteDiameterN_succ_le`
twice, composed with `transfiniteDiameterN_two`).  The exact value `d₄ = 4^{1/3}`
needs the extremal upper bound and is not established here. -/
theorem transfiniteDiameterN_four_mem_Icc :
    transfiniteDiameterN 4 ∈ Set.Icc ((4 : ℝ) ^ ((1 : ℝ) / 3)) 2 := by
  refine ⟨transfiniteDiameterN_four_ge, ?_⟩
  have h43 : transfiniteDiameterN 4 ≤ transfiniteDiameterN 3 :=
    transfiniteDiameterN_succ_le (by norm_num)
  have h32 : transfiniteDiameterN 3 ≤ transfiniteDiameterN 2 :=
    transfiniteDiameterN_succ_le (le_refl 2)
  rw [transfiniteDiameterN_two] at h32
  linarith

/-! ### The general lower bound `dₙ ≥ n^{1/(n-1)}`: the `n`-th roots of unity

The `n = m+2` complex `n`-th roots of unity `ζᵏ` (`ζ = exp(2πi/n)`, a primitive
`n`-th root) all lie on the unit circle, so they form a configuration in the closed
unit disc.  Their spread product is the **Vandermonde discriminant** `n^{n/2}`:

* For each fixed index `i`, the product over `j ≠ i` telescopes — after the
  translation `j ↦ j - i` on `Fin n` and factoring out the unit `ζⁱ` — to
  `∏_{k=1}^{n-1}‖1 - ζᵏ‖ = |∏_{k=1}^{n-1}(1 - ζᵏ)| = |n| = n`, using the classical
  identity `∏_{k=1}^{n-1}(1 - ζᵏ) = n` (`IsPrimitiveRoot.prod_one_sub_pow_eq_order`).
* Multiplying `∏_{j≠i} = n` over the `n` values of `i` gives the *ordered*
  off-diagonal product `n^n`, which equals `(spreadProduct)²` because the lower and
  upper triangles `{j < i}` and `{i < j}` carry equal products (`‖zᵢ-zⱼ‖ = ‖zⱼ-zᵢ‖`).

Hence `spreadProduct = n^{n/2}` and
`dₙ(roots of unity) = (n^{n/2})^{2/(n(n-1))} = n^{1/(n-1)}`, giving the sharp lower
bound `dₙ ≥ n^{1/(n-1)}`.  Passing to the limit, every term of `d = infₙ dₙ` is `≥ 1`
(`n^{1/(n-1)} ≥ 1`), so `d ≥ 1` — the logarithmic capacity of the closed unit disc.
This generalises the exact terms `d₂ = 2`, `d₃ ≥ √3`, `d₄ ≥ 4^{1/3}` above.  The
matching Fekete–Szegő *upper* bound (`d = 1` exactly) is not established here. -/

/-- The `n`-point **roots-of-unity configuration** `k ↦ ζᵏ` for a primitive root `ζ`. -/
noncomputable def rootConfig (ζ : ℂ) (N : ℕ) : Fin N → ℂ := fun k => ζ ^ (k : ℕ)

section RootsOfUnity

open Complex

variable {m : ℕ} {ζ : ℂ}

/-- Every power of a primitive `(m+2)`-th root of unity has modulus `1`. -/
private theorem rou_norm (hζ : IsPrimitiveRoot ζ (m + 2)) (k : ℕ) : ‖ζ ^ k‖ = 1 := by
  rw [norm_pow, Complex.norm_eq_one_of_pow_eq_one hζ.pow_eq_one (by omega), one_pow]

/-- Powers of `ζ` (order `m+2`) only depend on the exponent modulo `m+2`. -/
private theorem rou_mod (hζ : IsPrimitiveRoot ζ (m + 2)) (a : ℕ) :
    ζ ^ (a % (m + 2)) = ζ ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a (m + 2)]
  rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]

/-- **Core discriminant value.**  `∏_{d ≠ 0} ‖1 - ζᵈ‖ = m + 2` over `Fin (m+2)`,
the modulus of the classical identity `∏_{k=1}^{n-1}(1 - ζᵏ) = n`. -/
private theorem prod_erase_zero (hζ : IsPrimitiveRoot ζ (m + 2)) :
    ∏ d ∈ (Finset.univ : Finset (Fin (m + 2))).erase 0, ‖1 - ζ ^ (d : ℕ)‖ = ((m : ℝ) + 2) := by
  haveI : NeZero (m + 2) := ⟨by omega⟩
  have hreindex : ∏ d ∈ (Finset.univ : Finset (Fin (m + 2))).erase 0, ‖1 - ζ ^ (d : ℕ)‖
      = ∏ k ∈ Finset.range (m + 1), ‖1 - ζ ^ (k + 1)‖ := by
    apply Finset.prod_nbij' (fun d : Fin (m + 2) => (d : ℕ) - 1)
      (fun k : ℕ => (⟨(k + 1) % (m + 2), Nat.mod_lt _ (by omega)⟩ : Fin (m + 2)))
    · intro d _
      simp only [Finset.mem_range]
      have := d.isLt; omega
    · intro k hk
      simp only [Finset.mem_range] at hk
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      apply Fin.ne_of_val_ne
      show (k + 1) % (m + 2) ≠ (0 : Fin (m + 2)).val
      rw [Fin.val_zero, Nat.mod_eq_of_lt (show k + 1 < m + 2 by omega)]
      omega
    · intro d hd
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hd
      have hpos : 1 ≤ (d : ℕ) := by
        rcases Nat.eq_zero_or_pos (d : ℕ) with h | h
        · exact absurd (Fin.val_eq_zero_iff.mp h) hd
        · exact h
      apply Fin.ext
      show ((d : ℕ) - 1 + 1) % (m + 2) = (d : ℕ)
      rw [Nat.sub_add_cancel hpos, Nat.mod_eq_of_lt d.isLt]
    · intro k hk
      simp only [Finset.mem_range] at hk
      show (k + 1) % (m + 2) - 1 = k
      rw [Nat.mod_eq_of_lt (show k + 1 < m + 2 by omega)]
      omega
    · intro d hd
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hd
      have hpos : 1 ≤ (d : ℕ) := by
        rcases Nat.eq_zero_or_pos (d : ℕ) with h | h
        · exact absurd (Fin.val_eq_zero_iff.mp h) hd
        · exact h
      rw [Nat.sub_add_cancel hpos]
  rw [hreindex, ← norm_prod, hζ.prod_one_sub_pow_eq_order]
  rw [show ((m + 1 : ℕ) : ℂ) + 1 = ((m + 2 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
  push_cast; ring

/-- **Per-index spread.**  For each index `i`, `∏_{j ≠ i} ‖ζⁱ - ζʲ‖ = m + 2`:
after translating `j ↦ j - i` and pulling out the unit `ζⁱ`, this is `prod_erase_zero`. -/
private theorem prod_erase_root (hζ : IsPrimitiveRoot ζ (m + 2)) (i : Fin (m + 2)) :
    ∏ j ∈ (Finset.univ : Finset (Fin (m + 2))).erase i,
      ‖rootConfig ζ (m + 2) i - rootConfig ζ (m + 2) j‖ = ((m : ℝ) + 2) := by
  simp only [rootConfig]
  have hfactor : ∀ j ∈ (Finset.univ : Finset (Fin (m + 2))).erase i,
      ‖ζ ^ (i : ℕ) - ζ ^ (j : ℕ)‖ = ‖1 - ζ ^ ((j - i : Fin (m + 2)) : ℕ)‖ := by
    intro j _
    have key : ζ ^ (i : ℕ) * ζ ^ ((j - i : Fin (m + 2)) : ℕ) = ζ ^ (j : ℕ) := by
      rw [← pow_add, ← rou_mod hζ ((i : ℕ) + ((j - i : Fin (m + 2)) : ℕ))]
      congr 1
      rw [← Fin.val_add]
      congr 1
      abel
    have harg : ζ ^ (i : ℕ) - ζ ^ (j : ℕ)
        = ζ ^ (i : ℕ) * (1 - ζ ^ ((j - i : Fin (m + 2)) : ℕ)) := by
      rw [mul_sub, mul_one, key]
    rw [harg, norm_mul, rou_norm hζ, one_mul]
  -- translation reindex `Fin (m+2) → Fin (m+2)`, `j ↦ j - i`, sends `erase i` to `erase 0`
  rw [Finset.prod_congr rfl hfactor,
    show (∏ j ∈ (Finset.univ : Finset (Fin (m + 2))).erase i,
          ‖1 - ζ ^ ((j - i : Fin (m + 2)) : ℕ)‖)
        = ∏ d ∈ (Finset.univ : Finset (Fin (m + 2))).erase 0, ‖1 - ζ ^ (d : ℕ)‖ from
      Finset.prod_equiv
        (⟨fun j => j - i, fun d => d + i, fun j => by simp, fun d => by simp⟩ :
          Fin (m + 2) ≃ Fin (m + 2))
        (fun a => by
          simp only [Finset.mem_erase, Finset.mem_univ, and_true, Equiv.coe_fn_mk, sub_ne_zero])
        (fun a _ => by simp only [Equiv.coe_fn_mk]),
    prod_erase_zero hζ]

/-- **Vandermonde discriminant of the roots of unity.**  `(spreadProduct)² = n^n`
for the `n = m+2` roots-of-unity configuration. -/
private theorem spreadProduct_rootConfig_sq (hζ : IsPrimitiveRoot ζ (m + 2)) :
    (spreadProduct (rootConfig ζ (m + 2))) ^ 2 = ((m : ℝ) + 2) ^ (m + 2) := by
  have hsplit : ∀ i : Fin (m + 2),
      (Finset.univ : Finset (Fin (m + 2))).erase i = Finset.Iio i ∪ Finset.Ioi i := by
    intro i; ext a
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_Iio,
      Finset.mem_Ioi]
    exact lt_or_lt_iff_ne.symm
  have hdisj : ∀ i : Fin (m + 2), Disjoint (Finset.Iio i) (Finset.Ioi i) := by
    intro i; rw [Finset.disjoint_left]; intro a ha ha'
    exact absurd (Finset.mem_Iio.mp ha) (not_lt.mpr (le_of_lt (Finset.mem_Ioi.mp ha')))
  -- lower triangle equals the spread product (via `norm_sub_rev` and Fubini)
  have hlow : (∏ i, ∏ j ∈ Finset.Iio i, ‖rootConfig ζ (m + 2) i - rootConfig ζ (m + 2) j‖)
      = spreadProduct (rootConfig ζ (m + 2)) := by
    rw [Finset.prod_comm' (s := (Finset.univ : Finset (Fin (m + 2)))) (t := fun i => Finset.Iio i)
      (t' := (Finset.univ : Finset (Fin (m + 2)))) (s' := fun j => Finset.Ioi j)
      (fun x y => by
        simp only [Finset.mem_univ, Finset.mem_Iio, Finset.mem_Ioi, true_and, and_true])]
    unfold spreadProduct
    exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => norm_sub_rev _ _
  -- the ordered off-diagonal product is the square of the spread product …
  have hsq : (∏ i, ∏ j ∈ (Finset.univ : Finset (Fin (m + 2))).erase i,
      ‖rootConfig ζ (m + 2) i - rootConfig ζ (m + 2) j‖)
      = (spreadProduct (rootConfig ζ (m + 2))) ^ 2 := by
    have herase : ∀ i : Fin (m + 2),
        (∏ j ∈ (Finset.univ : Finset (Fin (m + 2))).erase i,
          ‖rootConfig ζ (m + 2) i - rootConfig ζ (m + 2) j‖)
        = (∏ j ∈ Finset.Iio i, ‖rootConfig ζ (m + 2) i - rootConfig ζ (m + 2) j‖)
          * (∏ j ∈ Finset.Ioi i, ‖rootConfig ζ (m + 2) i - rootConfig ζ (m + 2) j‖) := by
      intro i; rw [hsplit i, Finset.prod_union (hdisj i)]
    have hup : (∏ i, ∏ j ∈ Finset.Ioi i,
        ‖rootConfig ζ (m + 2) i - rootConfig ζ (m + 2) j‖)
        = spreadProduct (rootConfig ζ (m + 2)) := rfl
    rw [Finset.prod_congr rfl (fun i _ => herase i), Finset.prod_mul_distrib, hlow, hup, sq]
  -- … and it is also `n^n`, since each factor is `n`.
  have hval : (∏ i, ∏ j ∈ (Finset.univ : Finset (Fin (m + 2))).erase i,
      ‖rootConfig ζ (m + 2) i - rootConfig ζ (m + 2) j‖) = ((m : ℝ) + 2) ^ (m + 2) := by
    rw [Finset.prod_congr rfl (fun i _ => prod_erase_root hζ i), Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  rw [← hsq, hval]

/-- **The `n`-point diameter of the roots of unity is `n^{1/(n-1)}`.** -/
private theorem discreteDiameter_rootConfig (hζ : IsPrimitiveRoot ζ (m + 2)) :
    discreteDiameter (rootConfig ζ (m + 2)) = ((m : ℝ) + 2) ^ ((1 : ℝ) / ((m : ℝ) + 1)) := by
  have hSsq : (spreadProduct (rootConfig ζ (m + 2))) ^ 2 = ((m : ℝ) + 2) ^ (m + 2) :=
    spreadProduct_rootConfig_sq hζ
  have hSnn : 0 ≤ spreadProduct (rootConfig ζ (m + 2)) := spreadProduct_nonneg _
  have hbase : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have h1 : (m : ℝ) + 2 ≠ 0 := by positivity
  have h2 : (m : ℝ) + 1 ≠ 0 := by positivity
  unfold discreteDiameter
  set e : ℝ := 2 / (((m + 2 : ℕ) : ℝ) * (((m + 2 : ℕ) : ℝ) - 1)) with he
  rw [show e = 2 * (e / 2) by ring, Real.rpow_mul hSnn,
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hSsq,
    ← Real.rpow_natCast ((m : ℝ) + 2) (m + 2), ← Real.rpow_mul (le_of_lt hbase)]
  congr 1
  rw [he, show (((m + 2 : ℕ) : ℝ)) = (m : ℝ) + 2 by push_cast; ring,
    show ((m : ℝ) + 2) - 1 = (m : ℝ) + 1 by ring]
  field_simp
  ring

/-- **The general lower bound `dₙ ≥ n^{1/(n-1)}`** for the closed unit disc, realised
by the `n = m+2` roots of unity.  Generalises `d₂ = 2`, `d₃ ≥ √3`, `d₄ ≥ 4^{1/3}`. -/
theorem transfiniteDiameterN_rootsOfUnity_ge (m : ℕ) :
    ((m : ℝ) + 2) ^ ((1 : ℝ) / ((m : ℝ) + 1)) ≤ transfiniteDiameterN (m + 2) := by
  have hζ : IsPrimitiveRoot (Complex.exp (2 * ↑Real.pi * Complex.I / ↑(m + 2))) (m + 2) :=
    Complex.isPrimitiveRoot_exp (m + 2) (by omega)
  set ζ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑(m + 2)) with hζdef
  have hmem : ∀ i, ‖rootConfig ζ (m + 2) i‖ ≤ 1 := fun i => by
    simp only [rootConfig]; exact le_of_eq (rou_norm hζ (i : ℕ))
  have hin : ((m : ℝ) + 2) ^ ((1 : ℝ) / ((m : ℝ) + 1)) ∈ unitDiscDiameters (m + 2) :=
    ⟨rootConfig ζ (m + 2), hmem, discreteDiameter_rootConfig hζ⟩
  exact le_csSup (unitDiscDiameters_bddAbove (by omega)) hin

/-- **The transfinite diameter of the closed unit disc is `≥ 1`.**  Each term of the
monotone sequence satisfies `d_{n+2} ≥ (n+2)^{1/(n+1)} ≥ 1`, so its infimum — the
transfinite diameter — is at least `1`.  Combined with `transfiniteDiameter_mem_Icc`
(`d ≤ 2`), this pins `d ∈ [1, 2]`; the sharp value `d = 1` (logarithmic capacity) is
the Fekete–Szegő content and is not established here. -/
theorem one_le_transfiniteDiameter : (1 : ℝ) ≤ transfiniteDiameter := by
  rw [transfiniteDiameter]
  refine le_ciInf (fun n => ?_)
  have hcast : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : (1 : ℝ) ≤ ((n : ℝ) + 2) ^ ((1 : ℝ) / ((n : ℝ) + 1)) := by
    calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / ((n : ℝ) + 1)) := (Real.one_rpow _).symm
      _ ≤ ((n : ℝ) + 2) ^ ((1 : ℝ) / ((n : ℝ) + 1)) :=
        Real.rpow_le_rpow (by norm_num) (by linarith) (by positivity)
  exact le_trans h1 (transfiniteDiameterN_rootsOfUnity_ge n)

/-- **The transfinite diameter of the closed unit disc lies in `[1, 2]`.**  Lower bound
from `one_le_transfiniteDiameter` (roots of unity); upper bound from
`transfiniteDiameter_mem_Icc`.  The exact value `d = 1` needs the Fekete–Szegő theorem. -/
theorem transfiniteDiameter_mem_Icc_one_two : transfiniteDiameter ∈ Set.Icc (1 : ℝ) 2 :=
  ⟨one_le_transfiniteDiameter, transfiniteDiameter_mem_Icc.2⟩

/-- **The root-of-unity lower bound is asymptotically sharp.**  The elementary
lower bounds `d_{n} ≥ n^{1/(n-1)}` realised by the `n`-th roots of unity
(`transfiniteDiameterN_rootsOfUnity_ge`) satisfy `n^{1/(n-1)} → 1` as `n → ∞`
(here `(m+2)^{1/(m+1)} → 1`).  Thus this elementary method certifies exactly the
lower bound `d ≥ 1` — the logarithmic capacity of the closed unit disc — and its
per-term bounds cannot be pushed above `1` in the limit; it recovers the
Fekete–Szegő value `d = 1` sharply from below (the matching upper bound `d ≤ 1`
still requires Fekete–Szegő and is not established here). -/
theorem tendsto_rootsOfUnity_lowerBound_one :
    Filter.Tendsto (fun m : ℕ => ((m : ℝ) + 2) ^ ((1 : ℝ) / ((m : ℝ) + 1)))
      Filter.atTop (nhds 1) := by
  -- `m ↦ (m : ℝ) + 2` tends to `+∞`
  have hbase : Filter.Tendsto (fun m : ℕ => (m : ℝ) + 2) Filter.atTop Filter.atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  -- `x ↦ x ^ (1 / (x - 1)) → 1` at `+∞` (Mathlib: `a / (b·x + c)` with `a=1, b=1, c=-1`)
  have hfun : Filter.Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / (1 * x + (-1))))
      Filter.atTop (nhds 1) := tendsto_rpow_div_mul_add 1 1 (-1) (by norm_num)
  refine (hfun.comp hbase).congr (fun m => ?_)
  simp only [Function.comp_apply]
  congr 1
  ring

end RootsOfUnity

/-!
## Hadamard's determinant inequality and the sharp value `d = 1`

Hadamard's inequality — `‖det M‖ ≤ ∏ᵢ ‖rowᵢ M‖₂` — is elementary linear algebra,
absent from Mathlib as such, but derivable from `gramSchmidtOrthonormalBasis_det`:
in the orthonormal basis `e` produced by Gram–Schmidt from the row family `f`,
the coefficient matrix is upper triangular, so `det f = ∏ᵢ ⟪eᵢ, fᵢ⟫`, and
Cauchy–Schwarz bounds every factor by `‖fᵢ‖`.

Applied to the Vandermonde matrix of `n` unit-disc points, every row has
`ℓ²`-norm at most `√n`, so `spreadProduct ≤ (√n)ⁿ` and `dₙ ≤ n^{1/(n-1)}` —
matching the roots-of-unity lower bound `transfiniteDiameterN_rootsOfUnity_ge`
exactly.  Hence `dₙ = n^{1/(n-1)}` for every `n ≥ 2` and, letting `n → ∞`, the
transfinite diameter of the closed unit disc is **exactly `1`** — the
logarithmic-capacity value, obtained here *without* Fekete–Szegő or any
potential theory.
-/

section Hadamard

open InnerProductSpace Module

/-- The rows of a square complex matrix as vectors of `EuclideanSpace ℂ (Fin n)`
(so that `‖matrixRow M i‖` is the `ℓ²`-norm of row `i`). -/
def matrixRow (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (M i)

/-- **Hadamard's determinant inequality** (complex, row form): the determinant of a
square matrix is bounded in norm by the product of the Euclidean norms of its rows.
Proof: Gram–Schmidt the rows into an orthonormal basis `e`; the coefficient matrix
of the rows in `e` is upper triangular (`gramSchmidtOrthonormalBasis_det`), so the
determinant is `∏ᵢ ⟪eᵢ, rowᵢ⟫` up to a unimodular basis-change factor, and
Cauchy–Schwarz bounds each factor by `‖rowᵢ‖`. -/
theorem norm_det_le_prod_norm_row (M : Matrix (Fin n) (Fin n) ℂ) :
    ‖M.det‖ ≤ ∏ i, ‖matrixRow M i‖ := by
  classical
  have hrank : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n) :=
    finrank_euclideanSpace
  -- the standard-basis coordinate matrix of the row family is `Mᵀ`
  have hmat : (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.toMatrix (matrixRow M)
      = M.transpose := by
    ext i j
    rw [Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr]
    rfl
  -- the Gram–Schmidt-basis determinant of the rows has the same norm as `det M`
  have hdet_eq :
      ‖(gramSchmidtOrthonormalBasis hrank (matrixRow M)).toBasis.det (matrixRow M)‖
        = ‖M.det‖ := by
    rw [Basis.det_apply,
      ← Basis.toMatrix_mul_toMatrix
        (gramSchmidtOrthonormalBasis hrank (matrixRow M)).toBasis
        (EuclideanSpace.basisFun (Fin n) ℂ).toBasis (matrixRow M),
      Matrix.det_mul, norm_mul, hmat, Matrix.det_transpose, ← Basis.det_apply,
      OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.det_to_matrix_orthonormalBasis, one_mul]
  calc ‖M.det‖
      = ‖(gramSchmidtOrthonormalBasis hrank (matrixRow M)).toBasis.det (matrixRow M)‖ :=
        hdet_eq.symm
    _ = ‖∏ i, inner ℂ (gramSchmidtOrthonormalBasis hrank (matrixRow M) i) (matrixRow M i)‖ := by
        rw [gramSchmidtOrthonormalBasis_det]
    _ = ∏ i, ‖inner ℂ (gramSchmidtOrthonormalBasis hrank (matrixRow M) i) (matrixRow M i)‖ :=
        norm_prod _ _
    _ ≤ ∏ i, ‖matrixRow M i‖ := by
        refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
        calc ‖inner ℂ (gramSchmidtOrthonormalBasis hrank (matrixRow M) i) (matrixRow M i)‖
            ≤ ‖gramSchmidtOrthonormalBasis hrank (matrixRow M) i‖ * ‖matrixRow M i‖ :=
              norm_inner_le_norm _ _
          _ = ‖matrixRow M i‖ := by
              rw [(gramSchmidtOrthonormalBasis hrank (matrixRow M)).orthonormal.1 i, one_mul]

/-- Each row of the Vandermonde matrix of unit-disc points has `ℓ²`-norm at most `√n`:
the row entries are the powers `zᵢᵏ`, `k < n`, each of norm at most `1`. -/
theorem norm_matrixRow_vandermonde_le {z : Fin n → ℂ} (hz : ∀ i, ‖z i‖ ≤ 1) (i : Fin n) :
    ‖matrixRow (Matrix.vandermonde z) i‖ ≤ Real.sqrt n := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ j, ‖matrixRow (Matrix.vandermonde z) i j‖ ^ 2
      ≤ ∑ _j : Fin n, (1 : ℝ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hentry : ‖matrixRow (Matrix.vandermonde z) i j‖ = ‖z i‖ ^ (j : ℕ) := by
          show ‖Matrix.vandermonde z i j‖ = ‖z i‖ ^ (j : ℕ)
          rw [Matrix.vandermonde_apply, norm_pow]
        rw [hentry]
        have h1 : ‖z i‖ ^ (j : ℕ) ≤ 1 := pow_le_one₀ (norm_nonneg _) (hz i)
        have h0 : (0 : ℝ) ≤ ‖z i‖ ^ (j : ℕ) := pow_nonneg (norm_nonneg _) _
        exact pow_le_one₀ h0 h1
    _ = n := by simp

/-- **Hadamard bound for the spread product**: `n` points of the closed unit disc have
spread product at most `(√n)ⁿ = n^{n/2}`. -/
theorem spreadProduct_le_sqrt_pow {z : Fin n → ℂ} (hz : ∀ i, ‖z i‖ ≤ 1) :
    spreadProduct z ≤ Real.sqrt n ^ n := by
  rw [spreadProduct_eq_norm_det_vandermonde]
  calc ‖(Matrix.vandermonde z).det‖
      ≤ ∏ i, ‖matrixRow (Matrix.vandermonde z) i‖ := norm_det_le_prod_norm_row _
    _ ≤ ∏ _i : Fin n, Real.sqrt n :=
        Finset.prod_le_prod (fun i _ => norm_nonneg _)
          (fun i _ => norm_matrixRow_vandermonde_le hz i)
    _ = Real.sqrt n ^ n := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Sharp discrete-diameter upper bound** (matches the roots-of-unity lower bound):
`n ≥ 2` points of the closed unit disc have `dₙ(Z) ≤ n^{1/(n-1)}`. -/
theorem discreteDiameter_le_rpow {z : Fin n → ℂ} (hn : 2 ≤ n) (hz : ∀ i, ‖z i‖ ≤ 1) :
    discreteDiameter z ≤ (n : ℝ) ^ ((1 : ℝ) / ((n : ℝ) - 1)) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hne1 : (n : ℝ) - 1 ≠ 0 := by intro h; nlinarith
  have hexp : (0 : ℝ) ≤ 2 / ((n : ℝ) * ((n : ℝ) - 1)) :=
    div_nonneg (by norm_num) (by nlinarith)
  unfold discreteDiameter
  calc spreadProduct z ^ (2 / ((n : ℝ) * ((n : ℝ) - 1)))
      ≤ (Real.sqrt n ^ n) ^ (2 / ((n : ℝ) * ((n : ℝ) - 1))) :=
        Real.rpow_le_rpow (spreadProduct_nonneg z) (spreadProduct_le_sqrt_pow hz) hexp
    _ = (n : ℝ) ^ ((1 / (2 : ℝ) * (n : ℝ)) * (2 / ((n : ℝ) * ((n : ℝ) - 1)))) := by
        rw [← Real.rpow_natCast (Real.sqrt n) n, Real.sqrt_eq_rpow,
          ← Real.rpow_mul (le_of_lt hnpos), ← Real.rpow_mul (le_of_lt hnpos)]
    _ = (n : ℝ) ^ ((1 : ℝ) / ((n : ℝ) - 1)) := by
        congr 1
        field_simp

/-- **Sharp `n`-point transfinite diameter (upper half)**: `dₙ ≤ n^{1/(n-1)}` for the
closed unit disc. -/
theorem transfiniteDiameterN_le_rpow (hn : 2 ≤ n) :
    transfiniteDiameterN n ≤ (n : ℝ) ^ ((1 : ℝ) / ((n : ℝ) - 1)) := by
  refine csSup_le (unitDiscDiameters_nonempty hn) ?_
  rintro d ⟨z, hz, rfl⟩
  exact discreteDiameter_le_rpow hn hz

/-- **The `n`-point transfinite diameter of the closed unit disc is exactly
`n^{1/(n-1)}`.**  Upper bound: Hadamard's inequality applied to the Vandermonde
matrix.  Lower bound: the `n`-th roots of unity
(`transfiniteDiameterN_rootsOfUnity_ge`).  The root-of-unity configurations are
thus extremal at every finite level. -/
theorem transfiniteDiameterN_eq_rpow (m : ℕ) :
    transfiniteDiameterN (m + 2) = ((m : ℝ) + 2) ^ ((1 : ℝ) / ((m : ℝ) + 1)) := by
  refine le_antisymm ?_ (transfiniteDiameterN_rootsOfUnity_ge m)
  have h := transfiniteDiameterN_le_rpow (n := m + 2) (by omega)
  have hcast : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
  rw [hcast, show (m : ℝ) + 2 - 1 = (m : ℝ) + 1 by ring] at h
  exact h

/-- **The transfinite diameter of the closed unit disc is at most `1`.**  The exact
`n`-point values `n^{1/(n-1)}` decrease to `1`
(`tendsto_rootsOfUnity_lowerBound_one`), and `d` is below every one of them. -/
theorem transfiniteDiameter_le_one : transfiniteDiameter ≤ 1 := by
  refine ge_of_tendsto' tendsto_rootsOfUnity_lowerBound_one fun m => ?_
  rw [← transfiniteDiameterN_eq_rpow m]
  exact transfiniteDiameter_le m

/-- **The transfinite diameter of the closed unit disc is exactly `1`** — the
logarithmic capacity of the disc, obtained by entirely elementary means: roots of
unity from below (`one_le_transfiniteDiameter`) and Hadamard's determinant
inequality from above (`transfiniteDiameter_le_one`), with no Fekete–Szegő
theorem and no potential theory. -/
theorem transfiniteDiameter_eq_one : transfiniteDiameter = 1 :=
  le_antisymm transfiniteDiameter_le_one one_le_transfiniteDiameter

end Hadamard

end Erdos1039TransfiniteDiameter
