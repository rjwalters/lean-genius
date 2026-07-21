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

end Erdos1039TransfiniteDiameter
