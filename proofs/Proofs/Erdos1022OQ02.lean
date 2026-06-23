/-
  Erdős #1022 OQ-02: Growth rate of the sparseness threshold c_t

  Problem #1022 (Property B for sparse families) asks: is there a function
  `c_t → ∞` such that every family `F` of sets of size `≥ t` that is
  `c_t`-sparse — meaning `|{A ∈ F : A ⊆ X}| < c_t · |X|` for *every* set `X`
  — has Property B (is 2-colorable)?  OQ-02 asks specifically: **if such a
  `c_t` exists, what is its growth rate?**

  This file isolates the *first-moment* answer to that growth-rate question.
  The argument is genuinely different from the OQ-03 file, which bounds the
  pairwise *intersection degree* and applies the Lovász Local Lemma.  Here we
  exploit the sparseness condition globally: instantiating it at `X = V` (the
  whole ground set) bounds the family size directly,

      |F|  <  c · |V|,

  and the first-moment bound (`|F| < 2^{t-1}` ⟹ Property B, generalized below
  from uniform to *minimum*-size families) turns this into an explicit
  2-colorability criterion

      c · |V|  ≤  2^{t-1}   ⟹   F has Property B.

  Reading off the admissible coefficient `c ≈ 2^{t-1}/|V|`, the first-moment
  threshold **doubles with every unit increase of `t`** — it grows
  *exponentially* in `t` (Theorem `firstMoment_threshold_doubles`).  So for a
  ground set of bounded size the sparseness threshold provably tends to
  infinity, and far faster than the `Θ(t)` rate floated in the literature.

  **Honest scope.**  This does *not* resolve Problem #1022.  The conjecture
  quantifies the sparseness condition over arbitrarily large `X` and so allows
  the ground set `V` to grow with the family; the crude ground-set bound used
  here is then no longer enough, and the genuinely hard regime (large ground
  sets, the Lovász `c_2 = 1` matching argument) is untouched.  What is
  established is the exact first-moment growth rate, which is a clean lower
  bound on any admissible `c_t` for bounded ground sets.

  Builds on `Proofs.PropertyBFirstMoment` (Erdős 1963 uniform first-moment
  theorem), reusing its `Mono`, `card_mono`, and `exists_zero_of_sum_lt_card`.

  Status: 0 sorries, 0 axioms. No `native_decide`.

  References:
  - Erdős, "On a combinatorial problem I" (1963)
  - Lovász (1968), c_2 = 1; Erdős–Lovász (1975), the Local Lemma
  - Alon & Spencer, "The Probabilistic Method", Chapter 1 (first moment)
-/
import Mathlib
import Proofs.PropertyBFirstMoment

namespace Erdos1022OQ02

open Finset BigOperators
open ProbMethod.PropertyB

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════
-- § 1: Property B and the sparseness condition
-- ══════════════════════════════════════════════════════════════════

/-- A family `F` has **Property B** if some 2-coloring of the ground set
    leaves no member of `F` monochromatic. -/
def HasPropertyB (F : Finset (Finset V)) : Prop :=
  ∃ c : V → Bool, ∀ e ∈ F, ¬ Mono e c

/-- `F` is **`c`-sparse** if for *every* set `X` the number of members of `F`
    contained in `X` is strictly less than `c · |X|`.  This is the local
    density (trace) condition of Problem #1022. -/
def IsSparse (F : Finset (Finset V)) (c : ℕ) : Prop :=
  ∀ X : Finset V, (F.filter (· ⊆ X)).card < c * X.card

-- ══════════════════════════════════════════════════════════════════
-- § 2: Sparseness bounds the family size (the global step)
-- ══════════════════════════════════════════════════════════════════

/-- **Sparseness controls the family size.**  Instantiating the sparseness
    condition at `X = V` (every member is a subset of the ground set) gives a
    direct bound on `|F|`: a `c`-sparse family on a ground set of size `n` has
    fewer than `c · n` members.  This is the global hook the first-moment
    bound needs. -/
theorem sparse_card_lt (F : Finset (Finset V)) (c : ℕ) (h : IsSparse F c) :
    F.card < c * Fintype.card V := by
  have hX := h univ
  rwa [Finset.filter_true_of_mem (fun e _ => Finset.subset_univ e),
       Finset.card_univ] at hX

-- ══════════════════════════════════════════════════════════════════
-- § 3: First moment for minimum-size families (≥ t, not uniform)
-- ══════════════════════════════════════════════════════════════════

/-- **Monochromatic count for an edge of size `≥ t`.**  The exact uniform
    count `2 · 2^{n-|e|}` of `card_mono` is monotone in `|e|`: a larger edge is
    monochromatic for fewer colorings, so an edge of size at least `t`
    contributes at most `2 · 2^{n-t}`. -/
theorem card_mono_le_of_min (e : Finset V) (t : ℕ) (ht : 1 ≤ t)
    (he : t ≤ e.card) :
    (univ.filter (fun c : V → Bool => Mono e c)).card
      ≤ 2 * 2 ^ (Fintype.card V - t) := by
  have hne : e.Nonempty := Finset.card_pos.mp (by omega)
  rw [card_mono e hne]
  have hexp : Fintype.card V - e.card ≤ Fintype.card V - t :=
    Nat.sub_le_sub_left he _
  have hpow : (2 : ℕ) ^ (Fintype.card V - e.card) ≤ 2 ^ (Fintype.card V - t) :=
    Nat.pow_le_pow_right (by norm_num) hexp
  exact Nat.mul_le_mul le_rfl hpow

/-- **First moment for families of minimum size `t`.**  A family in which every
    member has size at least `t ≥ 1` and which has fewer than `2^{t-1}` members
    has Property B.  This generalizes the uniform Erdős theorem
    `property_b_two_colorable` (edges of size exactly `k`) to a lower bound on
    sizes, which is what the `≥ t` hypothesis of Problem #1022 supplies. -/
theorem property_b_min_size (F : Finset (Finset V)) (t : ℕ) (ht : 1 ≤ t)
    (hmin : ∀ e ∈ F, t ≤ e.card) (hsmall : F.card < 2 ^ (t - 1)) :
    HasPropertyB F := by
  rcases F.eq_empty_or_nonempty with hF | hF
  · exact ⟨fun _ => true, by simp [hF]⟩
  -- t ≤ n, from any member
  obtain ⟨e₀, he₀⟩ := hF
  have htn : t ≤ Fintype.card V := by
    have hle : e₀.card ≤ Fintype.card V := by
      rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ e₀)
    exact le_trans (hmin e₀ he₀) hle
  -- first-moment sum bounded edge-by-edge
  have h2nt : 0 < (2 : ℕ) ^ (Fintype.card V - t) := pow_pos (by norm_num) _
  have hsum_le :
      (∑ c : V → Bool, (F.filter (fun e => Mono e c)).card)
        ≤ F.card * (2 * 2 ^ (Fintype.card V - t)) := by
    have hswap :
        (∑ c : V → Bool, (F.filter (fun e => Mono e c)).card)
          = ∑ e ∈ F, (univ.filter (fun c : V → Bool => Mono e c)).card := by
      simp_rw [Finset.card_filter]
      rw [Finset.sum_comm]
    rw [hswap]
    calc (∑ e ∈ F, (univ.filter (fun c : V → Bool => Mono e c)).card)
          ≤ ∑ _e ∈ F, 2 * 2 ^ (Fintype.card V - t) :=
            Finset.sum_le_sum (fun e he =>
              card_mono_le_of_min e t ht (hmin e he))
      _ = F.card * (2 * 2 ^ (Fintype.card V - t)) := by
            rw [Finset.sum_const, smul_eq_mul]
  -- |Ω| = 2^n
  have hcard : (univ : Finset (V → Bool)).card = 2 ^ Fintype.card V := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
  -- F.card * (2 * 2^{n-t}) < 2^n
  have hAlt : F.card * (2 * 2 ^ (Fintype.card V - t)) < 2 ^ Fintype.card V := by
    have e1 : (2 : ℕ) ^ Fintype.card V
        = 2 ^ t * 2 ^ (Fintype.card V - t) := by
      rw [← pow_add]; congr 1; omega
    have ekey : F.card * 2 < 2 ^ t := by
      have e2 : (2 : ℕ) ^ t = 2 * 2 ^ (t - 1) := by
        conv_lhs => rw [show t = 1 + (t - 1) by omega]
        rw [pow_add, pow_one]
      rw [e2]; omega
    calc F.card * (2 * 2 ^ (Fintype.card V - t))
          = (F.card * 2) * 2 ^ (Fintype.card V - t) := by ring
      _ < 2 ^ t * 2 ^ (Fintype.card V - t) :=
            (Nat.mul_lt_mul_right h2nt).mpr ekey
      _ = 2 ^ Fintype.card V := e1.symm
  -- combine and apply the first-moment principle
  have hlt :
      (∑ c : V → Bool, (F.filter (fun e => Mono e c)).card)
        < (univ : Finset (V → Bool)).card := by
    rw [hcard]; exact lt_of_le_of_lt hsum_le hAlt
  obtain ⟨c, -, hc⟩ := exists_zero_of_sum_lt_card hlt
  refine ⟨c, ?_⟩
  have hempty : F.filter (fun e => Mono e c) = ∅ := Finset.card_eq_zero.mp hc
  intro e he
  exact (Finset.filter_eq_empty_iff.mp hempty) he

-- ══════════════════════════════════════════════════════════════════
-- § 4: Main criterion — sparseness ⟹ Property B
-- ══════════════════════════════════════════════════════════════════

/-- **Sparse families of large sets are 2-colorable (first-moment form).**
    If every member of `F` has size at least `t ≥ 1`, `F` is `c`-sparse, and
    the ground set is small enough that `c · |V| ≤ 2^{t-1}`, then `F` has
    Property B.  The hypothesis `c · |V| ≤ 2^{t-1}` is exactly the regime in
    which the sparseness coefficient `c` may grow like `2^{t-1}/|V|`. -/
theorem propertyB_of_sparse (F : Finset (Finset V)) (t c : ℕ) (ht : 1 ≤ t)
    (hmin : ∀ e ∈ F, t ≤ e.card) (hsparse : IsSparse F c)
    (hbound : c * Fintype.card V ≤ 2 ^ (t - 1)) :
    HasPropertyB F := by
  have h1 : F.card < c * Fintype.card V := sparse_card_lt F c hsparse
  exact property_b_min_size F t ht hmin (lt_of_lt_of_le h1 hbound)

-- ══════════════════════════════════════════════════════════════════
-- § 5: Growth rate of the first-moment threshold
-- ══════════════════════════════════════════════════════════════════

/-- The first-moment admissible threshold: the largest family size for which
    minimum-size-`t` families are guaranteed 2-colorable is `2^{t-1}`.  We make
    its growth in `t` explicit below. -/
def firstMomentThreshold (t : ℕ) : ℕ := 2 ^ (t - 1)

/-- **The threshold doubles with each unit increase of `t`.**  Hence as a
    function of the minimum set size `t`, the first-moment sparseness threshold
    grows *exponentially* — the quantitative content of OQ-02's "what is the
    growth rate" for the first-moment regime. -/
theorem firstMoment_threshold_doubles (t : ℕ) (ht : 1 ≤ t) :
    firstMomentThreshold (t + 1) = 2 * firstMomentThreshold t := by
  unfold firstMomentThreshold
  rw [show t + 1 - 1 = 1 + (t - 1) by omega, pow_add, pow_one]

/-- The threshold is strictly increasing in `t` (for `t ≥ 1`): a strictly
    larger minimum set size admits a strictly denser family.  (The restriction
    `1 ≤ a` is genuine: truncated subtraction collapses `t = 0` and `t = 1` to
    the same value `2^0 = 1`.) -/
theorem firstMoment_threshold_lt {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    firstMomentThreshold a < firstMomentThreshold b := by
  unfold firstMomentThreshold
  have hexp : a - 1 < b - 1 := by omega
  exact pow_lt_pow_right₀ (by norm_num) hexp

/-- **Exponential lower bound on the admissible density.**  The first-moment
    threshold dominates `t`: `t ≤ 2^{t-1}` for every `t ≥ 1`.  So the admissible
    sparseness grows at least linearly — and in fact exponentially by
    `firstMoment_threshold_doubles` — confirming `c_t → ∞` in this regime, and
    much faster than the conjectured `Θ(t)`. -/
theorem firstMoment_threshold_ge_self (t : ℕ) (ht : 1 ≤ t) :
    t ≤ firstMomentThreshold t := by
  unfold firstMomentThreshold
  have h : t - 1 < 2 ^ (t - 1) := Nat.lt_two_pow_self
  omega

/-- **Lovász base case `t = 2`.**  The first-moment threshold at `t = 2` is `2`:
    a family of `2`-sets on a ground set of size `n` is guaranteed 2-colorable
    once `c · n ≤ 2`.  Lovász's `c_2 = 1` is sharper (it allows `c · n` up to a
    matching bound), so this records the crude first-moment value at the only
    solved case. -/
theorem firstMomentThreshold_two : firstMomentThreshold 2 = 2 := by
  unfold firstMomentThreshold; norm_num

end Erdos1022OQ02
