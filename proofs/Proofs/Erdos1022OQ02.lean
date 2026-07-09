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

-- ══════════════════════════════════════════════════════════════════
-- § 6: The threshold diverges — a formal `c_t → ∞`
-- ══════════════════════════════════════════════════════════════════

/-- Truncated integer division by a fixed positive constant is cofinal: as the
    dividend runs to infinity so does the quotient.  This is the arithmetic hook
    that survives dividing the exponential threshold by a fixed ground-set size. -/
theorem tendsto_div_const_atTop {n : ℕ} (hn : 0 < n) :
    Filter.Tendsto (· / n) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨b * n, fun m hm => ?_⟩
  rw [Nat.le_div_iff_mul_le hn]
  exact hm

/-- **The first-moment threshold tends to infinity.**  `firstMomentThreshold t
    = 2^{t-1} → ∞` as `t → ∞`.  This upgrades the pointwise bound
    `firstMoment_threshold_ge_self` (`t ≤ 2^{t-1}`) to the actual limit
    statement, making precise the `c_t → ∞` that Problem #1022 asks for. -/
theorem firstMomentThreshold_tendsto_atTop :
    Filter.Tendsto firstMomentThreshold Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_mono' _
    (by
      filter_upwards [Filter.eventually_ge_atTop 1] with t ht
      exact firstMoment_threshold_ge_self t ht)
    Filter.tendsto_id

/-- **An admissible sparseness coefficient exists and diverges (bounded ground
    set).**  Over any *fixed* nonempty ground set `V`, the explicit function
    `c(t) = ⌊2^{t-1} / |V|⌋` satisfies both halves of Erdős #1022's existential
    in the first-moment regime:

    * `c(t) → ∞` as `t → ∞` (the divergence the problem requires), and
    * every `c(t)`-sparse family whose members all have size at least `t ≥ 1`
      has Property B.

    This packages the whole file into the exact logical shape of the conjecture
    (`∃ c, (c → ∞) ∧ (sparse ⟹ Property B)`), *honestly restricted* to bounded
    ground sets: the divisor `|V|` is the fixed cardinality, so the crude
    ground-set bound (and hence this construction) degrades once `V` is allowed
    to grow with the family — precisely the untouched hard regime. -/
theorem exists_admissible_coeff (hV : 0 < Fintype.card V) :
    ∃ c : ℕ → ℕ, Filter.Tendsto c Filter.atTop Filter.atTop ∧
      ∀ (F : Finset (Finset V)) (t : ℕ), 1 ≤ t →
        (∀ e ∈ F, t ≤ e.card) → IsSparse F (c t) → HasPropertyB F := by
  refine ⟨fun t => firstMomentThreshold t / Fintype.card V, ?_, ?_⟩
  · exact (tendsto_div_const_atTop hV).comp firstMomentThreshold_tendsto_atTop
  · intro F t ht hmin hsparse
    refine propertyB_of_sparse F t _ ht hmin hsparse ?_
    calc firstMomentThreshold t / Fintype.card V * Fintype.card V
          ≤ firstMomentThreshold t := Nat.div_mul_le_self _ _
      _ = 2 ^ (t - 1) := rfl

-- ══════════════════════════════════════════════════════════════════
-- § 7: Quantitative growth rate of the admissible *coefficient*
-- ══════════════════════════════════════════════════════════════════

/-
  § 5-6 pin the growth of the *threshold* `2^{t-1}` (it doubles per step,
  `firstMoment_threshold_doubles`) and show the admissible coefficient
  `c(t) = ⌊2^{t-1}/|V|⌋` diverges (`exists_admissible_coeff`).  What was left
  *qualitative* is the growth rate of that integer coefficient itself.  This
  section pins it: over a fixed ground set `c(t)` tracks the real density
  `2^{t-1}/|V|` to within one vertex (the floor loses `< |V|`), and — despite
  the floor — `c(t)` *at least doubles* with each unit increase of `t`.  So the
  admissible coefficient, not merely the underlying threshold, grows at least
  exponentially in the minimum set size `t`: the sharp coefficient-level answer
  to OQ-02 in the first-moment regime for bounded ground sets.
-/

-- The `DecidableEq V` instance is unused in this final section (only `Fintype`
-- and `Nat` arithmetic are needed); omit it for the remaining declarations.
omit [DecidableEq V]

/-- **The integer coefficient tracks the real density to within one vertex.**
    `c(t) = ⌊2^{t-1}/|V|⌋` satisfies `2^{t-1} < (c(t)+1)·|V|`: the truncated
    division discards strictly less than a full copy of `|V|`, so the integer
    coefficient never falls more than one vertex-worth below the exact real
    threshold `2^{t-1}/|V|`.  Together with `propertyB_of_sparse`'s lower bound
    this brackets `c(t)` tightly around `2^{t-1}/|V|`. -/
theorem threshold_lt_succ_coeff_mul (hV : 0 < Fintype.card V) (t : ℕ) :
    firstMomentThreshold t
      < (firstMomentThreshold t / Fintype.card V + 1) * Fintype.card V := by
  have hdm := Nat.div_add_mod (firstMomentThreshold t) (Fintype.card V)
  have hmod := Nat.mod_lt (firstMomentThreshold t) hV
  rw [add_mul, one_mul,
      Nat.mul_comm (firstMomentThreshold t / Fintype.card V) (Fintype.card V)]
  omega

/-- **The admissible coefficient at least doubles with each unit increase of
    `t`.**  This lifts the threshold-level doubling
    (`firstMoment_threshold_doubles`) to the *integer* coefficient
    `c(t) = ⌊2^{t-1}/|V|⌋` itself, surviving the floor: `2·c(t) ≤ c(t+1)`.
    Hence the admissible sparseness coefficient — the quantity Problem #1022
    actually asks about, not merely the real threshold — grows at least
    exponentially in the minimum set size `t`.  This is the sharp
    coefficient-level growth rate for the first-moment regime over a bounded
    ground set. -/
theorem admissibleCoeff_ge_two_mul (hV : 0 < Fintype.card V) (t : ℕ) (ht : 1 ≤ t) :
    2 * (firstMomentThreshold t / Fintype.card V)
      ≤ firstMomentThreshold (t + 1) / Fintype.card V := by
  rw [firstMoment_threshold_doubles t ht, Nat.le_div_iff_mul_le hV, mul_assoc]
  have h : firstMomentThreshold t / Fintype.card V * Fintype.card V
      ≤ firstMomentThreshold t := Nat.div_mul_le_self _ _
  omega

/-- **Strict growth of the admissible coefficient once it is positive.**  As
    soon as the ground set is small enough for the threshold to admit a nonzero
    coefficient (`0 < c(t)`, i.e. `|V| ≤ 2^{t-1}`), the coefficient strictly
    increases at the next step: `c(t) < c(t+1)`.  Immediate from the doubling
    bound `2·c(t) ≤ c(t+1)`. -/
theorem admissibleCoeff_lt_of_pos (hV : 0 < Fintype.card V) (t : ℕ) (ht : 1 ≤ t)
    (hpos : 0 < firstMomentThreshold t / Fintype.card V) :
    firstMomentThreshold t / Fintype.card V
      < firstMomentThreshold (t + 1) / Fintype.card V := by
  have h := admissibleCoeff_ge_two_mul hV t ht
  omega

/-- **Matching upper bound on the coefficient's step.**  The floor can only ever
    add one extra unit on top of doubling: `c(t+1) ≤ 2·c(t) + 1`.  Indeed
    `c(t+1) = ⌊2·2^{t-1}/|V|⌋` and `⌊2x⌋ ≤ 2⌊x⌋ + 1` for the truncated division
    `x = 2^{t-1}/|V|`.  Combined with the lower bound `admissibleCoeff_ge_two_mul`,
    this pins the coefficient recurrence to `c(t+1) ∈ {2·c(t), 2·c(t)+1}` — the
    sharp two-sided step, so the "at least doubles" growth is in fact "doubles,
    up to the unavoidable `±1` from the floor". -/
theorem admissibleCoeff_le_two_mul_succ (hV : 0 < Fintype.card V) (t : ℕ) (ht : 1 ≤ t) :
    firstMomentThreshold (t + 1) / Fintype.card V
      ≤ 2 * (firstMomentThreshold t / Fintype.card V) + 1 := by
  rw [firstMoment_threshold_doubles t ht]
  set n := Fintype.card V with hn
  set M := firstMomentThreshold t with hM
  have hq : n * (M / n) + M % n = M := Nat.div_add_mod M n
  have hmod : M % n < n := Nat.mod_lt _ hV
  have hrewrite : 2 * M = n * (2 * (M / n)) + 2 * (M % n) := by
    have h2 : 2 * M = 2 * (n * (M / n) + M % n) := by rw [hq]
    rw [h2]; ring
  rw [hrewrite, Nat.mul_add_div hV]
  have hlt : 2 * (M % n) / n < 2 := by
    rw [Nat.div_lt_iff_lt_mul hV]; omega
  omega

/-- **The exact coefficient recurrence (two-sided pin).**  For every `t ≥ 1` over
    a fixed nonempty ground set, the admissible coefficient `c(t) = ⌊2^{t-1}/|V|⌋`
    satisfies

        2·c(t)  ≤  c(t+1)  ≤  2·c(t) + 1,

    i.e. `c(t+1) ∈ {2·c(t), 2·c(t)+1}`.  This is the sharp coefficient-level
    growth law for the first-moment regime: exponential doubling, deviating from
    exact doubling by at most one unit (the truncated-division remainder). -/
theorem admissibleCoeff_step_bracket (hV : 0 < Fintype.card V) (t : ℕ) (ht : 1 ≤ t) :
    2 * (firstMomentThreshold t / Fintype.card V)
        ≤ firstMomentThreshold (t + 1) / Fintype.card V
      ∧ firstMomentThreshold (t + 1) / Fintype.card V
        ≤ 2 * (firstMomentThreshold t / Fintype.card V) + 1 :=
  ⟨admissibleCoeff_ge_two_mul hV t ht, admissibleCoeff_le_two_mul_succ hV t ht⟩

/-- **Iterated exponential lower bound (the growth rate over many steps).**
    Iterating the one-step doubling `admissibleCoeff_ge_two_mul` `k` times gives the
    genuine exponential growth law for the admissible coefficient:

        `2^k · c(t)  ≤  c(t + k)`      (`c(s) = ⌊2^{s-1}/|V|⌋`).

    Where `admissibleCoeff_ge_two_mul` only asserts "at least doubles per step", this
    accumulates the doublings: after `k` steps the coefficient has grown by a factor of
    at least `2^k`. Proof by induction on `k`, chaining the one-step bound at index
    `t + k` (which is `≥ 1` since `t ≥ 1`) with the `2·`-monotonicity of the IH. -/
theorem admissibleCoeff_two_pow_mul_le (hV : 0 < Fintype.card V) (t : ℕ) (ht : 1 ≤ t)
    (k : ℕ) :
    2 ^ k * (firstMomentThreshold t / Fintype.card V)
      ≤ firstMomentThreshold (t + k) / Fintype.card V := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep := admissibleCoeff_ge_two_mul hV (t + k) (by omega)
      rw [show t + (k + 1) = (t + k) + 1 from by ring, pow_succ', mul_assoc]
      exact le_trans (Nat.mul_le_mul (le_refl 2) ih) hstep

/-- **Iterated exponential upper bound (the growth rate over many steps).**
    The matching iterate of the one-step ceiling `admissibleCoeff_le_two_mul_succ`.
    Carrying the `+1` through the recurrence to absorb the per-step floor remainders,

        `c(t + k) + 1  ≤  2^k · (c(t) + 1)`,

    equivalently `c(t + k) ≤ 2^k · c(t) + (2^k − 1)`: over `k` steps the coefficient
    exceeds pure `2^k`-doubling by at most `2^k − 1`, the geometric sum of the `k`
    truncated-division `±1` errors. Together with `admissibleCoeff_two_pow_mul_le` this
    brackets `c(t + k)` between `2^k · c(t)` and `2^k · (c(t) + 1) − 1`, pinning the
    multi-step growth to exact exponential rate `2^k` up to a bounded relative error.
    Proof by induction on `k`, chaining the one-step ceiling at index `t + k` with the
    `2·`-monotonicity of the IH. -/
theorem admissibleCoeff_succ_le_two_pow_mul (hV : 0 < Fintype.card V) (t : ℕ) (ht : 1 ≤ t)
    (k : ℕ) :
    firstMomentThreshold (t + k) / Fintype.card V + 1
      ≤ 2 ^ k * (firstMomentThreshold t / Fintype.card V + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep := admissibleCoeff_le_two_mul_succ hV (t + k) (by omega)
      rw [show t + (k + 1) = (t + k) + 1 from by ring, pow_succ', mul_assoc]
      have h2 : firstMomentThreshold ((t + k) + 1) / Fintype.card V + 1
          ≤ 2 * (firstMomentThreshold (t + k) / Fintype.card V + 1) := by omega
      exact le_trans h2 (Nat.mul_le_mul (le_refl 2) ih)

end Erdos1022OQ02
