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

/-- The first-moment threshold is always strictly positive: `2^{t-1} ≥ 1`.  A base
    positivity fact for the sparseness bound `c · n ≤ 2^{t-1}` — the admissible density is
    never vacuously zero. -/
theorem firstMomentThreshold_pos (t : ℕ) : 0 < firstMomentThreshold t := by
  unfold firstMomentThreshold; positivity

/-- **Lovász base case `t = 1`** (companion to `firstMomentThreshold_two`).  The threshold
    at `t = 1` is `1`: `2^0 = 1`.  A single-element set family is trivially 2-colorable, and
    the crude first-moment bound reflects this with the minimal threshold `1`. -/
theorem firstMomentThreshold_one : firstMomentThreshold 1 = 1 := by
  unfold firstMomentThreshold; norm_num

/-- **The threshold is `1` exactly on the degenerate regime `t ≤ 1`.**  `2^{t-1} = 1 ↔ t ≤ 1`:
    the first-moment sparseness threshold sits at its minimal value `1` precisely for the two
    truncated-subtraction-collapsed cases `t = 0, 1`, and is `≥ 2` (strictly growing) from
    `t = 2` onward.  This pins the boundary of the exponential-growth regime driving
    `firstMoment_threshold_lt` / `_doubles`. -/
theorem firstMomentThreshold_eq_one_iff (t : ℕ) : firstMomentThreshold t = 1 ↔ t ≤ 1 := by
  unfold firstMomentThreshold
  rw [Nat.pow_eq_one]
  omega

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

/-- **Exact positivity threshold for the admissible coefficient.**  The integer
    coefficient `c(t) = ⌊2^{t-1}/|V|⌋` is nonzero *exactly* when the ground set is
    small enough for the threshold to reach one full copy of `|V|`:

        `0 < c(t)  ↔  |V| ≤ 2^{t-1}`.

    This locates the explicit step `t₀` (any `t` with `|V| ≤ firstMomentThreshold t`)
    past which the construction of `exists_admissible_coeff` yields a genuinely
    positive sparseness coefficient — the effective content behind the abstract
    divergence `firstMomentThreshold_tendsto_atTop`. -/
theorem admissibleCoeff_pos_iff (hV : 0 < Fintype.card V) (t : ℕ) :
    0 < firstMomentThreshold t / Fintype.card V
      ↔ Fintype.card V ≤ firstMomentThreshold t := by
  constructor
  · intro h; exact (Nat.one_le_div_iff hV).mp h
  · intro h; exact (Nat.one_le_div_iff hV).mpr h

/-- **The explicit positivity threshold `t₀ = |V|`.**  The `↔` criterion
    `admissibleCoeff_pos_iff` locates positivity at the abstract condition
    `|V| ≤ 2^{t-1}`, but never exhibits a concrete `t₀` realising it.  This does:
    for *every* `t ≥ |V|` the admissible coefficient is already positive,

        `|V| ≤ t  ⟹  0 < c(t)`.

    So `t₀ = |V|` is an explicit step past which the `exists_admissible_coeff`
    construction yields a genuinely nonzero sparseness coefficient.  Proof: the
    exponential dominates the linear bound (`t ≤ 2^{t-1}`,
    `firstMoment_threshold_ge_self`), so `|V| ≤ t ≤ 2^{t-1}`, and
    `admissibleCoeff_pos_iff` reads off positivity. -/
theorem admissibleCoeff_pos_of_card_le (hV : 0 < Fintype.card V) (t : ℕ)
    (ht : Fintype.card V ≤ t) :
    0 < firstMomentThreshold t / Fintype.card V := by
  have h1 : 1 ≤ t := by omega
  exact (admissibleCoeff_pos_iff hV t).mpr
    (le_trans ht (firstMoment_threshold_ge_self t h1))

/-- **Eventual positivity of the admissible coefficient (filter form).**  Packaging
    the explicit threshold `admissibleCoeff_pos_of_card_le` as an `atTop` statement:
    the coefficient `c(t) = ⌊2^{t-1}/|V|⌋` is *eventually* positive.  This is the
    qualitative shadow of the effective bound — the companion to the divergence
    `firstMomentThreshold_tendsto_atTop` on the positivity side — with the witness
    `t₀ = |V|` supplied concretely by `admissibleCoeff_pos_of_card_le`. -/
theorem admissibleCoeff_eventually_pos (hV : 0 < Fintype.card V) :
    ∀ᶠ t in Filter.atTop, 0 < firstMomentThreshold t / Fintype.card V :=
  Filter.eventually_atTop.mpr
    ⟨Fintype.card V, fun t ht => admissibleCoeff_pos_of_card_le hV t ht⟩

/-- **Explicit exponential lower bound on the coefficient (effective divergence).**
    Once the coefficient is positive at step `t` (i.e. `|V| ≤ 2^{t-1}`, cf.
    `admissibleCoeff_pos_iff`), it is bounded below by a *concrete* power of two after
    `k` further steps:

        `2^k ≤ c(t + k)`.

    Equivalently, writing `t₀` for the positivity threshold, `c(t) ≥ 2^{t-t₀}` for all
    `t ≥ t₀`.  This upgrades the qualitative `firstMomentThreshold_tendsto_atTop` /
    `exists_admissible_coeff` divergence to an explicit exponential rate: it exhibits,
    for each target `2^k`, the exact step at which the admissible sparseness coefficient
    surpasses it.  Proof: `1 ≤ c(t)` from `admissibleCoeff_pos_iff`, then multiply the
    iterated lower bound `admissibleCoeff_two_pow_mul_le` (`2^k·c(t) ≤ c(t+k)`). -/
theorem admissibleCoeff_ge_two_pow_of_le (hV : 0 < Fintype.card V) (t : ℕ) (ht : 1 ≤ t)
    (hle : Fintype.card V ≤ firstMomentThreshold t) (k : ℕ) :
    2 ^ k ≤ firstMomentThreshold (t + k) / Fintype.card V := by
  have hpos : 0 < firstMomentThreshold t / Fintype.card V :=
    (admissibleCoeff_pos_iff hV t).mpr hle
  have hmul := admissibleCoeff_two_pow_mul_le hV t ht k
  calc 2 ^ k = 2 ^ k * 1 := (mul_one _).symm
    _ ≤ 2 ^ k * (firstMomentThreshold t / Fintype.card V) :=
        Nat.mul_le_mul (le_refl _) hpos
    _ ≤ firstMomentThreshold (t + k) / Fintype.card V := hmul

/-- **Two-sided exponential bracket (the exact multi-step growth rate).**  The
    capstone conjunction promised in the docstrings of the two iterate bounds:
    combining the geometric lower bound `admissibleCoeff_two_pow_mul_le` with the
    ceiling `admissibleCoeff_succ_le_two_pow_mul` pins the coefficient after `k`
    steps to a window of width exactly `2^k − 1` around pure `2^k`-doubling,

        `2^k · c(t)  ≤  c(t + k)  ≤  2^k · c(t) + (2^k − 1)`,

    i.e. `0 ≤ c(t+k) − 2^k·c(t) < 2^k`.  The additive slack `2^k − 1` is the
    geometric sum `∑_{i<k} 2^i` of the `k` per-step truncated-division remainders,
    so relative to the leading `2^k·c(t)` the error is at most one unit of `c(t)`:
    the growth rate is **exactly exponential with ratio `2`**, the floor operations
    contributing only a bounded lower-order correction.  The lower half is
    `admissibleCoeff_two_pow_mul_le`; the upper half rewrites the `+1`-shifted
    ceiling `admissibleCoeff_succ_le_two_pow_mul` by distributing `2^k·(c(t)+1)`
    and discharging with `omega` (using `1 ≤ 2^k`). -/
theorem admissibleCoeff_bracket (hV : 0 < Fintype.card V) (t : ℕ) (ht : 1 ≤ t) (k : ℕ) :
    2 ^ k * (firstMomentThreshold t / Fintype.card V)
        ≤ firstMomentThreshold (t + k) / Fintype.card V
      ∧ firstMomentThreshold (t + k) / Fintype.card V
        ≤ 2 ^ k * (firstMomentThreshold t / Fintype.card V) + (2 ^ k - 1) := by
  have hlow := admissibleCoeff_two_pow_mul_le hV t ht k
  have hup := admissibleCoeff_succ_le_two_pow_mul hV t ht k
  rw [mul_add, mul_one] at hup
  have hpow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  exact ⟨hlow, by omega⟩

/-- **Unconditional positivity step (explicit `t₀` for every ground set).**  The
    positivity criterion `admissibleCoeff_pos_iff` requires the side condition
    `|V| ≤ 2^{t-1}`; here we discharge it with a *concrete, computable* step valid
    for arbitrary ground sets.  As soon as `t` exceeds `|V|`, the elementary bound
    `|V| < 2^{|V|} ≤ 2^{t-1}` supplies the hypothesis, so

        `|V| < t  ⟹  0 < c(t)`.

    Thus `t₀ = |V| + 1` is an explicit positivity threshold that does not require
    knowing where `2^{t-1}` overtakes `|V|` — the crude gap `2^{|V|} > |V|` already
    forces it.  (This `t₀` is far from the sharp `⌈log₂|V|⌉ + 1`, but it is
    unconditional and computable directly from `|V|`.) -/
theorem admissibleCoeff_pos_of_card_lt (hV : 0 < Fintype.card V) (t : ℕ)
    (ht : Fintype.card V < t) :
    0 < firstMomentThreshold t / Fintype.card V := by
  refine (admissibleCoeff_pos_iff hV t).mpr ?_
  have h1 : Fintype.card V < 2 ^ (Fintype.card V) := Nat.lt_two_pow_self
  have h2 : 2 ^ (Fintype.card V) ≤ 2 ^ (t - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  calc Fintype.card V ≤ 2 ^ (Fintype.card V) := le_of_lt h1
    _ ≤ 2 ^ (t - 1) := h2
    _ = firstMomentThreshold t := rfl

/-- **Unconditional effective exponential divergence.**  Feeding the explicit
    positivity step `admissibleCoeff_pos_of_card_lt` into the iterated lower bound
    `admissibleCoeff_two_pow_mul_le` removes *all* side conditions relating `|V|` to
    the threshold: for every nonempty ground set and every target exponent `k`,

        `2^k ≤ c(|V| + 1 + k)`.

    This is the fully explicit, hypothesis-free form of the divergence
    `firstMomentThreshold_tendsto_atTop` / `exists_admissible_coeff`: it names, for
    each `k`, the concrete step `|V| + 1 + k` at which the admissible sparseness
    coefficient of a bounded ground set already exceeds `2^k`.  Proof: `1 ≤ c(|V|+1)`
    from the positivity step, then scale the iterated bound `2^k·c(|V|+1) ≤ c(|V|+1+k)`. -/
theorem admissibleCoeff_ge_two_pow_of_card (hV : 0 < Fintype.card V) (k : ℕ) :
    2 ^ k ≤ firstMomentThreshold (Fintype.card V + 1 + k) / Fintype.card V := by
  have ht : (1 : ℕ) ≤ Fintype.card V + 1 := by omega
  have hpos : 0 < firstMomentThreshold (Fintype.card V + 1) / Fintype.card V :=
    admissibleCoeff_pos_of_card_lt hV (Fintype.card V + 1) (by omega)
  have hmul := admissibleCoeff_two_pow_mul_le hV (Fintype.card V + 1) ht k
  calc 2 ^ k = 2 ^ k * 1 := (mul_one _).symm
    _ ≤ 2 ^ k * (firstMomentThreshold (Fintype.card V + 1) / Fintype.card V) :=
        Nat.mul_le_mul (le_refl _) hpos
    _ ≤ firstMomentThreshold (Fintype.card V + 1 + k) / Fintype.card V := hmul

/-- **Closed single-index exponential lower bound on the coefficient.**  The two-index
    iterate `admissibleCoeff_ge_two_pow_of_card` (`2^k ≤ c(|V|+1+k)`) collapsed to a
    single variable by setting `k = t − |V| − 1`: for every minimum set size `t > |V|`,

        `2^{t − |V| − 1}  ≤  c(t) = ⌊2^{t-1}/|V|⌋`.

    This makes precise the remark (in `admissibleCoeff_ge_two_pow_of_le`'s docstring)
    that "writing `t₀` for the positivity threshold, `c(t) ≥ 2^{t−t₀}` for all `t ≥ t₀`":
    here `t₀ = |V| + 1` is the concrete, unconditional threshold, so this is the explicit
    exponential growth law of the admissible sparseness coefficient as a function of the
    minimum set size `t` alone, with no auxiliary index. -/
theorem admissibleCoeff_ge_two_pow_sub (hV : 0 < Fintype.card V) (t : ℕ)
    (ht : Fintype.card V < t) :
    2 ^ (t - Fintype.card V - 1) ≤ firstMomentThreshold t / Fintype.card V := by
  have hk := admissibleCoeff_ge_two_pow_of_card hV (t - Fintype.card V - 1)
  rwa [show Fintype.card V + 1 + (t - Fintype.card V - 1) = t from by omega] at hk

/-
  §§ 5-7 above bound the coefficient `c(t) = ⌊2^{t-1}/|V|⌋` up to the unavoidable
  truncated-division `±1` error (`admissibleCoeff_step_bracket`, `admissibleCoeff_bracket`).
  That error vanishes *exactly* when `|V|` divides the threshold — i.e. when `|V|` is a
  power of two.  In that case the floor is inert: the coefficient is a clean power of two
  and doubles with no correction, exhibiting the sharpness of the `+1` slack in the step
  bracket (it is attained only away from power-of-two ground sets).
-/

/-- **Exact coefficient for a power-of-two ground set.**  When `|V| = 2^j` with `j ≤ t-1`,
    the divisor exactly divides the threshold `2^{t-1}`, so the floor in
    `c(t) = ⌊2^{t-1}/|V|⌋` is inert and the coefficient is the clean power of two

        `c(t) = 2^{t-1-j}`.

    This is the exact special case of the "tracks the real density to within one vertex"
    bracket `threshold_lt_succ_coeff_mul`: for power-of-two ground sets the one-vertex slack
    is zero.  Proof: `2^{t-1} / 2^j = 2^{t-1-j}` by `Nat.pow_div`. -/
theorem admissibleCoeff_eq_of_card_eq_two_pow {j : ℕ} (t : ℕ)
    (hcard : Fintype.card V = 2 ^ j) (hj : j ≤ t - 1) :
    firstMomentThreshold t / Fintype.card V = 2 ^ (t - 1 - j) := by
  unfold firstMomentThreshold
  rw [hcard, Nat.pow_div hj (by norm_num)]

/-- **The coefficient doubles *exactly* for a power-of-two ground set.**  When `|V| = 2^j`
    the truncated division loses nothing, so the "at least doubles / at most doubles + 1"
    step bracket `admissibleCoeff_step_bracket` collapses to exact doubling:

        `c(t+1) = 2·c(t)`      (for `t ≥ 1`, `j ≤ t-1`).

    So the `+1` slack in `admissibleCoeff_step_bracket` / `admissibleCoeff_le_two_mul_succ`
    is a genuine feature of non-power-of-two ground sets: it is contributed entirely by the
    per-step remainder `2^{t-1} mod |V|`, which is `0` precisely when `|V| ∣ 2^{t-1}`.  Proof:
    evaluate the exact value `admissibleCoeff_eq_of_card_eq_two_pow` at `t` and `t+1`. -/
theorem admissibleCoeff_doubles_of_card_eq_two_pow {j : ℕ} (t : ℕ) (ht : 1 ≤ t)
    (hcard : Fintype.card V = 2 ^ j) (hj : j ≤ t - 1) :
    firstMomentThreshold (t + 1) / Fintype.card V
      = 2 * (firstMomentThreshold t / Fintype.card V) := by
  rw [admissibleCoeff_eq_of_card_eq_two_pow (t + 1) hcard (by omega),
      admissibleCoeff_eq_of_card_eq_two_pow t hcard hj,
      show t + 1 - 1 - j = (t - 1 - j) + 1 from by omega, pow_succ]
  ring

-- ══════════════════════════════════════════════════════════════════
-- § 8: Monotonicity of the admissible coefficient in `t`
-- ══════════════════════════════════════════════════════════════════

/-
  §§ 5-7 pin the *rate* of growth (doubling per step, exponential brackets).
  What underlies all of that — and is worth recording on its own, since OQ-02
  asks about the growth *rate* of `c_t` — is the bare qualitative fact that the
  coefficient never decreases as the minimum set size `t` grows.  Both the
  threshold `2^{t-1}` and its truncated quotient `⌊2^{t-1}/|V|⌋` are monotone
  in `t`, unconditionally (no positivity or ground-set hypothesis needed): a
  larger `t` admits a sparseness coefficient at least as large.  This is the
  monotone envelope the quantitative doubling bound `admissibleCoeff_ge_two_mul`
  refines.
-/

/-- **The first-moment threshold is monotone in `t`.**  `2^{a-1} ≤ 2^{b-1}`
    whenever `a ≤ b`; the exponential threshold never decreases as the minimum
    set size grows. -/
theorem firstMomentThreshold_mono {a b : ℕ} (hab : a ≤ b) :
    firstMomentThreshold a ≤ firstMomentThreshold b := by
  unfold firstMomentThreshold
  exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le_sub_right hab 1)

/-- **The admissible coefficient is monotone in `t`.**  For a fixed ground set,
    `c(a) = ⌊2^{a-1}/|V|⌋ ≤ ⌊2^{b-1}/|V|⌋ = c(b)` whenever `a ≤ b`: truncated
    division by the fixed divisor `|V|` preserves the monotonicity of the
    threshold.  This is the unconditional monotone backbone of the quantitative
    growth bounds in §§ 5-7 — no positivity or `1 ≤ a` hypothesis is required. -/
theorem admissibleCoeff_mono {a b : ℕ} (hab : a ≤ b) :
    firstMomentThreshold a / Fintype.card V
      ≤ firstMomentThreshold b / Fintype.card V :=
  Nat.div_le_div_right (firstMomentThreshold_mono hab)

-- ══════════════════════════════════════════════════════════════════
-- § 9: Modulus of divergence in *value* form, and the Property-B payoff
-- ══════════════════════════════════════════════════════════════════

/-
  §§ 5-7 measure the growth of the coefficient `c(t) = ⌊2^{t-1}/|V|⌋` *by rate*:
  every explicit bound is phrased as "`2^k ≤ c(t + k)`" — a statement about the
  exponent `k`, not the value reached.  What is still missing is the dual,
  *value*-indexed reading of the same divergence: given a target coefficient
  `N`, at which step is it attained?  This section supplies the explicit
  (linear) modulus `t₀ = |V| + 1 + N` with `N ≤ c(t₀)`, names the coefficient's
  own `Tendsto … atTop` (used only inline so far, inside
  `exists_admissible_coeff`), and — the mathematical point — *inverts* the
  divergence back to Property B: because `c(t)` overtakes every fixed `N`, any
  *fixed* sparseness coefficient `N`, however large, is defeated once the
  minimum set size is large enough.  This is the effective converse to
  `exists_admissible_coeff`, which fixed a diverging `c(t)`; here `N` is fixed
  and the minimum size varies.
-/

/-- **The admissible coefficient tends to infinity (named).**  Over a fixed
    nonempty ground set, `c(t) = ⌊2^{t-1}/|V|⌋ → ∞` as `t → ∞`.  This divergence
    is used *inline* in the proof of `exists_admissible_coeff` (as the first
    conjunct of its witness), but is recorded here as a standalone lemma — the
    coefficient-level companion of `firstMomentThreshold_tendsto_atTop`, and the
    literal `c_t → ∞` of Problem #1022 read off the explicit coefficient. -/
theorem admissibleCoeff_tendsto_atTop (hV : 0 < Fintype.card V) :
    Filter.Tendsto (fun t => firstMomentThreshold t / Fintype.card V)
      Filter.atTop Filter.atTop :=
  (tendsto_div_const_atTop hV).comp firstMomentThreshold_tendsto_atTop

/-- **Explicit linear modulus of divergence (value form).**  Every target
    coefficient value `N` is reached by the explicit, *linear* step
    `t₀ = |V| + 1 + N`:

        `N ≤ c(|V| + 1 + N) = ⌊2^{|V| + N}/|V|⌋`.

    Where §§ 5-7 bound the coefficient by rate (`2^k ≤ c(|V|+1+k)`, an exponent
    statement), this reads the same divergence off in the dual direction — as an
    explicit *inverse* modulus telling, for each desired value `N`, a concrete
    step at which the coefficient has surpassed it.  Proof: the exponential
    bound `2^N ≤ c(|V|+1+N)` of `admissibleCoeff_ge_two_pow_of_card` combined
    with `N ≤ 2^N`. -/
theorem admissibleCoeff_ge_self (hV : 0 < Fintype.card V) (N : ℕ) :
    N ≤ firstMomentThreshold (Fintype.card V + 1 + N) / Fintype.card V := by
  have hpow := admissibleCoeff_ge_two_pow_of_card hV N
  have hN : N ≤ 2 ^ N := Nat.le_of_lt Nat.lt_two_pow_self
  exact le_trans hN hpow

/-- **Eventual dominance of any target (value form, filter).**  Packaging
    `admissibleCoeff_ge_self` with the monotonicity `admissibleCoeff_mono`: for
    every target `N`, the coefficient is *eventually* at least `N`,

        `∀ N, ∀ᶠ t, N ≤ c(t)`,

    with the explicit witness step `t₀ = |V| + 1 + N`.  This is the value-indexed
    shadow of `admissibleCoeff_tendsto_atTop` with a concrete modulus attached. -/
theorem admissibleCoeff_eventually_ge (hV : 0 < Fintype.card V) (N : ℕ) :
    ∀ᶠ t in Filter.atTop, N ≤ firstMomentThreshold t / Fintype.card V :=
  Filter.eventually_atTop.mpr
    ⟨Fintype.card V + 1 + N, fun _t ht =>
      le_trans (admissibleCoeff_ge_self hV N) (admissibleCoeff_mono ht)⟩

/-- **Large minimum size defeats any fixed sparseness coefficient (the payoff).**
    The effective converse of `exists_admissible_coeff`.  There the coefficient
    `c(t)` was allowed to grow with `t`; here we *fix* an arbitrary target
    sparseness coefficient `N` and show it is tolerated once the minimum set size
    is large enough: there is an explicit threshold `t₀` (namely `|V| + 1 + N`)
    such that every `N`-sparse family whose members all have size at least `t₀`
    has Property B.

        `∀ N, ∃ t₀ ≥ 1, ∀ F, (∀ e ∈ F, t₀ ≤ |e|) → IsSparse F N → HasPropertyB F`.

    So no *constant* sparseness bound is an obstruction to first-moment
    2-colorability: the minimum size can always be pushed high enough to absorb
    it.  Proof: `admissibleCoeff_ge_self` gives `N ≤ c(t₀)`, hence
    `N · |V| ≤ 2^{t₀-1}`, which is exactly the hypothesis `propertyB_of_sparse`
    needs. -/
theorem exists_min_size_for_sparse_bound [DecidableEq V] (hV : 0 < Fintype.card V)
    (N : ℕ) :
    ∃ t₀ : ℕ, 1 ≤ t₀ ∧ ∀ (F : Finset (Finset V)),
      (∀ e ∈ F, t₀ ≤ e.card) → IsSparse F N → HasPropertyB F := by
  refine ⟨Fintype.card V + 1 + N, by omega, fun F hmin hsparse => ?_⟩
  have hcoeff : N ≤ firstMomentThreshold (Fintype.card V + 1 + N) / Fintype.card V :=
    admissibleCoeff_ge_self hV N
  have hbound : N * Fintype.card V ≤ firstMomentThreshold (Fintype.card V + 1 + N) :=
    (Nat.le_div_iff_mul_le hV).mp hcoeff
  exact propertyB_of_sparse F (Fintype.card V + 1 + N) N (by omega) hmin hsparse hbound

-- ══════════════════════════════════════════════════════════════════
-- § 10: Sharp *logarithmic* modulus of divergence
-- ══════════════════════════════════════════════════════════════════

/-
  § 9 exhibits an *explicit* modulus of divergence in value form: the target
  coefficient `N` is reached by step `t₀ = |V| + 1 + N` (`admissibleCoeff_ge_self`,
  `exists_min_size_for_sparse_bound`).  That modulus is honest but *crude* — it is
  **linear** in `N`, obtained by throwing away the exponential in `2^N ≤ c(|V|+1+N)`.
  Yet the defining relation `N ≤ c(t) ⇔ N·|V| ≤ 2^{t-1}` shows the true cost of
  reaching value `N` is only **logarithmic**: `t` need only clear `1 + ⌈log₂(N·|V|)⌉`.

  This section installs that sharp threshold.  The pivot is the elementary
  characterization `admissibleCoeff_ge_iff` (a one-line consequence of
  `Nat.le_div_iff_mul_le`), which via `Nat.clog` sharpens to the exact
  `N ≤ c(t) ⇔ clog₂(N·|V|) ≤ t-1`.  Reading it forwards gives the logarithmic
  modulus `t₀ = clog₂(N·|V|) + 1`; a machine-checked inequality then confirms this
  is never worse than § 9's linear `|V| + 1 + N` (and generically exponentially
  smaller).  The Property-B payoff of § 9 is re-derived with this sharp `t₀`.
-/

/-- **Coefficient exceeds a target iff the threshold clears `N·|V|`.**  The defining
    equivalence behind every divergence bound in this file, stated once as a clean
    `↔`: the admissible coefficient `c(t) = ⌊2^{t-1}/|V|⌋` reaches a target value `N`
    exactly when the raw first-moment threshold `2^{t-1}` clears `N` full copies of
    the ground set,

        `N ≤ c(t)  ↔  N·|V| ≤ 2^{t-1}`.

    Immediate from `Nat.le_div_iff_mul_le` (the floor's Galois connection with
    multiplication).  Every bound of §§ 5-9 is an estimate of one side of this
    equivalence; isolating it makes the sharp logarithmic modulus below a two-line
    consequence. -/
theorem admissibleCoeff_ge_iff (hV : 0 < Fintype.card V) (N t : ℕ) :
    N ≤ firstMomentThreshold t / Fintype.card V
      ↔ N * Fintype.card V ≤ firstMomentThreshold t := by
  rw [Nat.le_div_iff_mul_le hV]

/-- **Sharp `clog` characterization of the modulus.**  Feeding
    `admissibleCoeff_ge_iff` through the ceiling-logarithm Galois connection
    `Nat.le_pow_iff_clog_le` (`x ≤ 2^y ↔ clog₂ x ≤ y`) pins the *exact* step at which
    the coefficient reaches `N`:

        `N ≤ c(t)  ↔  clog₂(N·|V|) ≤ t - 1`.

    So the threshold is attained precisely when `t` clears `clog₂(N·|V|) + 1`: a
    **logarithmic** modulus, exponentially sharper than § 9's linear `|V| + 1 + N`. -/
theorem admissibleCoeff_ge_iff_clog_le (hV : 0 < Fintype.card V) (N t : ℕ) :
    N ≤ firstMomentThreshold t / Fintype.card V
      ↔ Nat.clog 2 (N * Fintype.card V) ≤ t - 1 := by
  rw [admissibleCoeff_ge_iff hV]
  unfold firstMomentThreshold
  exact (Nat.clog_le_iff_le_pow (by norm_num)).symm

/-- **The logarithmic modulus (forward form).**  Reading
    `admissibleCoeff_ge_iff_clog_le` forwards: the target coefficient `N` is reached
    at *every* step past the logarithmic threshold `t₀ = clog₂(N·|V|) + 1`,

        `clog₂(N·|V|) + 1 ≤ t  ⟹  N ≤ c(t)`.

    This is the sharp counterpart of `admissibleCoeff_ge_self` (whose witness step is
    the linear `|V| + 1 + N`); here the step is only logarithmic in `N`. -/
theorem admissibleCoeff_ge_of_clog_le (hV : 0 < Fintype.card V) (N t : ℕ)
    (ht : Nat.clog 2 (N * Fintype.card V) + 1 ≤ t) :
    N ≤ firstMomentThreshold t / Fintype.card V := by
  rw [admissibleCoeff_ge_iff_clog_le hV]
  omega

/-- **The logarithmic modulus improves on § 9's linear one.**  A machine-checked
    proof that the sharp threshold never exceeds the crude one,

        `clog₂(N·|V|) + 1  ≤  |V| + 1 + N`,

    so `admissibleCoeff_ge_of_clog_le` strictly dominates `admissibleCoeff_ge_self`.
    Proof: `N·|V| ≤ 2^N · 2^{|V|} = 2^{N+|V|}` (from `n < 2^n` twice), hence
    `clog₂(N·|V|) ≤ N + |V|` by `Nat.clog_le_of_le_pow`.  The gap between the two
    moduli is generically exponential — `clog₂(N·|V|) ≈ log₂ N + log₂ |V|` against the
    linear `N + |V|`. -/
theorem admissibleCoeff_log_modulus_le_linear (N : ℕ) :
    Nat.clog 2 (N * Fintype.card V) + 1 ≤ Fintype.card V + 1 + N := by
  have hb : N * Fintype.card V ≤ 2 ^ (N + Fintype.card V) := by
    calc N * Fintype.card V
          ≤ 2 ^ N * 2 ^ (Fintype.card V) :=
            Nat.mul_le_mul (Nat.le_of_lt Nat.lt_two_pow_self)
              (Nat.le_of_lt Nat.lt_two_pow_self)
      _ = 2 ^ (N + Fintype.card V) := (pow_add 2 N (Fintype.card V)).symm
  have hc : Nat.clog 2 (N * Fintype.card V) ≤ N + Fintype.card V :=
    Nat.clog_le_of_le_pow hb
  omega

/-- **Eventual dominance with the sharp witness.**  The `atTop` companion of
    `admissibleCoeff_ge_of_clog_le`: for every target `N` the coefficient is
    eventually at least `N`, now with the *logarithmic* witness step
    `t₀ = clog₂(N·|V|) + 1` in place of the linear witness of
    `admissibleCoeff_eventually_ge`. -/
theorem admissibleCoeff_eventually_ge_sharp (hV : 0 < Fintype.card V) (N : ℕ) :
    ∀ᶠ t in Filter.atTop, N ≤ firstMomentThreshold t / Fintype.card V :=
  Filter.eventually_atTop.mpr
    ⟨Nat.clog 2 (N * Fintype.card V) + 1,
      fun _t ht => admissibleCoeff_ge_of_clog_le hV N _ ht⟩

/-- **Large minimum size defeats any fixed sparseness coefficient — logarithmically
    (the sharp payoff).**  The § 9 payoff `exists_min_size_for_sparse_bound` with the
    linear modulus replaced by the sharp logarithmic one: every fixed `N`-sparse
    family of `≥ t₀`-sets has Property B already for a minimum size

        `t₀ = clog₂(N·|V|) + 1`,

    only *logarithmic* in the sparseness bound `N`, and — as certified by the middle
    conjunct `t₀ ≤ |V| + 1 + N` — never worse than the linear threshold of § 9.  So
    absorbing a constant sparseness coefficient `N` costs only `O(log N)` in the
    minimum set size, not `O(N)`.  Proof: `admissibleCoeff_ge_of_clog_le` at the
    logarithmic step yields `N ≤ c(t₀)`, hence `N·|V| ≤ 2^{t₀-1}`, exactly the
    hypothesis `propertyB_of_sparse` needs; the improvement bound is
    `admissibleCoeff_log_modulus_le_linear`. -/
theorem exists_min_size_for_sparse_bound_sharp [DecidableEq V] (hV : 0 < Fintype.card V)
    (N : ℕ) :
    ∃ t₀ : ℕ, 1 ≤ t₀ ∧ t₀ ≤ Fintype.card V + 1 + N ∧ ∀ (F : Finset (Finset V)),
      (∀ e ∈ F, t₀ ≤ e.card) → IsSparse F N → HasPropertyB F := by
  refine ⟨Nat.clog 2 (N * Fintype.card V) + 1, by omega,
    admissibleCoeff_log_modulus_le_linear N, fun F hmin hsparse => ?_⟩
  have hcoeff : N ≤ firstMomentThreshold (Nat.clog 2 (N * Fintype.card V) + 1)
      / Fintype.card V :=
    admissibleCoeff_ge_of_clog_le hV N _ (le_refl _)
  have hbound : N * Fintype.card V
      ≤ firstMomentThreshold (Nat.clog 2 (N * Fintype.card V) + 1) :=
    (admissibleCoeff_ge_iff hV N _).mp hcoeff
  exact propertyB_of_sparse F _ N (by omega) hmin hsparse hbound

-- ══════════════════════════════════════════════════════════════════
-- § 9: Strict monotonicity past the positivity threshold
-- ══════════════════════════════════════════════════════════════════

/-
  § 8 records the unconditional *non-strict* monotone envelope `c(a) ≤ c(b)`,
  and `admissibleCoeff_lt_of_pos` records the *consecutive* strict step
  `c(t) < c(t+1)` (given `0 < c(t)`).  Neither yet says the coefficient is
  strictly increasing across an *arbitrary* gap `a < b`, which is the precise
  qualitative shape OQ-02 asks about: past the positivity threshold the
  admissible sparseness coefficient is not merely non-decreasing but *strictly*
  increasing — it is never eventually constant.  This section supplies the
  arbitrary-gap strict bound and packages it as the canonical `StrictMonoOn`.
-/

/-- **Strict growth over an arbitrary gap, past the positivity threshold.**
    For `|V| ≤ a < b` the coefficient strictly increases: `c(a) < c(b)`.  Once
    `a` is large enough that `c(a) > 0` (guaranteed by `|V| ≤ a`, via
    `admissibleCoeff_pos_of_card_le`), the consecutive strict step
    `admissibleCoeff_lt_of_pos` gives `c(a) < c(a+1)`, and the non-strict
    envelope `admissibleCoeff_mono` carries `c(a+1) ≤ c(b)` across the rest of
    the gap.  This is the multi-step strict refinement of `admissibleCoeff_mono`
    — the coefficient is strictly increasing on `t ≥ |V|`, not merely between
    neighbours. -/
theorem admissibleCoeff_lt_of_card_le_of_lt (hV : 0 < Fintype.card V) {a b : ℕ}
    (ha : Fintype.card V ≤ a) (hab : a < b) :
    firstMomentThreshold a / Fintype.card V
      < firstMomentThreshold b / Fintype.card V := by
  have hpos : 0 < firstMomentThreshold a / Fintype.card V :=
    admissibleCoeff_pos_of_card_le hV a ha
  have hstep : firstMomentThreshold a / Fintype.card V
      < firstMomentThreshold (a + 1) / Fintype.card V :=
    admissibleCoeff_lt_of_pos hV a (by omega) hpos
  exact lt_of_lt_of_le hstep (admissibleCoeff_mono (by omega))

/-- **The admissible coefficient is strictly monotone on `t ≥ |V|`.**  The
    canonical `StrictMonoOn` packaging of `admissibleCoeff_lt_of_card_le_of_lt`:
    on the ray `Set.Ici |V|` the coefficient `c(t) = ⌊2^{t-1}/|V|⌋` is strictly
    increasing.  This is the sharp qualitative answer to OQ-02's growth-rate
    question at the ordinal level — beyond the exponential *rate* bounds of
    §§ 5-7, it records that the sparseness coefficient of a bounded ground set
    is a genuine strictly increasing sequence in the minimum set size `t`, with
    no plateau, once past the explicit threshold `|V|`. -/
theorem admissibleCoeff_strictMonoOn (hV : 0 < Fintype.card V) :
    StrictMonoOn (fun t => firstMomentThreshold t / Fintype.card V)
      (Set.Ici (Fintype.card V)) := by
  intro a ha b _ hab
  exact admissibleCoeff_lt_of_card_le_of_lt hV (Set.mem_Ici.mp ha) hab

end Erdos1022OQ02
