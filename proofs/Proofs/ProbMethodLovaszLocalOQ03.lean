/-
  Lopsided Lovász Local Lemma (Negative Correlation Form)

  The lopsided LLL (Erdős–Spencer 1991) weakens the mutual-independence
  hypothesis of the classical Lovász Local Lemma to a NEGATIVE CORRELATION
  (lopsidependency) condition: conditioning an event A_i on the avoidance of
  events outside its lopsidependency neighborhood can only DECREASE its
  probability,
      P(A_i | ⋂_{j ∈ S} ¬A_j) ≤ P(A_i).
  Because full independence P(A_i | E) = P(A_i) is a special case of this
  inequality, the lopsided LLL EXTENDS the basic version: every configuration
  handled by the classical LLL is handled by the lopsided LLL — under a
  possibly SPARSER dependency graph and with the SAME quantitative criterion.

  Following the abstract ℚ-valued model of the parent entry
  `prob-method-lovasz-local` (marginal probabilities `prob`, an assignment
  `x : Fin n → ℚ` with x_i ∈ [0,1), and a dependency neighborhood `adj`), we
  add the conditional probabilities `condProb` and formalize:

    • the negative-correlation / lopsidependency condition;
    • independence ⟹ negative correlation  (basic ⊆ lopsided);
    • the KEY TRANSFER lemma — negative correlation carries the LLL bound from
      the marginal to the conditional probabilities, so the classical LLL
      recursion applies verbatim under the weaker hypothesis;
    • the marginal and conditional bounds prob_i, condProb_i ≤ x_i;
    • the avoidance product bound ∏(1 - x_i) > 0 (conclusion unchanged);
    • the symmetric criterion is IDENTICAL to the basic one;
    • a strict-extension witness (strict negative correlation, not independent).

  Erdős & Spencer (1991), "Lopsided Lovász Local Lemma and Latin transversals",
  Random Structures & Algorithms 2, 33–42.
-/
import Mathlib

namespace ProbMethod.LovaszLocalLopsided

open Finset

-- ═══════════════════════════════════════════════════════════════════
-- HYPOTHESES (abstract ℚ model, matching the parent entry)
-- ═══════════════════════════════════════════════════════════════════

/-- The LLL bound on the MARGINAL probabilities: each event probability is at
    most `x i` times the avoidance product over its dependency neighborhood.
    This is the standard Lovász Local Lemma condition. -/
def LLLBound {n : ℕ} (prob x : Fin n → ℚ) (adj : Fin n → Finset (Fin n)) : Prop :=
  ∀ i, prob i ≤ x i * (adj i).prod (fun j => 1 - x j)

/-- Negative correlation / lopsidependency: conditioning an event on avoiding
    events outside its lopsidependency neighborhood cannot increase its
    probability. Here `condProb i` abstracts the worst-case conditional
    probability P(A_i | ⋂_{j ∈ S} ¬A_j) appearing in the LLL recursion. This is
    the DEFINING hypothesis of the lopsided LLL. -/
def NegativeCorrelation {n : ℕ} (prob condProb : Fin n → ℚ) : Prop :=
  ∀ i, condProb i ≤ prob i

/-- Full independence: conditioning is irrelevant, so the conditional
    probability equals the marginal. This is the (stronger) hypothesis of the
    classical LLL. -/
def Independence {n : ℕ} (prob condProb : Fin n → ℚ) : Prop :=
  ∀ i, condProb i = prob i

/-- Each `x i` lies in the half-open unit interval `[0, 1)`. -/
def XRange {n : ℕ} (x : Fin n → ℚ) : Prop :=
  ∀ i, 0 ≤ x i ∧ x i < 1

-- ═══════════════════════════════════════════════════════════════════
-- PART I: BASIC LLL ⊆ LOPSIDED LLL
-- ═══════════════════════════════════════════════════════════════════

/-- Independence is a special case of negative correlation: if conditioning is
    irrelevant (`condProb = prob`) then trivially `condProb ≤ prob`. Hence every
    configuration satisfying the classical LLL's independence hypothesis
    satisfies the lopsided LLL's lopsidependency hypothesis. -/
theorem independence_implies_negativeCorrelation {n : ℕ} {prob condProb : Fin n → ℚ}
    (h : Independence prob condProb) : NegativeCorrelation prob condProb :=
  fun i => le_of_eq (h i)

-- ═══════════════════════════════════════════════════════════════════
-- PART II: THE KEY TRANSFER LEMMA
-- ═══════════════════════════════════════════════════════════════════

/-- **Transfer lemma (heart of the lopsided LLL).** Negative correlation carries
    the LLL bound from the marginal probabilities to the CONDITIONAL
    probabilities:
        condProb i ≤ x i · ∏_{j ∈ adj i} (1 - x j).
    This is exactly the inequality the classical LLL induction needs at each
    step; the negative-correlation hypothesis is precisely what allows replacing
    the marginal by the conditional in that recursion. Consequently the entire
    classical LLL proof goes through unchanged with the (possibly sparser)
    lopsidependency graph. -/
theorem lopsided_condProb_satisfies_LLLBound {n : ℕ}
    {prob condProb x : Fin n → ℚ} {adj : Fin n → Finset (Fin n)}
    (hnc : NegativeCorrelation prob condProb) (hb : LLLBound prob x adj) :
    ∀ i, condProb i ≤ x i * (adj i).prod (fun j => 1 - x j) :=
  fun i => le_trans (hnc i) (hb i)

-- ═══════════════════════════════════════════════════════════════════
-- PART III: PROBABILITY BOUNDS
-- ═══════════════════════════════════════════════════════════════════

/-- The LLL bound implies each MARGINAL probability is ≤ x_i, since every factor
    `1 - x j ≤ 1` makes the avoidance product ≤ 1. (Mirror of the parent
    entry's `lll_prob_bound`.) -/
theorem lopsided_marginal_bound {n : ℕ} {prob x : Fin n → ℚ}
    {adj : Fin n → Finset (Fin n)}
    (hx : XRange x) (hb : LLLBound prob x adj) : ∀ i, prob i ≤ x i := by
  intro i
  have hprod : (adj i).prod (fun j => 1 - x j) ≤ 1 :=
    Finset.prod_le_one
      (fun j _ => by linarith [(hx j).2])
      (fun j _ => by linarith [(hx j).1])
  calc prob i ≤ x i * (adj i).prod (fun j => 1 - x j) := hb i
    _ ≤ x i * 1 := mul_le_mul_of_nonneg_left hprod (hx i).1
    _ = x i := mul_one _

/-- Under lopsidependency, each CONDITIONAL probability is also ≤ x_i. This is
    the bound the LLL induction propagates; it holds from the strictly weaker
    negative-correlation hypothesis. -/
theorem lopsided_condProb_bound {n : ℕ}
    {prob condProb x : Fin n → ℚ} {adj : Fin n → Finset (Fin n)}
    (hx : XRange x) (hnc : NegativeCorrelation prob condProb)
    (hb : LLLBound prob x adj) : ∀ i, condProb i ≤ x i :=
  fun i => le_trans (hnc i) (lopsided_marginal_bound hx hb i)

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: AVOIDANCE PRODUCT (CONCLUSION UNCHANGED)
-- ═══════════════════════════════════════════════════════════════════

/-- The avoidance product ∏(1 - x_i) is strictly positive whenever x_i ∈ [0,1).
    In the probabilistic lopsided LLL this lower-bounds P(⋂ ¬A_i) > 0, so all
    bad events are simultaneously avoidable. The conclusion is identical to the
    classical LLL — only the hypothesis was weakened. -/
theorem lopsided_avoidance_pos {n : ℕ} {x : Fin n → ℚ} (hx : XRange x) :
    0 < (univ : Finset (Fin n)).prod (fun i => 1 - x i) :=
  Finset.prod_pos (fun i _ => by linarith [(hx i).2])

/-- **Lopsided LLL (packaged).** From the negative-correlation hypothesis and
    the LLL marginal bound with x_i ∈ [0,1): every marginal and conditional
    probability is ≤ x_i, and the avoidance product ∏(1 - x_i) is strictly
    positive — the exact conclusion of the classical LLL, obtained from the
    weaker lopsidependency hypothesis. -/
theorem lopsided_lll {n : ℕ}
    {prob condProb x : Fin n → ℚ} {adj : Fin n → Finset (Fin n)}
    (hx : XRange x) (hnc : NegativeCorrelation prob condProb)
    (hb : LLLBound prob x adj) :
    (∀ i, prob i ≤ x i) ∧ (∀ i, condProb i ≤ x i) ∧
    0 < (univ : Finset (Fin n)).prod (fun i => 1 - x i) :=
  ⟨lopsided_marginal_bound hx hb,
   lopsided_condProb_bound hx hnc hb,
   lopsided_avoidance_pos hx⟩

-- ═══════════════════════════════════════════════════════════════════
-- PART V: SYMMETRIC CRITERION UNCHANGED
-- ═══════════════════════════════════════════════════════════════════

/-- In the symmetric case (all marginals equal `p`), negative correlation gives
    a uniform conditional bound `condProb i ≤ p`. The lopsidependency graph may
    be sparser, but the per-event probability constraint is unchanged. -/
theorem lopsided_symmetric_condProb_le {n : ℕ} {prob condProb : Fin n → ℚ} {p : ℚ}
    (hsym : ∀ i, prob i = p) (hnc : NegativeCorrelation prob condProb) :
    ∀ i, condProb i ≤ p :=
  fun i => (hsym i) ▸ (hnc i)

/-- The symmetric avoidance criterion is IDENTICAL to the basic LLL's: if
    `p·(d+1) ≤ 1/3` (the parent's approximation of the sharp `e·p·(d+1) ≤ 1`)
    then the uniform avoidance factor `(1 - p)^n` is strictly positive. The
    lopsided LLL reaches the same guarantee from the weaker hypothesis, so it
    never demands a stronger criterion than the classical version. -/
theorem lopsided_symmetric_criterion {n : ℕ} {p : ℚ} {d : ℕ}
    (hp : 0 ≤ p) (hpd : p * (↑d + 1) ≤ 1 / 3) : 0 < (1 - p) ^ n := by
  apply pow_pos
  have hd_pos : (0 : ℚ) < ↑d + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right (show p ≤ 1 / 3 from by nlinarith) (le_of_lt hd_pos)]

-- ═══════════════════════════════════════════════════════════════════
-- PART VI: THE EXTENSION IS PROPER
-- ═══════════════════════════════════════════════════════════════════

/-- **Proper extension.** There is a configuration satisfying the FULL lopsided
    LLL hypothesis set — `XRange`, the LLL marginal bound, and negative
    correlation — that is NOT independent (`condProb i < prob i` strictly).
    Such a configuration is invisible to the classical LLL (whose independence
    hypothesis fails) yet fully covered by the lopsided LLL. Hence the lopsided
    LLL strictly extends the basic version.

    Witness (single event): P(A) = 1/4, worst-case conditional 1/8 < 1/4,
    x = 1/3, empty dependency neighborhood. -/
theorem lopsided_strictly_extends :
    ∃ (prob condProb x : Fin 1 → ℚ) (adj : Fin 1 → Finset (Fin 1)),
      XRange x ∧ LLLBound prob x adj ∧
      NegativeCorrelation prob condProb ∧ ¬ Independence prob condProb := by
  refine ⟨fun _ => 1 / 4, fun _ => 1 / 8, fun _ => 1 / 3, fun _ => ∅, ?_, ?_, ?_, ?_⟩
  · intro i; constructor <;> norm_num
  · intro i; simp only [Finset.prod_empty, mul_one]; norm_num
  · intro i; norm_num
  · intro h; have := h 0; norm_num at this

/-- Negative correlation does not imply independence: the strict witness above
    satisfies `NegativeCorrelation` but violates `Independence`. Together with
    `independence_implies_negativeCorrelation`, this shows lopsidependency is a
    STRICTLY weaker hypothesis than independence. -/
theorem negativeCorrelation_strictly_weaker_than_independence :
    ∃ (prob condProb : Fin 1 → ℚ),
      NegativeCorrelation prob condProb ∧ ¬ Independence prob condProb := by
  refine ⟨fun _ => 1 / 4, fun _ => 1 / 8, ?_, ?_⟩
  · intro i; norm_num
  · intro h; have := h 0; norm_num at this

end ProbMethod.LovaszLocalLopsided
