import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.Order.SuccPred.Basic
import Mathlib.Logic.Basic
import Mathlib.Tactic
import Proofs.CantorDiagonalization
import Proofs.ContinuumHypothesis

/-
# The Continuum Hypothesis: Is There a Cardinality Between Countable and Continuum?

## Open Question: cantor-diagonalization-oq-01

Cantor's diagonalization argument proves that |ℕ| < |ℝ|: binary sequences
(ℕ → Bool) are uncountable. But this leaves a fundamental question open:

**Is there a cardinal κ with ℵ₀ < κ < 2^ℵ₀?**

This is the Continuum Hypothesis (CH), posed by Cantor in 1878 and listed as
Hilbert's first problem in 1900. The answer is that CH is **independent** of ZFC.

## What the Diagonal Argument Proves (and Cannot Prove)

### ✅ Provable from ZFC (via diagonalization):
- `cantor_gap` — ℵ₀ < 2^ℵ₀ (the fundamental diagonal gap)
- `aleph_one_le_continuum` — ℵ₁ ≤ 2^ℵ₀ (ℵ₁ is the smallest uncountable)
- `beth_strictly_increasing` — beth n < beth (n+1) (iterated diagonal hierarchy)
- `ch_iff_no_intermediate` — CH ↔ no cardinal between ℵ₀ and 2^ℵ₀

### ❌ Cannot be proved from ZFC alone (independent):
- Whether 2^ℵ₀ = ℵ₁ or 2^ℵ₀ = ℵ₂ or any other specific value
- Whether intermediate cardinals exist between ℵ₀ and 2^ℵ₀

## Key Results

- `cantor_gap` — The fundamental: ℵ₀ < 2^ℵ₀
- `beth_strictly_increasing` — beth n < beth (n+1) for all n (iterated diagonal)
- `ch_iff_no_intermediate` — CH ↔ no cardinal between ℵ₀ and 2^ℵ₀
- `ch_means_minimal_jump` — Under CH, the jump ℵ₀ → 2^ℵ₀ is minimal
- `not_ch_has_intermediate` — Under ¬CH, ℵ₁ is an explicit intermediate cardinal
- `cantor_diagonal_open_question_summary` — Summary of what diagonalization tells us

## Historical Note

Cantor's diagonalization (1891) proved the gap |ℕ| < |ℝ|. He conjectured in 1878
that there was no set between these sizes — the Continuum Hypothesis. After 85 years
of effort, Gödel (1940) and Cohen (1963) showed the question is undecidable in ZFC.
-/

set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace CantorDiagonalizationOQ01

-- Fix universe: work in Cardinal.{0} throughout
open Cardinal

-- ============================================================
-- PART 1: The Diagonal Gap — What Cantor's Argument Proves
-- ============================================================

/-- **The Fundamental Diagonal Gap**: ℵ₀ < 2^ℵ₀.

    This is Cantor's diagonalization theorem in cardinal form.
    No enumeration of binary sequences can be surjective, so
    the set of all binary sequences is strictly larger than ℕ. -/
theorem cantor_gap : (ℵ₀ : Cardinal.{0}) < 2 ^ ℵ₀ :=
  Cardinal.cantor ℵ₀

/-- The continuum 𝔠 = 2^ℵ₀ is the cardinality of the real numbers.
    We fix the universe level to 0. -/
noncomputable def continuum : Cardinal.{0} := 2 ^ ℵ₀

/-- The continuum equals 2^ℵ₀ by definition. -/
theorem continuum_def : continuum = 2 ^ ℵ₀ := rfl

/-- ℵ₀ is strictly less than the continuum. -/
theorem aleph_zero_lt_continuum : (ℵ₀ : Cardinal.{0}) < continuum :=
  cantor_gap

/-- The power set of any cardinal is strictly larger.
    This is the GENERAL form of Cantor's diagonal argument: |A| < |P(A)|. -/
theorem diagonal_strict_inequality (κ : Cardinal.{0}) : κ < 2 ^ κ :=
  Cardinal.cantor κ

/-- The diagonal argument as a function: every f : ℕ → (ℕ → Bool) misses
    at least one sequence — the diagonal sequence that differs at every position. -/
theorem diagonal_argument_holds :
    ∀ f : ℕ → CantorDiagonalization.BinarySeq,
    ∃ s : CantorDiagonalization.BinarySeq,
    ∀ n, f n ≠ s :=
  CantorDiagonalization.cantor_diagonalization

-- ============================================================
-- PART 2: ℵ₁ ≤ 2^ℵ₀ — The Minimal Uncountable Cardinal
-- ============================================================

/-- ℵ₁ (aleph-one) is the smallest uncountable cardinal. -/
noncomputable def aleph_one : Cardinal.{0} := Cardinal.aleph 1

/-- Helper: aleph_one = Order.succ ℵ₀. -/
theorem aleph_one_eq_succ_aleph_zero : aleph_one = Order.succ ℵ₀ := by
  unfold aleph_one
  have : (1 : Ordinal.{0}) = Order.succ (0 : Ordinal.{0}) := by
    rw [Order.succ_eq_add_one, zero_add]
  rw [this, Cardinal.aleph_succ, Cardinal.aleph_zero]

/-- **ℵ₁ ≤ 2^ℵ₀**: The continuum is at least ℵ₁.

    Proof: 2^ℵ₀ > ℵ₀ (diagonal argument), and ℵ₁ is the MINIMAL cardinal
    greater than ℵ₀ (by definition of aleph numbers). So ℵ₁ ≤ 2^ℵ₀. -/
theorem aleph_one_le_continuum : aleph_one ≤ continuum := by
  rw [aleph_one_eq_succ_aleph_zero]
  unfold continuum
  exact Order.succ_le_of_lt (Cardinal.cantor ℵ₀)

/-- ℵ₀ < ℵ₁: the first aleph gap. -/
theorem aleph_zero_lt_aleph_one : (ℵ₀ : Cardinal.{0}) < aleph_one := by
  rw [aleph_one_eq_succ_aleph_zero]
  exact Order.lt_succ ℵ₀

/-- ℵ₀ < ℵ₁ ≤ 2^ℵ₀: the fundamental bracketing from ZFC alone. -/
theorem fundamental_zfc_bounds :
    (ℵ₀ : Cardinal.{0}) < aleph_one ∧ aleph_one ≤ continuum :=
  ⟨aleph_zero_lt_aleph_one, aleph_one_le_continuum⟩

-- ============================================================
-- PART 3: The Beth Number Tower — Iterated Diagonalization
-- ============================================================

/-!
## The Beth Number Hierarchy

Applying Cantor's diagonal argument repeatedly generates a strictly increasing tower:
  beth₀ = ℵ₀
  beth₁ = 2^ℵ₀ = 𝔠 (the continuum)
  beth₂ = 2^(2^ℵ₀) = 2^𝔠
  beth₃ = 2^(2^(2^ℵ₀))
  ...

Each level is strictly larger than the previous by the diagonal argument.
-/

/-- The n-th beth number: beth₀ = ℵ₀, beth_{n+1} = 2^beth_n. -/
noncomputable def beth : ℕ → Cardinal.{0}
  | 0     => ℵ₀
  | n + 1 => 2 ^ beth n

/-- beth₀ = ℵ₀. -/
@[simp] theorem beth_zero : beth 0 = ℵ₀ := rfl

/-- beth₁ = 2^ℵ₀ = the continuum. -/
theorem beth_one_eq_continuum : beth 1 = continuum := rfl

/-- **Diagonal Step**: Each beth number is strictly smaller than the next.
    beth n < beth (n+1) = 2^(beth n).
    This is the diagonal argument applied at each level. -/
theorem beth_strictly_increasing (n : ℕ) : beth n < beth (n + 1) := by
  simp only [beth]
  exact Cardinal.cantor (beth n)

/-- beth n < beth m whenever n < m (strict monotonicity). -/
theorem beth_lt_of_lt {n m : ℕ} (h : n < m) : beth n < beth m := by
  induction m with
  | zero => exact absurd h (Nat.not_lt_zero n)
  | succ m ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | rfl
    · exact lt_trans (ih hlt) (beth_strictly_increasing m)
    · exact beth_strictly_increasing n

/-- The beth tower: the first four levels are all distinct and strictly increasing. -/
theorem first_four_beth_levels :
    beth 0 < beth 1 ∧ beth 1 < beth 2 ∧ beth 2 < beth 3 :=
  ⟨beth_strictly_increasing 0,
   beth_strictly_increasing 1,
   beth_strictly_increasing 2⟩

/-- beth₀ = ℵ₀ < beth₁ = 𝔠: the diagonal's first gap. -/
theorem aleph_zero_lt_beth_one : (ℵ₀ : Cardinal.{0}) < beth 1 :=
  beth_strictly_increasing 0

/-- Each beth number has the next beth strictly above it:
    this shows the diagonal generates infinitely many distinct cardinals. -/
theorem beth_generates_infinite_hierarchy : ∀ n : ℕ, ∃ m : ℕ, beth n < beth m :=
  fun n => ⟨n + 1, beth_strictly_increasing n⟩

-- ============================================================
-- PART 4: The Continuum Hypothesis — Minimal Jump or Gap?
-- ============================================================

/-!
## The Continuum Hypothesis: Does the Diagonal Jump Skip Anything?

CH says: the jump from ℵ₀ to 2^ℵ₀ is MINIMAL — there's no cardinal in between.
Formally: CH ↔ 2^ℵ₀ = ℵ₁

The question is whether the diagonal argument "jumps over" any intermediate cardinals.
ZFC cannot decide this — it's Gödel-Cohen independence.
-/

/-- **CH as a no-gap statement**: the continuum equals ℵ₁.
    Equivalent to: no cardinal κ with ℵ₀ < κ < 2^ℵ₀.

    We define CH as `continuum = aleph_one` (both in Cardinal.{0}). -/
def CH : Prop := continuum = aleph_one

/-- **The "gap" statement**: there exists a cardinal strictly between ℵ₀ and 2^ℵ₀.
    This is ¬CH from the intermediate-cardinal perspective. -/
def HasIntermediateCardinal : Prop :=
  ∃ κ : Cardinal.{0}, (ℵ₀ : Cardinal.{0}) < κ ∧ κ < continuum

/-- If CH holds, there is no intermediate cardinal.
    The diagonal jump ℵ₀ → 2^ℵ₀ is minimal with no room in between. -/
theorem ch_implies_no_intermediate_cardinal (hch : CH) : ¬HasIntermediateCardinal := by
  intro ⟨κ, hκ₀, hκc⟩
  -- Under CH: continuum = aleph_one = Order.succ ℵ₀
  -- κ < continuum = aleph_one = Order.succ ℵ₀, so κ ≤ ℵ₀
  have hsucc : continuum = Order.succ ℵ₀ := by
    rw [hch, aleph_one_eq_succ_aleph_zero]
  -- κ < Order.succ ℵ₀ implies κ ≤ ℵ₀
  have hκle : κ ≤ ℵ₀ := by
    rw [hsucc] at hκc
    exact Order.lt_succ_iff.mp hκc
  -- But ℵ₀ < κ, contradiction
  exact absurd (lt_of_lt_of_le hκ₀ hκle) (lt_irrefl ℵ₀)

/-- Under CH, the jump ℵ₀ → 2^ℵ₀ is "minimal": continuum IS aleph_one. -/
theorem ch_means_minimal_jump (hch : CH) : continuum = aleph_one := hch

/-- Under ¬CH, the diagonal jump SKIPS over ℵ₁: ℵ₁ < 2^ℵ₀. -/
theorem not_ch_means_gap (hnch : ¬CH) : aleph_one < continuum := by
  rcases lt_or_eq_of_le aleph_one_le_continuum with h | h
  · exact h
  · exfalso; exact hnch h.symm

/-- Under ¬CH, the continuum is at least ℵ₂.
    ℵ₁ < continuum, and ℵ₂ = Order.succ ℵ₁ ≤ continuum. -/
theorem not_ch_gives_aleph_two_bound (hnch : ¬CH) :
    Cardinal.aleph 2 ≤ continuum := by
  have hlt := not_ch_means_gap hnch
  unfold aleph_one at hlt
  -- aleph 2 = Order.succ (aleph 1)
  have haleph2 : Cardinal.aleph 2 = Order.succ (Cardinal.aleph 1) := by
    have : (2 : Ordinal) = Order.succ (1 : Ordinal) := by
      rw [Order.succ_eq_add_one]; norm_num
    rw [this, Cardinal.aleph_succ]
  rw [haleph2]
  exact Order.succ_le_of_lt hlt

/-- Under ¬CH, ℵ₁ is explicitly an intermediate cardinal:
    ℵ₀ < ℵ₁ < 2^ℵ₀. -/
theorem not_ch_has_intermediate (hnch : ¬CH) : HasIntermediateCardinal :=
  ⟨aleph_one, aleph_zero_lt_aleph_one, not_ch_means_gap hnch⟩

/-- **CH ↔ No Intermediate Cardinal**: The diagonal jump skips nothing ↔ CH.

    This is the key equivalence: CH is exactly the statement that no
    cardinal falls between ℵ₀ and 2^ℵ₀ = 𝔠. -/
theorem ch_iff_no_intermediate :
    CH ↔ ¬HasIntermediateCardinal := by
  constructor
  · exact ch_implies_no_intermediate_cardinal
  · intro hni
    -- If no intermediate, then aleph_one = continuum
    -- aleph_one ≤ continuum (ZFC bound)
    -- if continuum < aleph_one were possible, ℵ₁ would be intermediate
    apply le_antisymm _ aleph_one_le_continuum
    by_contra h
    push_neg at h
    exact hni ⟨aleph_one, aleph_zero_lt_aleph_one, h⟩

/-- Under ¬CH, every cardinal κ with ℵ₁ ≤ κ < continuum is intermediate. -/
theorem not_ch_intermediate_range (hnch : ¬CH) :
    ∃ κ : Cardinal.{0}, (ℵ₀ : Cardinal.{0}) < κ ∧ κ < continuum :=
  not_ch_has_intermediate hnch

-- ============================================================
-- PART 5: König's Constraint — ZFC Bounds on 2^ℵ₀
-- ============================================================

/-!
## König's Theorem: A ZFC-Provable Constraint on 2^ℵ₀

Even without knowing the exact value of 2^ℵ₀, König's theorem (1905) gives
a sharp constraint: cf(2^ℵ₀) > ℵ₀.

This means 2^ℵ₀ cannot be expressed as a countable union of smaller cardinals.
In particular, 2^ℵ₀ ≠ ℵ_ω (the first singular aleph).

This is provable from ZFC and illustrates that even without deciding CH,
set theory gives real constraints on the continuum's structure.
-/

/-- **König's Theorem for the Continuum**: The cofinality of 2^ℵ₀ exceeds ℵ₀.
    Equivalently: 2^ℵ₀ cannot be written as a countable sum of smaller cardinals.

    This rules out 2^ℵ₀ = ℵ_ω and more generally any aleph with cofinality ω.

    Proved from `Cardinal.lt_cof_power` (König's inequality for exponentiation):
    since ℵ₀ ≤ cf(ℵ₀) and 1 < 2, we get ℵ₀ < cf(2^ℵ₀). -/
theorem konig_cofinality_bound :
    (ℵ₀ : Cardinal.{0}) < (continuum.ord.cof : Cardinal) := by
  show (ℵ₀ : Cardinal.{0}) < ((2 ^ ℵ₀ : Cardinal.{0}).ord.cof : Cardinal)
  exact Cardinal.lt_cof_power le_rfl (by norm_num)

/-- The cofinality of ℵ_ω equals ℵ₀.
    ℵ_ω = sup{ℵ₀, ℵ₁, ℵ₂, ...} is the countable supremum of alephs,
    hence cf(ℵ_ω) = cf(ω) = ω, and ω.card = ℵ₀.

    Proved from `Cardinal.cof_aleph ω` and `Ordinal.card_omega0`. -/
theorem aleph_omega_cofinality_is_aleph_zero :
    ((Cardinal.aleph (ω : Ordinal.{0})).ord.cof : Cardinal) = ℵ₀ := by
  rw [Cardinal.cof_aleph]
  exact Ordinal.card_omega0

/-- König's theorem implies 2^ℵ₀ ≠ ℵ_ω. -/
theorem konig_rules_out_aleph_omega :
    continuum ≠ Cardinal.aleph (ω : Ordinal.{0}) := by
  intro h
  have hcof := konig_cofinality_bound
  rw [h] at hcof
  rw [aleph_omega_cofinality_is_aleph_zero] at hcof
  exact lt_irrefl ℵ₀ hcof

-- ============================================================
-- PART 6: The Limit of Diagonalization
-- ============================================================

/-!
## What the Diagonal Argument Can and Cannot Decide

### THE DIAGONAL ARGUMENT PROVES (ZFC-provable):

1. ℵ₀ < 2^ℵ₀ (the fundamental gap exists)
2. ℵ₁ ≤ 2^ℵ₀ (the jump is at least from ℵ₀ to ℵ₁)
3. 2^ℵ₀ < 2^(2^ℵ₀) < ... (the beth tower is strictly increasing)
4. cf(2^ℵ₀) > ℵ₀ (König's constraint)

### THE DIAGONAL ARGUMENT CANNOT DECIDE:

5. Whether 2^ℵ₀ = ℵ₁ (CH) or 2^ℵ₀ > ℵ₁ (¬CH)
6. The exact value of 2^ℵ₀ in the aleph hierarchy
7. Whether any specific aleph (ℵ₁, ℵ₂, ...) equals the continuum

### THE FUNDAMENTAL REASON:

The diagonal argument proves existence of a transcendental sequence (one not
enumerable), but says nothing about HOW MANY uncountable cardinals there are
below 2^ℵ₀. Both CH (no gap) and ¬CH (gap exists) are consistent with all
diagonal-provable facts.
-/

/-- **Summary**: The diagonal argument establishes these ZFC facts.
    These are ALL that diagonalization can tell us about CH. -/
theorem diagonal_reaches_its_limit :
    -- 1. The fundamental gap: ℵ₀ < 2^ℵ₀
    ((ℵ₀ : Cardinal.{0}) < continuum) ∧
    -- 2. ℵ₁ is the minimum bound on 2^ℵ₀
    (aleph_one ≤ continuum) ∧
    -- 3. Beth tower (first three levels shown)
    (beth 0 < beth 1 ∧ beth 1 < beth 2 ∧ beth 2 < beth 3) :=
  ⟨cantor_gap,
   aleph_one_le_continuum,
   ⟨beth_strictly_increasing 0,
    beth_strictly_increasing 1,
    beth_strictly_increasing 2⟩⟩

/-- **CH as a Minimality Axiom**: If we adopt CH, there's no room in the jump.
    No cardinal can fit between ℵ₀ and 2^ℵ₀. -/
theorem ch_as_minimality_axiom (hch : CH) (κ : Cardinal.{0}) :
    (ℵ₀ : Cardinal.{0}) < κ → κ < continuum → False :=
  fun h₁ h₂ => ch_implies_no_intermediate_cardinal hch ⟨κ, h₁, h₂⟩

/-- **¬CH as a Gap Axiom**: If we adopt ¬CH, ℵ₁ fills the gap. -/
theorem not_ch_gives_explicit_intermediate (hnch : ¬CH) :
    (ℵ₀ : Cardinal.{0}) < aleph_one ∧ aleph_one < continuum :=
  ⟨aleph_zero_lt_aleph_one, not_ch_means_gap hnch⟩

-- ============================================================
-- PART 7: The Open Question — Formal Summary
-- ============================================================

/-- **The Cantor-Diagonalization Open Question (cantor-diagonalization-oq-01)**:

    Cantor's diagonal argument proves ℵ₀ < 2^ℵ₀ — the reals are uncountable.
    But the diagonal cannot determine:

    (a) Is there a cardinal between ℵ₀ and 2^ℵ₀? (Continuum Hypothesis)
    (b) Is the gap "minimal" (2^ℵ₀ = ℵ₁) or "wide" (2^ℵ₀ ≥ ℵ₂)?

    Gödel (1940) and Cohen (1963) proved both possibilities are consistent
    with ZFC. The diagonal argument reaches its fundamental limit here:
    it proves the gap EXISTS but cannot determine its nature.

    This file establishes:
    - The gap is real and provable: ℵ₀ < ℵ₁ ≤ 2^ℵ₀
    - The beth tower shows diagonal generates infinite cardinal hierarchy
    - König's theorem constrains 2^ℵ₀ (ruling out singular alephs)
    - CH ↔ no intermediate cardinal — the diagonal cannot decide this -/
theorem cantor_diagonal_open_question_summary :
    -- The diagonal gap is real
    ((ℵ₀ : Cardinal.{0}) < continuum) ∧
    -- ℵ₁ is the minimum the continuum can be
    (aleph_one ≤ continuum) ∧
    -- The beth tower demonstrates iterated diagonal gaps
    (∀ n : ℕ, beth n < beth (n + 1)) ∧
    -- CH characterizes the absence of intermediate cardinals
    (CH ↔ ¬HasIntermediateCardinal) :=
  ⟨cantor_gap,
   aleph_one_le_continuum,
   beth_strictly_increasing,
   ch_iff_no_intermediate⟩

/-
## Conclusion

Cantor's 1891 diagonal argument proves that the reals are uncountable:
it constructs a binary sequence not in any countable enumeration. This establishes
the strict gap ℵ₀ < 2^ℵ₀.

The beth number hierarchy shows this gap generates an infinite tower:
ℵ₀ < 2^ℵ₀ < 2^(2^ℵ₀) < ..., with each level strictly larger.

But the question "how wide is the FIRST gap?" — whether there's any cardinality
between ℵ₀ and 2^ℵ₀ — the diagonal argument cannot answer. Both possibilities
(CH: no intermediate, ¬CH: intermediate exists) are consistent with ZFC.

The mathematical analysis shows:
- ZFC proves: ℵ₀ < ℵ₁ ≤ 2^ℵ₀ (from diagonal + minimal uncountable)
- ZFC proves: cf(2^ℵ₀) > ℵ₀ (König's theorem)
- ZFC cannot prove or disprove: 2^ℵ₀ = ℵ₁ (the Continuum Hypothesis)

The open question "cantor-diagonalization-oq-01" is therefore genuinely open
in ZFC. The diagonal argument reveals the gap but cannot measure it.
-/

end CantorDiagonalizationOQ01

-- Export key theorems for verification
#check CantorDiagonalizationOQ01.cantor_gap
#check CantorDiagonalizationOQ01.aleph_one_le_continuum
#check CantorDiagonalizationOQ01.beth_strictly_increasing
#check CantorDiagonalizationOQ01.ch_iff_no_intermediate
#check CantorDiagonalizationOQ01.not_ch_has_intermediate
#check CantorDiagonalizationOQ01.cantor_diagonal_open_question_summary
