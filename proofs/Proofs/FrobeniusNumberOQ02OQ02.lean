/-
  OQ-02-OQ-02: The Combinatorial Gorenstein Criterion for Symmetric
  Numerical Semigroups   (frobenius-number-oq-02-oq-02)

  Kunz (1970): a numerical semigroup ring k[S] is *Gorenstein* if and only if
  the semigroup S is *symmetric*, meaning the involution  z ↦ F − z  (F the
  Frobenius number) swaps the gaps and the non-gaps inside the window [0, F].
  The purely numerical signature of this symmetry is

        2 · (number of gaps in [0,F])  =  F + 1,

  i.e. "exactly half of the integers 0, …, F are gaps".  This is the number the
  commutative algebra ultimately detects (the type of the Gorenstein ring is 1).

  ## Infrastructure assessment
  Mathlib currently has *no* development of Gorenstein rings or of numerical
  semigroup rings k[t^a, t^b] (a `grep` for `gorenstein` over Mathlib returns
  nothing).  Building that machinery is a >1000-line foundational effort, so the
  ring-theoretic half of Kunz's theorem is genuinely out of reach here.  What
  we formalize instead is the full *combinatorial* content of the duality —
  the piece that carries the actual mathematics:

    * abstract:  symmetry of the gap involution  ⟹  2·(#gaps in [0,F]) = F+1;
    * concrete:  the two–generator semigroup ⟨a,b⟩ is symmetric (reusing the
                 parent's involution `frobenius_symmetry`), hence its genus is
                 exactly (F+1)/2 — the Gorenstein / type-one criterion.

  This bridges the parent's representability involution to the numerical
  criterion that a commutative-algebra proof of Gorenstein-ness would consume.

  ## Status: 0 sorries, 0 axioms
-/
import Mathlib.Tactic
import Proofs.FrobeniusNumberOQ02

namespace FrobeniusGorenstein

open FrobeniusNumber FrobeniusSymmetry

/-! ## Abstract combinatorial core: the gap-involution criterion

We work with an arbitrary decidable membership predicate `S` on `ℕ` and an
integer `F` (thought of as the Frobenius number).  All counting happens in the
window `[0, F] = Finset.range (F+1)`.  For a numerical semigroup `F` is the
largest gap, so *every* gap lies in this window and `#gaps` is the genus. -/

variable (F : ℕ) (S : ℕ → Prop) [DecidablePred S]

/-- Non-gaps (elements of `S`) inside the window `[0, F]`. -/
def nonGaps : Finset ℕ := (Finset.range (F + 1)).filter (fun z => S z)

/-- Gaps (non-elements of `S`) inside the window `[0, F]`. -/
def gaps : Finset ℕ := (Finset.range (F + 1)).filter (fun z => ¬ S z)

@[simp] theorem mem_nonGaps_iff {z : ℕ} : z ∈ nonGaps F S ↔ z ≤ F ∧ S z := by
  rw [nonGaps, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

@[simp] theorem mem_gaps_iff {z : ℕ} : z ∈ gaps F S ↔ z ≤ F ∧ ¬ S z := by
  rw [gaps, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

/-- The window `[0, F]` splits into its non-gaps and its gaps. -/
theorem nonGaps_card_add_gaps_card :
    (nonGaps F S).card + (gaps F S).card = F + 1 := by
  rw [nonGaps, gaps, Finset.filter_card_add_filter_neg_card_eq_card,
    Finset.card_range]

/-- The gap involution is *symmetric* on `[0, F]`: membership at `z` is the
negation of membership at `F − z`.  For a numerical semigroup this is exactly
the classical symmetry condition. -/
def SymmetricSet : Prop := ∀ z ≤ F, (S z ↔ ¬ S (F - z))

/-- Under symmetry, the involution `z ↦ F − z` sends non-gaps to gaps. -/
theorem card_nonGaps_le (h : SymmetricSet F S) :
    (nonGaps F S).card ≤ (gaps F S).card := by
  apply Finset.card_le_card_of_injOn (fun z => F - z)
  · intro z hz
    simp only [Finset.mem_coe, mem_nonGaps_iff] at hz
    simp only [Finset.mem_coe, mem_gaps_iff]
    exact ⟨Nat.sub_le _ _, (h z hz.1).mp hz.2⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, mem_nonGaps_iff] at hx hy
    simp only at hxy
    omega

/-- Under symmetry, the involution `z ↦ F − z` sends gaps to non-gaps. -/
theorem card_gaps_le (h : SymmetricSet F S) :
    (gaps F S).card ≤ (nonGaps F S).card := by
  apply Finset.card_le_card_of_injOn (fun z => F - z)
  · intro z hz
    simp only [Finset.mem_coe, mem_gaps_iff] at hz
    simp only [Finset.mem_coe, mem_nonGaps_iff]
    refine ⟨Nat.sub_le _ _, ?_⟩
    -- symmetry at `F - z`: `S (F - z) ↔ ¬ S (F - (F - z))`, and `F - (F - z) = z`.
    have hle : F - z ≤ F := Nat.sub_le _ _
    have hback : F - (F - z) = z := Nat.sub_sub_self hz.1
    have hsym := h (F - z) hle
    rw [hback] at hsym
    exact hsym.mpr hz.2
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, mem_gaps_iff] at hx hy
    simp only at hxy
    omega

/-- **Combinatorial Gorenstein criterion.**  If the gap involution `z ↦ F − z`
is symmetric on `[0, F]`, then exactly half of `{0, 1, …, F}` are gaps:
`2 · #gaps = F + 1`.  This is the numerical shadow of `k[S]` being Gorenstein
(Kunz 1970). -/
theorem card_gaps_two_mul (h : SymmetricSet F S) :
    2 * (gaps F S).card = F + 1 := by
  have hle₁ := card_nonGaps_le F S h
  have hle₂ := card_gaps_le F S h
  have hsum := nonGaps_card_add_gaps_card F S
  omega

/-! ## Concrete instance: the two-generator semigroup ⟨a, b⟩

We reuse the parent's involution `frobenius_symmetry` and extend it across the
boundary points `0` and `g` to obtain `SymmetricSet` for the whole window. -/

variable {a b : ℕ}

open Classical

/-- The representability involution of ⟨a,b⟩ satisfies the abstract symmetry
condition on the whole window `[0, g]` (parent covered only `0 < n < g`). -/
theorem frob_symmetricSet (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    SymmetricSet (frobeniusNumber a b) (Representable a b) := by
  intro z hz
  rcases Nat.eq_zero_or_pos z with hz0 | hzpos
  · -- z = 0 : `0` is representable, `g` is not.
    subst hz0
    rw [Nat.sub_zero]
    have hg : ¬ Representable a b (frobeniusNumber a b) := by
      simpa [frobeniusNumber] using frobenius_not_representable hab ha hb
    exact ⟨fun _ => hg, fun _ => representable_zero a b⟩
  · rcases eq_or_lt_of_le hz with hzg | hzlt
    · -- z = g : `g` is not representable, `0` is.
      subst hzg
      rw [Nat.sub_self]
      have hg : ¬ Representable a b (frobeniusNumber a b) := by
        simpa [frobeniusNumber] using frobenius_not_representable hab ha hb
      exact ⟨fun hrep => absurd hrep hg,
             fun h0 => absurd (representable_zero a b) h0⟩
    · -- interior : the parent theorem applies verbatim.
      exact frobenius_symmetry ha hb hab hzpos hzlt

/-- **Gorenstein criterion for ⟨a, b⟩.**  For coprime `a, b ≥ 2` with Frobenius
number `g = ab − a − b`, exactly half of `{0, …, g}` are non-representable:
`2 · #{gaps in [0,g]} = g + 1`.  Equivalently the numerical semigroup ⟨a,b⟩ is
symmetric, so (by Kunz's theorem) the ring `k[t^a, t^b]` is Gorenstein. -/
theorem frob_gorenstein_criterion (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    2 * (gaps (frobeniusNumber a b) (Representable a b)).card
      = frobeniusNumber a b + 1 :=
  card_gaps_two_mul _ _ (frob_symmetricSet ha hb hab)

/-- Sanity check: for ⟨3, 5⟩ the Frobenius number is `7` and there are `4` gaps
(`1, 2, 4, 7`), and indeed `2 · 4 = 8 = 7 + 1`. -/
example : 2 * (gaps (frobeniusNumber 3 5) (Representable 3 5)).card
    = frobeniusNumber 3 5 + 1 :=
  frob_gorenstein_criterion (by norm_num) (by norm_num) (by norm_num)

end FrobeniusGorenstein
