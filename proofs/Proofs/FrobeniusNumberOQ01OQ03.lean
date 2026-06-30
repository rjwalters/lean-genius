/-
  OQ-01-OQ-03: Two-Generator Numerical Semigroups Are Symmetric of Type One
  (frobenius-number-oq-01-oq-03)

  For coprime a, b ≥ 2 with Frobenius number g = ab - a - b, the numerical
  semigroup S = ⟨a, b⟩ = { ax + by : x, y ∈ ℕ } is **symmetric**, and moreover
  has **type one**: its set of pseudo-Frobenius numbers is exactly {g}.

  ## What is new here (vs. the parent family)

  - `frobenius-number-oq-01` proves the genus |ℕ \ S| = (a-1)(b-1)/2.
  - `frobenius-number-oq-02` (`FrobeniusSymmetry.frobenius_symmetry`) proves the
    interior duality  Rep(n) ↔ ¬Rep(g-n)  for the OPEN range 0 < n < g.

  This file:
  1. Completes the symmetry to the full closed interval 0 ≤ k ≤ g
     (`symmetric_le_frobenius`), i.e. the genuine *symmetric numerical semigroup*
     statement over the whole gap window, including the boundary k = 0 and k = g.
  2. Introduces the **pseudo-Frobenius** predicate and proves the structural
     characterisation  PF(S) = {g}  (`pseudoFrobenius_setOf_eq`), hence the
     semigroup has **type 1** (`frobenius_type_eq_one`). Type 1 is precisely the
     Gorenstein / symmetric condition in numerical-semigroup theory; two-generator
     semigroups are its prototypical examples. This invariant (the size of PF(S))
     is distinct from the genus and from the interior symmetry.

  ## Status: 0 sorries, 0 axioms (built on verified parents).
-/
import Mathlib.Data.Set.Card
import Mathlib.Tactic
import Proofs.FrobeniusNumber
import Proofs.FrobeniusNumberOQ02

namespace FrobeniusNumberOQ01OQ03

open FrobeniusNumber FrobeniusSymmetry

variable {a b : ℕ}

/-! ## Part 1: Full symmetry on the closed interval [0, g] -/

/-- **Symmetric numerical semigroup (full statement).** For coprime `a, b ≥ 2`
with Frobenius number `g = ab - a - b`, and for every `k ≤ g`, exactly one of
`k` and `g - k` is representable:
$$ k \in S \iff (g - k) \notin S. $$
This extends `FrobeniusSymmetry.frobenius_symmetry` (which assumes `0 < k < g`)
to the boundary points `k = 0` and `k = g`, giving the duality over the entire
window `0 ≤ k ≤ g`. -/
theorem symmetric_le_frobenius (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b)
    {k : ℕ} (hk : k ≤ frobeniusNumber a b) :
    Representable a b k ↔ ¬ Representable a b (frobeniusNumber a b - k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · -- k = 0:  0 ∈ S (true), and g - 0 = g ∉ S (true), so the iff is True ↔ ¬False.
    simp only [Nat.sub_zero]
    refine ⟨fun _ => frobenius_not_representable hab ha hb, fun _ => representable_zero a b⟩
  · rcases eq_or_lt_of_le hk with heq | hlt
    · -- k = g:  g ∉ S (LHS false), and g - g = 0 ∈ S (so ¬Rep is false). False ↔ False.
      subst heq
      simp only [Nat.sub_self]
      exact ⟨fun h => absurd h (frobenius_not_representable hab ha hb),
             fun h => absurd (representable_zero a b) h⟩
    · -- 0 < k < g: the interior duality from OQ-02.
      exact frobenius_symmetry ha hb hab hpos hlt

/-! ## Part 2: Pseudo-Frobenius numbers and type -/

/-- `x` is a **pseudo-Frobenius number** of the numerical semigroup `⟨a, b⟩` when
`x` is itself a gap (not representable) but `x + s` is representable for every
nonzero element `s` of the semigroup. Equivalently, `x` is maximal among the gaps
under the order `u ≤ v ⟺ v - u ∈ S`. The cardinality of this set is the
**type** of the semigroup. -/
def IsPseudoFrobenius (a b x : ℕ) : Prop :=
  ¬ Representable a b x ∧ ∀ s, 0 < s → Representable a b s → Representable a b (x + s)

/-- The Frobenius number `g` is a pseudo-Frobenius number: it is a gap, and adding
any positive representable value lands above `g`, hence back inside `S`. -/
theorem frobenius_isPseudoFrobenius (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    IsPseudoFrobenius a b (frobeniusNumber a b) := by
  refine ⟨frobenius_not_representable hab ha hb, ?_⟩
  intro s hs _
  obtain ⟨_, _, hmax⟩ := sylvester_frobenius hab ha hb
  exact hmax (frobeniusNumber a b + s) (by omega)

/-- **Uniqueness.** Every pseudo-Frobenius number equals `g`. If `x` is a gap with
`x < g`, then by symmetry `g - x ∈ S` and `g - x > 0`, so the pseudo-Frobenius
closure forces `x + (g - x) = g ∈ S`, contradicting `g ∉ S`. And no gap exceeds
`g`. -/
theorem pseudoFrobenius_eq_frobenius (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b)
    {x : ℕ} (hx : IsPseudoFrobenius a b x) : x = frobeniusNumber a b := by
  obtain ⟨hx_notrep, hx_closed⟩ := hx
  have hg_notrep : ¬ Representable a b (frobeniusNumber a b) :=
    frobenius_not_representable hab ha hb
  obtain ⟨_, _, hmax⟩ := sylvester_frobenius hab ha hb
  rcases lt_trichotomy x (frobeniusNumber a b) with hlt | heq | hgt
  · -- x < g
    exfalso
    have hx_pos : 0 < x := by
      rcases Nat.eq_zero_or_pos x with rfl | hp
      · exact absurd (representable_zero a b) hx_notrep
      · exact hp
    -- g - x is representable (symmetry), and positive
    have hgx_rep : Representable a b (frobeniusNumber a b - x) := by
      by_contra h
      exact hx_notrep ((frobenius_symmetry ha hb hab hx_pos hlt).mpr h)
    have hgsum : Representable a b (x + (frobeniusNumber a b - x)) :=
      hx_closed _ (by omega) hgx_rep
    rw [show x + (frobeniusNumber a b - x) = frobeniusNumber a b by omega] at hgsum
    exact hg_notrep hgsum
  · exact heq
  · -- x > g: every value above g is representable, contradicting that x is a gap.
    exact absurd (hmax x hgt) hx_notrep

/-- The pseudo-Frobenius numbers of `⟨a, b⟩` are exactly `{g}`. -/
theorem isPseudoFrobenius_iff (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b)
    {x : ℕ} : IsPseudoFrobenius a b x ↔ x = frobeniusNumber a b :=
  ⟨pseudoFrobenius_eq_frobenius ha hb hab, fun h => h ▸ frobenius_isPseudoFrobenius ha hb hab⟩

/-- **PF(S) = {g}.** The set of pseudo-Frobenius numbers is the singleton `{g}`. -/
theorem pseudoFrobenius_setOf_eq (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    {x : ℕ | IsPseudoFrobenius a b x} = {frobeniusNumber a b} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  exact isPseudoFrobenius_iff ha hb hab

/-- **Type one.** The two-generator numerical semigroup `⟨a, b⟩` has type 1: its set
of pseudo-Frobenius numbers has cardinality one. This is the defining property of a
*symmetric* (Gorenstein) numerical semigroup. -/
theorem frobenius_type_eq_one (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    {x : ℕ | IsPseudoFrobenius a b x}.ncard = 1 := by
  rw [pseudoFrobenius_setOf_eq ha hb hab, Set.ncard_singleton]

/-! ## Numerical sanity checks (⟨3,5⟩, g = 7) -/

-- 7 is pseudo-Frobenius for ⟨3,5⟩; e.g. its only gaps are 1,2,4,7 and only 7 is maximal.
example : frobeniusNumber 3 5 = 7 := by decide

end FrobeniusNumberOQ01OQ03
