/-
  Erdős Problem #606 — OQ-01: The arithmetic core of the Erdős–Salamon gap structure

  Source problem: https://erdosproblems.com/606
  Parent: Proofs/Erdos606Problem.lean (Erdős–Salamon 1988 characterization, axiomatized)

  ## What is open

  Erdős–Salamon (1988) proved that for all sufficiently large n, the set of
  achievable distinct-line counts of n planar points is exactly

      {1} ∪ ([n, C(n,2)] \ {C(n,2)-1, C(n,2)-3}).

  OQ-01 asks for the *exact* threshold N₀ beyond which this holds — a hard
  question about the small-n geometry that we do NOT resolve here.

  ## What this file proves (0 axioms, fully verified)

  We isolate and formalize the **number-theoretic reason** that the two forbidden
  values are precisely `C(n,2)-1` and `C(n,2)-3`, a fact the parent file only
  states in prose (its "Part X: The Gap Structure Explained").

  Place `k` of the points on a common line. Their `C(k,2)` pairs determine a
  single line instead of `C(k,2)` distinct lines, so the line count drops by

      lineDeficit k := C(k,2) - 1.

  For k = 2 this is 0 (an "ordinary" line, no loss); for a collinear triple it is
  `lineDeficit 3 = 2`, and for a collinear quadruple `lineDeficit 4 = 5`. Using
  several disjoint such groups, the total achievable deficit ranges over all
  non-negative integer combinations of the deficits — in particular over

      { 2·a + 5·b : a, b ∈ ℕ }   (triples and quadruples alone).

  This is the **numerical semigroup ⟨2,5⟩**. Its set of gaps (non-representable
  naturals) is exactly {1, 3}, and its Frobenius number — the largest
  non-representable integer — is 3 = 2·5 − 2 − 5. Translating deficits back to
  line counts `C(n,2) - d`, the only unreachable counts in the top range are
  `C(n,2)-1` and `C(n,2)-3`, matching Erdős–Salamon exactly.

  We prove:
    * `representable_iff`     : 2a+5b representable ⇔ n ∉ {1,3}
    * `gaps_eq`              : the gap set of ⟨2,5⟩ is exactly {1,3}
    * `frobenius_two_five`   : 3 is non-representable and every m > 3 is representable
    * `lineDeficit_three/four`: the triple/quadruple deficits are 2 and 5
    * `forbidden_line_counts`: in the deficit model, the only unreachable counts at
                               the top of [.,C(n,2)] are C(n,2)-1 and C(n,2)-3.

  Honest scope: we do NOT prove geometric realizability (that disjoint collinear
  triples/quadruples can actually be placed in the plane — that is the geometric
  content carried by the parent's axioms), nor the Erdős–Salamon threshold N₀.
  We prove the self-contained combinatorial arithmetic that explains *why the
  gap set is {1,3}* and nothing else.
-/

import Mathlib.Tactic

namespace Erdos606OQ01

/-! ## Part I: The numerical semigroup ⟨2,5⟩ -/

/-- A natural number is *representable* if it is a non-negative integer combination
    of `2` and `5`. Geometrically (see header): `a` collinear triples and `b`
    collinear quadruples produce a line-count deficit of `2·a + 5·b`. -/
def Representable (n : ℕ) : Prop := ∃ a b : ℕ, n = 2 * a + 5 * b

/-- **Gap characterization of ⟨2,5⟩.** A natural number is a non-negative
    combination of 2 and 5 iff it is neither `1` nor `3`. -/
theorem representable_iff (n : ℕ) : Representable n ↔ n ≠ 1 ∧ n ≠ 3 := by
  constructor
  · rintro ⟨a, b, rfl⟩
    omega
  · rintro ⟨h1, h3⟩
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- n = 2k  (Nat.even gives n = k + k)
      exact ⟨k, 0, by omega⟩
    · -- n = 2k+1; since n ∉ {1,3} we have k ≥ 2, so n = 2(k-2) + 5
      refine ⟨k - 2, 1, ?_⟩
      omega

/-- The set of **gaps** (non-representable naturals) of ⟨2,5⟩ is exactly `{1, 3}`. -/
theorem gaps_eq : {n : ℕ | ¬ Representable n} = {1, 3} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    representable_iff]
  tauto

/-- `1` is a gap. -/
theorem one_not_representable : ¬ Representable 1 := by
  rw [representable_iff]; omega

/-- `3` is a gap. -/
theorem three_not_representable : ¬ Representable 3 := by
  rw [representable_iff]; omega

/-- **Frobenius number of ⟨2,5⟩ is 3.** `3` is not representable, yet every
    integer strictly larger than `3` is. (And `3 = 2·5 − 2 − 5`, the classical
    Sylvester–Frobenius value for two coprime generators.) -/
theorem frobenius_two_five :
    (¬ Representable 3) ∧ (∀ m : ℕ, 3 < m → Representable m) := by
  refine ⟨three_not_representable, fun m hm => ?_⟩
  rw [representable_iff]; omega

/-- The Frobenius value matches the Sylvester formula `2·5 - 2 - 5 = 3`. -/
theorem frobenius_value : 2 * 5 - 2 - 5 = 3 := by norm_num

/-! ## Part II: The line-count deficit of a collinear group -/

/-- When `k` configuration points are collinear, their `C(k,2)` pairs determine a
    single line instead of `C(k,2)` distinct lines, lowering the total line count
    by `lineDeficit k = C(k,2) - 1`. (For `k = 2`, an ordinary line, this is `0`.) -/
def lineDeficit (k : ℕ) : ℕ := k * (k - 1) / 2 - 1

/-- An ordinary line (exactly two points) costs no deficit. -/
theorem lineDeficit_two : lineDeficit 2 = 0 := by decide

/-- A collinear **triple** has deficit `2` — the smallest positive deficit. -/
theorem lineDeficit_three : lineDeficit 3 = 2 := by decide

/-- A collinear **quadruple** has deficit `5`. -/
theorem lineDeficit_four : lineDeficit 4 = 5 := by decide

/-- The two generators `2` and `5` of the semigroup are realized by the smallest
    rich lines: a triple and a quadruple. -/
theorem generators_are_deficits :
    lineDeficit 3 = 2 ∧ lineDeficit 4 = 5 :=
  ⟨lineDeficit_three, lineDeficit_four⟩

/-- Every representable deficit is realizable using **only triples and quadruples**:
    `2·a + 5·b = a · lineDeficit 3 + b · lineDeficit 4`. -/
theorem representable_via_triples_quadruples (n : ℕ) :
    Representable n ↔ ∃ a b : ℕ, n = a * lineDeficit 3 + b * lineDeficit 4 := by
  rw [lineDeficit_three, lineDeficit_four]
  constructor
  · rintro ⟨a, b, rfl⟩; exact ⟨a, b, by ring⟩
  · rintro ⟨a, b, rfl⟩; exact ⟨a, b, by ring⟩

/-! ## Part III: Forbidden line counts at the top of the range -/

/-- Maximum line count for `n` points (general position): `C(n,2) = n(n-1)/2`.
    Matches `Erdos606.maxLines`. -/
def maxLines (n : ℕ) : ℕ := n * (n - 1) / 2

/-- In the deficit model, a line count `c ≤ maxLines n` is **achievable** iff the
    induced deficit `maxLines n - c` is representable (a combination of triples and
    quadruples). -/
def DeficitAchievable (n c : ℕ) : Prop :=
  c ≤ maxLines n ∧ Representable (maxLines n - c)

/-- A top-range line count is unachievable in the deficit model **iff** its deficit
    is one of the two gaps `1` or `3`. -/
theorem not_deficitAchievable_iff (n c : ℕ) (h : c ≤ maxLines n) :
    ¬ DeficitAchievable n c ↔ (maxLines n - c = 1 ∨ maxLines n - c = 3) := by
  unfold DeficitAchievable
  rw [not_and_or]
  constructor
  · rintro (hc | hrep)
    · exact absurd h hc
    · rw [representable_iff] at hrep; tauto
  · intro hd
    right
    rw [representable_iff]; tauto

/-- **The exact forbidden counts.** For `n ≥ 4` (so that `maxLines n ≥ 4` and both
    values lie strictly inside the range), the line counts `maxLines n - 1` and
    `maxLines n - 3` are NOT deficit-achievable, while `maxLines n`,
    `maxLines n - 2` and `maxLines n - 4` ARE. These are precisely the two
    Erdős–Salamon gaps `C(n,2)-1`, `C(n,2)-3`. -/
theorem forbidden_line_counts (n : ℕ) (hn : 4 ≤ n) :
    ¬ DeficitAchievable n (maxLines n - 1) ∧
    ¬ DeficitAchievable n (maxLines n - 3) ∧
    DeficitAchievable n (maxLines n) ∧
    DeficitAchievable n (maxLines n - 2) ∧
    DeficitAchievable n (maxLines n - 4) := by
  -- maxLines n ≥ 6 for n ≥ 4, so all the subtractions below behave.
  have hmax : 6 ≤ maxLines n := by
    have : 4 * 3 / 2 ≤ n * (n - 1) / 2 := by
      apply Nat.div_le_div_right
      have h1 : 4 ≤ n := hn
      have h2 : 3 ≤ n - 1 := by omega
      calc 4 * 3 ≤ n * 3 := by exact Nat.mul_le_mul_right 3 h1
        _ ≤ n * (n - 1) := by exact Nat.mul_le_mul_left n h2
    simpa [maxLines] using this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- deficit = 1, a gap
    rw [not_deficitAchievable_iff n _ (by omega)]
    left; omega
  · -- deficit = 3, a gap
    rw [not_deficitAchievable_iff n _ (by omega)]
    right; omega
  · -- deficit = 0 = 2·0 + 5·0
    exact ⟨le_refl _, 0, 0, by omega⟩
  · -- deficit = 2 = one triple
    exact ⟨by omega, 1, 0, by omega⟩
  · -- deficit = 4 = two triples
    exact ⟨by omega, 2, 0, by omega⟩

/-- **Summary corollary.** The set of forbidden deficits — equivalently the set of
    forbidden line counts `maxLines n - d` — is exactly `{1, 3}`, a set of size 2.
    This is the arithmetic content of the Erdős–Salamon characterization. -/
theorem exactly_two_gaps : ({1, 3} : Set ℕ).ncard = 2 := by
  rw [Set.ncard_pair (by norm_num)]

end Erdos606OQ01
