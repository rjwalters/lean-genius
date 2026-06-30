import Mathlib

/-!
# Descartes Circle Theorem OQ-01-OQ-02-OQ-01: parity of integral Apollonian curvatures

The sibling leaf `descartes-circle-theorem-oq-01-oq-02` proved the **integrality** dictionary
for integer Descartes quadruples (an integer fourth curvature exists iff the symmetric product
is a perfect square). This follow-up answers the natural next question:

> *Among the four integer curvatures of a Descartes quadruple, how many are odd?*

The integer Descartes relation is
`descartesRelZ a b c d : (a + b + c + d)² = 2 (a² + b² + c² + d²)`.

## What this proves

1. **`descartesRelZ_sum_even`** — the sum of the four curvatures is always even
   (the right-hand side is `2·(…)`, so the left-hand square — hence its base — is even).
2. **`descartesRelZ_not_all_odd`** (the crux) — the four curvatures are **never all odd**.
   If all four were odd, the relation would force a square `≡ 2 (mod 4)`, which is impossible.
3. **`descartesRelZ_oddCount_eq_zero_or_two`** — combining (1) and (2): the number of odd
   curvatures (`oddCount`, counted via residues mod `2`) is always exactly `0` or `2`.
4. **`descartesRelZ_two_odd_of_not_all_even`** (headline) — in the **primitive** case (the four
   curvatures are not all even, e.g. when their gcd is `1`), exactly **two are odd and two are
   even**. This is the classical parity invariant of a primitive integral Apollonian gasket.
5. **`descartesRelZ_all_even_imp_two_dvd`** — the complementary `oddCount = 0` case is exactly
   the imprimitive one: all four curvatures are then divisible by `2`.

## How

The whole argument is elementary `2`-adic bookkeeping. The crux (2) substitutes `a = 2k+1`,
…, `d = 2n+1`, uses `Int.even_mul_succ_self` to record that each `kᵢ(kᵢ+1)` is even, and
`linear_combination` to distil the relation down to `4·(k+l+m+n+2)² = 16·(…) + 8`, i.e.
`(k+l+m+n+2)² ≡ 2 (mod 4)` — a contradiction discharged by `omega` after a single parity split.
Facts (3)–(5) are then pure modular arithmetic that `omega` closes once `Int.odd_iff` /
`Int.even_iff` translate parities into residues.

All results are machine-checked: `0` `sorry`, `0` `axiom`, no `native_decide`.
-/

namespace DescartesCircleParity

/-- The **integer Descartes relation** among four signed curvatures. -/
def descartesRelZ (a b c d : ℤ) : Prop :=
  (a + b + c + d) ^ 2 = 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)

/-- The number of **odd** curvatures in a quadruple, counted via residues `mod 2`
(each summand is `0` or `1`). -/
def oddCount (a b c d : ℤ) : ℤ := a % 2 + b % 2 + c % 2 + d % 2

/-- The sum of the four curvatures of an integer Descartes quadruple is even:
the relation makes `(a+b+c+d)²` equal to `2·(…)`, an even number, so its base is even. -/
theorem descartesRelZ_sum_even {a b c d : ℤ} (h : descartesRelZ a b c d) :
    Even (a + b + c + d) := by
  have h2 : Even ((a + b + c + d) ^ 2) :=
    ⟨a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2, by unfold descartesRelZ at h; rw [h]; ring⟩
  exact (Int.even_pow.mp h2).1

/-- **The four curvatures of an integer Descartes quadruple are never all odd.**

If `a, b, c, d` were all odd, writing `a = 2k+1, …, d = 2n+1` the relation collapses to
`4·(k+l+m+n+2)² = 16·(e₁+e₂+e₃+e₄) + 8`, where `eᵢ` witnesses that `kᵢ(kᵢ+1)` is even. That
says `(k+l+m+n+2)² ≡ 2 (mod 4)`, impossible since integer squares are `0` or `1 (mod 4)`. -/
theorem descartesRelZ_not_all_odd {a b c d : ℤ} (h : descartesRelZ a b c d) :
    ¬ (Odd a ∧ Odd b ∧ Odd c ∧ Odd d) := by
  rintro ⟨⟨k, rfl⟩, ⟨l, rfl⟩, ⟨m, rfl⟩, ⟨n, rfl⟩⟩
  unfold descartesRelZ at h
  obtain ⟨e1, he1⟩ := Int.even_mul_succ_self k
  obtain ⟨e2, he2⟩ := Int.even_mul_succ_self l
  obtain ⟨e3, he3⟩ := Int.even_mul_succ_self m
  obtain ⟨e4, he4⟩ := Int.even_mul_succ_self n
  have key : 4 * (k + l + m + n + 2) ^ 2 = 16 * (e1 + e2 + e3 + e4) + 8 := by
    linear_combination h + 8 * he1 + 8 * he2 + 8 * he3 + 8 * he4
  rcases Int.even_or_odd (k + l + m + n + 2) with ⟨t, ht⟩ | ⟨t, ht⟩
  · rw [ht] at key
    obtain ⟨T, hT⟩ : ∃ T, t * t = T := ⟨_, rfl⟩
    have hexp : 4 * (t + t) ^ 2 = 16 * (t * t) := by ring
    rw [hexp, hT] at key
    omega
  · rw [ht] at key
    obtain ⟨T, hT⟩ : ∃ T, t * t = T := ⟨_, rfl⟩
    have hexp : 4 * (2 * t + 1) ^ 2 = 16 * (t * t) + 16 * t + 4 := by ring
    rw [hexp, hT] at key
    omega

/-- **The number of odd curvatures is exactly `0` or `2`.**

The sum being even rules out `1` and `3`; the "never all odd" crux rules out `4`. -/
theorem descartesRelZ_oddCount_eq_zero_or_two {a b c d : ℤ} (h : descartesRelZ a b c d) :
    oddCount a b c d = 0 ∨ oddCount a b c d = 2 := by
  have hsum : (a + b + c + d) % 2 = 0 := Int.even_iff.mp (descartesRelZ_sum_even h)
  have hno : ¬ (a % 2 = 1 ∧ b % 2 = 1 ∧ c % 2 = 1 ∧ d % 2 = 1) := by
    rintro ⟨pa, pb, pc, pd⟩
    exact descartesRelZ_not_all_odd h
      ⟨Int.odd_iff.mpr pa, Int.odd_iff.mpr pb, Int.odd_iff.mpr pc, Int.odd_iff.mpr pd⟩
  unfold oddCount
  omega

/-- **Headline (primitive case): a Descartes quadruple that is not "all even" has exactly two
odd and two even curvatures.** Primitive integral Apollonian gaskets (gcd of the four
curvatures equal to `1`) always fall in this case. -/
theorem descartesRelZ_two_odd_of_not_all_even {a b c d : ℤ} (h : descartesRelZ a b c d)
    (hne : ¬ (Even a ∧ Even b ∧ Even c ∧ Even d)) :
    oddCount a b c d = 2 := by
  rcases descartesRelZ_oddCount_eq_zero_or_two h with h0 | h2
  · exfalso
    apply hne
    unfold oddCount at h0
    exact ⟨Int.even_iff.mpr (by omega), Int.even_iff.mpr (by omega),
      Int.even_iff.mpr (by omega), Int.even_iff.mpr (by omega)⟩
  · exact h2

/-- The complementary case `oddCount = 0` is exactly the **imprimitive** one:
every curvature is then divisible by `2` (the relation `h` is not needed — `oddCount = 0`
already forces all four parities to vanish — but the statement records the imprimitive
Descartes case). -/
theorem descartesRelZ_all_even_imp_two_dvd {a b c d : ℤ} (_h : descartesRelZ a b c d)
    (h0 : oddCount a b c d = 0) :
    2 ∣ a ∧ 2 ∣ b ∧ 2 ∣ c ∧ 2 ∣ d := by
  unfold oddCount at h0
  exact ⟨Int.dvd_of_emod_eq_zero (by omega), Int.dvd_of_emod_eq_zero (by omega),
    Int.dvd_of_emod_eq_zero (by omega), Int.dvd_of_emod_eq_zero (by omega)⟩

end DescartesCircleParity
