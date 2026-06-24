import Mathlib
import Proofs.CatalanNumbersOQ01OQ01OQ02

/-
# The Catalan-triangle (ballot) recurrence `B(p,q) = B(p-1,q) + B(p,q-1)`

The parent entry (`CatalanNumbersOQ01OQ01OQ02`) introduced the generalized
ballot number / Catalan-triangle entry

  `ballot p q = C(p + q, q) - C(p + q, p + 1)`,

with the subtrahend written at the index `p + 1` (the reflected index `q - 1`) so
that the `ℕ` subtraction is never truncated in the regime `q ≤ p`
(`ballot_genuine`), and proved its closed form, its diagonal value
`ballot n n = catalan n`, and the boundary identities.

This file proves the defining **two-term recurrence of the Catalan triangle**:

  `ballot p q = ballot (p - 1) q + ballot p (q - 1)`   (for `1 ≤ q ≤ p`),

the additive law that, together with the boundary `ballot p 0 = 1`, generates the
entire triangle row by row.  The proof is *pure binomial algebra*: substituting
`p = a + 1`, `q = b + 1` makes every index a clean polynomial, Pascal's rule
`C(n+1, k+1) = C(n, k) + C(n, k+1)` splits the two binomials of `ballot p q`, and
the three genuineness bounds (from the parent's `ballot_genuine`) let the
truncated `ℕ` subtractions recombine — a single `omega` then closes the goal.

As an immediate corollary we record the **diagonal recurrence**
`ballot n n = ballot n (n - 1)` (since `ballot (n-1) n = 0` lies above the
diagonal), the rule that propagates the Catalan numbers up the edge of the
triangle.

Everything is over `ℕ`, fully machine-checked, `0`-axiom, no `native_decide`.
-/

/-- **Catalan-triangle recurrence.** For `1 ≤ q ≤ p`,
`ballot p q = ballot (p - 1) q + ballot p (q - 1)`.

The entry equals the sum of its left and lower neighbours in the triangle.
Substituting `p = a + 1`, `q = b + 1` and applying Pascal's rule to both
binomials of `ballot p q = C(p+q, q) - C(p+q, p+1)` reduces the claim to a linear
identity among six binomial coefficients with explicit genuineness bounds, closed
by `omega`. -/
theorem ballot_recurrence {p q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) :
    ballot p q = ballot (p - 1) q + ballot p (q - 1) := by
  obtain ⟨a, rfl⟩ : ∃ a, p = a + 1 := ⟨p - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, q = b + 1 := ⟨q - 1, by omega⟩
  have hba : b ≤ a := by omega
  -- normalise the predecessors `(a+1) - 1 = a`, `(b+1) - 1 = b`
  simp only [Nat.add_sub_cancel]
  -- Pascal's rule on the two binomials of `ballot (a+1) (b+1)`
  have key1 : (a + b + 2).choose (b + 1)
      = (a + b + 1).choose b + (a + b + 1).choose (b + 1) :=
    Nat.choose_succ_succ' (a + b + 1) b
  have key2 : (a + b + 2).choose (a + 2)
      = (a + b + 1).choose (a + 1) + (a + b + 1).choose (a + 2) :=
    Nat.choose_succ_succ' (a + b + 1) (a + 1)
  -- genuineness bounds so the `ℕ` subtractions do not truncate
  have hg1 : (a + b + 2).choose (a + 2) ≤ (a + b + 2).choose (b + 1) := by
    have h := ballot_genuine (p := a + 1) (q := b + 1) (by omega)
    rw [show a + 1 + (b + 1) = a + b + 2 from by omega,
        show a + 1 + 1 = a + 2 from by omega] at h
    exact h
  have hg3 : (a + b + 1).choose (a + 2) ≤ (a + b + 1).choose b := by
    have h := ballot_genuine (p := a + 1) (q := b) (by omega)
    rw [show a + 1 + b = a + b + 1 from by omega,
        show a + 1 + 1 = a + 2 from by omega] at h
    exact h
  have hg2 : (a + b + 1).choose (a + 1) ≤ (a + b + 1).choose (b + 1) := by
    rcases Nat.lt_or_ge b a with h | h
    · have hgg := ballot_genuine (p := a) (q := b + 1) (by omega)
      rw [show a + (b + 1) = a + b + 1 from by omega] at hgg
      exact hgg
    · have hb : b = a := by omega
      subst hb
      exact le_refl _
  -- unfold the three ballot values and normalise every binomial index
  simp only [ballot]
  rw [show a + 1 + (b + 1) = a + b + 2 from by omega,
      show a + (b + 1) = a + b + 1 from by omega,
      show a + 1 + b = a + b + 1 from by omega,
      show a + 1 + 1 = a + 2 from by omega]
  omega

/-- **Diagonal recurrence.** `ballot n n = ballot n (n - 1)` for `1 ≤ n`.

On the diagonal the left neighbour `ballot (n-1) n` lies above the diagonal and
vanishes (`ballot_eq_zero_of_lt`), so the two-term recurrence collapses to the
edge rule that carries the Catalan numbers `ballot n n = catalan n` up the
triangle. -/
theorem ballot_recurrence_diag {n : ℕ} (hn : 1 ≤ n) :
    ballot n n = ballot n (n - 1) := by
  have h := ballot_recurrence (p := n) (q := n) hn (le_refl n)
  rwa [ballot_eq_zero_of_lt (show n - 1 < n by omega), zero_add] at h

/-- Sanity check: `B(4,2) = B(3,2) + B(4,1)`, i.e. `9 = 5 + 4`. -/
example : ballot 4 2 = ballot 3 2 + ballot 4 1 := by decide

/-- Sanity check (diagonal): `B(3,3) = B(3,2)`, i.e. `5 = 5`. -/
example : ballot 3 3 = ballot 3 2 := by decide

/-- Sanity check: `B(5,3) = B(4,3) + B(5,2)`. -/
example : ballot 5 3 = ballot 4 3 + ballot 5 2 := by decide
