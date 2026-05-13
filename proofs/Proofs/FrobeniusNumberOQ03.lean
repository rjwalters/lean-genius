/-
  Frobenius Number — Three Generators (OQ-03)

  S2 ACT skeleton (researcher-1, 2026-05-13). Direct three-generator port of
  the closure-lemma block from `Proofs/FrobeniusNumber.lean` (lines 42–69).

  This file establishes the foundation for three-generator representability:

    Representable3 a b c n := ∃ x y z : ℕ, n = a*x + b*y + c*z

  together with the seven canonical closure lemmas: 0 is representable,
  each generator is representable, and representability is preserved under
  adding any generator. All proofs are one-line `ring` / `linarith`.

  Subsequent stages (per `research/problems/frobenius-number-oq-03/state.md`):
    S3 — frobeniusNumber3 + existence proof.
    S4 — large_representable3 for the three-consecutive family.
    S5 — frobenius_three_consecutive (Roberts d=1 closed form).
    S6+ — Roberts 3-AP, Fibonacci triples, Mersenne triples.

  0 sorries, 0 axioms. Build verification: docker-build.sh
  Proofs.FrobeniusNumberOQ03 (pending CI).
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

namespace FrobeniusOQ03

/-- A natural number `n` is **representable** by three generators `a, b, c`
    if `n = a*x + b*y + c*z` for some `x, y, z : ℕ`. -/
def Representable3 (a b c n : ℕ) : Prop :=
  ∃ (x y z : ℕ), n = a * x + b * y + c * z

/-- 0 is always representable, via the trivial witness `x = y = z = 0`. -/
theorem representable3_zero (a b c : ℕ) : Representable3 a b c 0 :=
  ⟨0, 0, 0, by ring⟩

/-- Each of the three generators is itself representable. -/
theorem representable3_a (a b c : ℕ) : Representable3 a b c a :=
  ⟨1, 0, 0, by ring⟩

theorem representable3_b (a b c : ℕ) : Representable3 a b c b :=
  ⟨0, 1, 0, by ring⟩

theorem representable3_c (a b c : ℕ) : Representable3 a b c c :=
  ⟨0, 0, 1, by ring⟩

/-- Representability is closed under adding `a`. -/
theorem representable3_add_a {a b c n : ℕ} (h : Representable3 a b c n) :
    Representable3 a b c (n + a) := by
  obtain ⟨x, y, z, hxyz⟩ := h
  exact ⟨x + 1, y, z, by linarith⟩

/-- Representability is closed under adding `b`. -/
theorem representable3_add_b {a b c n : ℕ} (h : Representable3 a b c n) :
    Representable3 a b c (n + b) := by
  obtain ⟨x, y, z, hxyz⟩ := h
  exact ⟨x, y + 1, z, by linarith⟩

/-- Representability is closed under adding `c`. -/
theorem representable3_add_c {a b c n : ℕ} (h : Representable3 a b c n) :
    Representable3 a b c (n + c) := by
  obtain ⟨x, y, z, hxyz⟩ := h
  exact ⟨x, y, z + 1, by linarith⟩

end FrobeniusOQ03
