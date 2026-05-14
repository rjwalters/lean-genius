/-
  Frobenius Number — Three Generators (OQ-03)

  S2 ACT skeleton (researcher-1, 2026-05-13). Direct three-generator port of
  the closure-lemma block from `Proofs/FrobeniusNumber.lean` (lines 42–69).
  S2-fix BUILD UNBLOCKER (researcher-9, 2026-05-14, PR #18979).
  S3a ACT (researcher-12, 2026-05-14): `frobeniusNumber3` definition + a small
  set-theoretic API for the non-representable set, **self-contained** (no
  dependency on the parent `Proofs.FrobeniusNumber` file).

    Representable3 a b c n := ∃ x y z : ℕ, n = a*x + b*y + c*z

  together with the seven canonical closure lemmas (S2) and, in S3a, the
  Frobenius number definition itself plus structural lemmas:

    `noncomputable def frobeniusNumber3 a b c : ℕ := sSup { n | ¬ Representable3 a b c n }`

  with structural API:
    `representable3_of_gt_of_bddAbove` — every `n > frobeniusNumber3 a b c` is
        representable, conditional on bounded-aboveness;
    `frobeniusNumber3_le_of_subset_Iio` — abstract upper bound.

  The **existence proof** (finiteness of the non-representable set for
  `gcd(a,b,c) = 1`) is deferred to S3b once the parent file
  `Proofs/FrobeniusNumber.lean` (which provides the 2-generator Sylvester
  bound `large_representable`) is unblocked from a Mathlib v4.26.0 regression
  — see this slug's state.md "Open blockers" entry. Importing
  `Proofs.FrobeniusNumber` from this file would expose 4 pre-existing build
  errors (linarith failures at lines 193/195/199, an unsolved rewrite goal at
  line 164) that are out of S3 research scope.

  Subsequent stages (per `research/problems/frobenius-number-oq-03/state.md`):
    S3b — finiteness/existence proof via the 2-generator Sylvester bound
          (blocked on parent-file unblock).
    S4 — `large_representable3` for the three-consecutive family.
    S5 — `frobenius_three_consecutive` (Roberts d=1 closed form).
    S6+ — Roberts 3-AP, Fibonacci triples, Mersenne triples.

  0 sorries, 0 axioms.
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Lattice

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

/-! ### S3a — `frobeniusNumber3` definition + structural API -/

/-- **Three-generator Frobenius number**: the largest natural that is NOT
    representable as a non-negative ℕ-combination of `a, b, c`.

    Defined as `sSup` of the non-representable set. The supremum is attained
    whenever the non-representable set is finite (proved in S3b for
    `gcd(a,b,c) = 1`); for an empty or unbounded non-representable set the
    value defaults to `0` via the `ℕ` `sSup` convention. -/
noncomputable def frobeniusNumber3 (a b c : ℕ) : ℕ :=
  sSup { n : ℕ | ¬ Representable3 a b c n }

/-- Unfolding lemma: `frobeniusNumber3 a b c` is the `sSup` of the
    non-representable set. -/
theorem frobeniusNumber3_def (a b c : ℕ) :
    frobeniusNumber3 a b c = sSup { n : ℕ | ¬ Representable3 a b c n } :=
  rfl

/-- Every natural strictly above `frobeniusNumber3 a b c` is representable,
    provided the non-representable set is bounded above (which holds whenever
    the set is finite — see S3b for `gcd(a,b,c) = 1`). -/
theorem representable3_of_gt_frobeniusNumber3_of_bddAbove {a b c n : ℕ}
    (hbdd : BddAbove { m : ℕ | ¬ Representable3 a b c m })
    (hn : frobeniusNumber3 a b c < n) :
    Representable3 a b c n := by
  by_contra hcontra
  have hmem : n ∈ { m : ℕ | ¬ Representable3 a b c m } := hcontra
  have hle : n ≤ frobeniusNumber3 a b c := le_csSup hbdd hmem
  omega

/-- Abstract upper bound on `frobeniusNumber3 a b c`: if the non-representable
    set is contained in `Iio K` for some `K`, then `frobeniusNumber3 a b c ≤ K`
    (and is strictly below `K` when `K ≥ 1` and the set is nonempty). -/
theorem frobeniusNumber3_le_of_subset_Iio {a b c K : ℕ}
    (hsub : { n : ℕ | ¬ Representable3 a b c n } ⊆ Set.Iio K) :
    frobeniusNumber3 a b c ≤ K := by
  unfold frobeniusNumber3
  by_cases hne : ({ n : ℕ | ¬ Representable3 a b c n }).Nonempty
  · refine csSup_le hne ?_
    intro n hn
    have hlt : n ∈ Set.Iio K := hsub hn
    simp only [Set.mem_Iio] at hlt
    omega
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, csSup_empty]
    exact bot_le

/-- When the non-representable set is bounded above and nonempty, the supremum
    is attained — i.e. `frobeniusNumber3 a b c` is itself non-representable. -/
theorem not_representable3_frobeniusNumber3_of_nonempty {a b c : ℕ}
    (hbdd : BddAbove { m : ℕ | ¬ Representable3 a b c m })
    (hne : ({ m : ℕ | ¬ Representable3 a b c m }).Nonempty) :
    ¬ Representable3 a b c (frobeniusNumber3 a b c) :=
  Nat.sSup_mem hne hbdd

/-- A `Representable3` witness with the third coefficient zero collapses to a
    two-generator witness in `a, b`. (Bridge lemma used in S3b once the parent
    file `Proofs.FrobeniusNumber` is unblocked.) -/
theorem representable3_of_two_gen {a b c n x y : ℕ} (h : n = a * x + b * y) :
    Representable3 a b c n := ⟨x, y, 0, by linarith⟩

end FrobeniusOQ03
