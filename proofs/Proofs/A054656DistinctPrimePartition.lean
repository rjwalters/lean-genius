/-
# OEIS A054656 — primes absent from every distinct-prime partition of n

For every integer `n ≥ 23`, the set of primes `p ≤ n` that occur in **no**
partition of `n` into **distinct** primes equals `{n−1, n−4, n−6} ∩ P`
(`P` = the primes). Equivalently, a prime `p ≤ n` occurs in some distinct-prime
partition of `n` iff the residual `m = n − p` is a sum of distinct primes,
none equal to `p`; the only non-representable residuals are `m ∈ {1, 4, 6}`.

Source: OEIS A054656 (created April 2000, still labeled conjectural). An
AI-claimed elementary proof (GPT-5.6 Pro) is the subject of GitHub issue #41831.
This file turns the elementary core into machine-checked Lean and scaffolds the
harder engine (seed block + interval-extension + Bertrand/Ramanujan induction)
behind clearly-marked `sorry`s.

## Status of this file (first iteration)

VERIFIED (0 sorries, kernel `decide` only — no `native_decide`):
  * `not_repr_one`, `not_repr_four`, `not_repr_six`
      — 1, 4, 6 are NOT sums of distinct primes.
  * `present_iff_residual_repr`
      — the reduction: `p` present in `n` ↔ `p` prime, `p ≤ n`, and `n − p`
        is a sum of distinct primes avoiding `p`.
  * `residual_avoiding_imp_repr` — an avoiding representation is a representation.

SCAFFOLDED (`sorry`, hard engine deferred — see comments):
  * `seed_block` — a run of ≥ 64 consecutive representable residuals.
  * `interval_extension` — extend a representable interval by an unused prime.
  * `repr_of_ge_seven_ne` — every residual ≥ 7 (and the small representable ones)
    is representable avoiding one forbidden prime.
  * `A054656_main` — the main theorem for `n ≥ 23`.

## Mathlib gap (identified this iteration)

Mathlib HAS Bertrand's postulate:
  `Nat.exists_prime_lt_and_le_two_mul (n) (hn0 : n ≠ 0) :`
  `  ∃ p, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n`
(`Mathlib/NumberTheory/Bertrand.lean`, alias `Nat.bertrand`).

Mathlib does NOT have any Ramanujan-prime result. The proof sketch needs
"`(q, 2q]` contains at least TWO primes" (second Ramanujan prime `R₂ = 11`), so
that after deleting the single forbidden prime `p` an available prime `≤ 2q`
still remains. That two-primes-in-`(q,2q]` lemma must be BUILT on top of
`Nat.exists_prime_lt_and_le_two_mul` — it is the key missing ingredient.
-/

import Mathlib

namespace A054656

open Finset

/-- `m` is a sum of **distinct** primes: there is a finite set of primes whose
sum is `m`. Distinctness is automatic because `S` is a `Finset`. -/
def Repr (m : ℕ) : Prop :=
  ∃ S : Finset ℕ, (∀ q ∈ S, Nat.Prime q) ∧ S.sum id = m

/-- `m` is a sum of distinct primes, none of them equal to `avoid`. -/
def ReprAvoiding (m avoid : ℕ) : Prop :=
  ∃ S : Finset ℕ, (∀ q ∈ S, Nat.Prime q) ∧ avoid ∉ S ∧ S.sum id = m

/-- A prime `p` is *present* in `n` when it occurs in some partition of `n`
into distinct primes. -/
def Present (p n : ℕ) : Prop :=
  ∃ S : Finset ℕ, (∀ q ∈ S, Nat.Prime q) ∧ p ∈ S ∧ S.sum id = n

/-- `D n`: the primes `p ≤ n` absent from every distinct-prime partition of `n`.
`|D n|` is the OEIS sequence A054656. -/
def D (n : ℕ) : Set ℕ := {p | Nat.Prime p ∧ p ≤ n ∧ ¬ Present p n}

/-! ## Basic facts about representations -/

/-- Every prime in a representing set is `≤ m` (all summands are nonnegative). -/
theorem le_of_mem_repr {S : Finset ℕ} {p m : ℕ}
    (hsum : S.sum id = m) (hp : p ∈ S) : p ≤ m :=
  calc p = id p := rfl
    _ ≤ S.sum id := Finset.single_le_sum (fun i _ => Nat.zero_le i) hp
    _ = m := hsum

/-- An avoiding representation is in particular a representation. -/
theorem repr_of_reprAvoiding {m avoid : ℕ} (h : ReprAvoiding m avoid) : Repr m := by
  obtain ⟨S, hprime, _, hsum⟩ := h
  exact ⟨S, hprime, hsum⟩

/-! ## The three exceptional residuals: 1, 4, 6 are NOT sums of distinct primes

These are the tractable, fully-verified wins. Kernel `decide` only. -/

/-- `1` is not a sum of distinct primes (it is below the smallest prime). -/
theorem not_repr_one : ¬ Repr 1 := by
  rintro ⟨S, hprime, hsum⟩
  rcases S.eq_empty_or_nonempty with h | ⟨p, hp⟩
  · subst h; simp at hsum
  · have hle : p ≤ 1 := le_of_mem_repr hsum hp
    have h2 : 2 ≤ p := (hprime p hp).two_le
    omega

/-- `4` is not a sum of distinct primes.
The only primes `≤ 4` are `2, 3`; no subset of `{2,3}` sums to `4`. -/
theorem not_repr_four : ¬ Repr 4 := by
  rintro ⟨S, hprime, hsum⟩
  have hsub : S ⊆ ({2, 3} : Finset ℕ) := by
    intro p hp
    have hle : p ≤ 4 := le_of_mem_repr hsum hp
    have hpp := hprime p hp
    have h2 : 2 ≤ p := hpp.two_le
    interval_cases p <;> revert hpp <;> decide
  have hmem : S ∈ ({2, 3} : Finset ℕ).powerset := Finset.mem_powerset.mpr hsub
  revert hsum
  fin_cases hmem <;> decide

/-- `6` is not a sum of distinct primes.
The only primes `≤ 6` are `2, 3, 5`; no subset of `{2,3,5}` sums to `6`. -/
theorem not_repr_six : ¬ Repr 6 := by
  rintro ⟨S, hprime, hsum⟩
  have hsub : S ⊆ ({2, 3, 5} : Finset ℕ) := by
    intro p hp
    have hle : p ≤ 6 := le_of_mem_repr hsum hp
    have hpp := hprime p hp
    have h2 : 2 ≤ p := hpp.two_le
    interval_cases p <;> revert hpp <;> decide
  have hmem : S ∈ ({2, 3, 5} : Finset ℕ).powerset := Finset.mem_powerset.mpr hsub
  revert hsum
  fin_cases hmem <;> decide

/-- The three exceptional residuals are exactly `{1, 4, 6}`, packaged. Kernel
`decide` verifies the finite check; the non-representability is the content of
the three lemmas above. -/
theorem not_reprAvoiding_of_mem_exceptional {m avoid : ℕ}
    (hm : m = 1 ∨ m = 4 ∨ m = 6) : ¬ ReprAvoiding m avoid := by
  intro h
  have hr : Repr m := repr_of_reprAvoiding h
  rcases hm with rfl | rfl | rfl
  · exact not_repr_one hr
  · exact not_repr_four hr
  · exact not_repr_six hr

/-! ## The reduction lemma (VERIFIED)

`p` occurs in a distinct-prime partition of `n` iff `p` is a prime `≤ n` and the
residual `n − p` is a sum of distinct primes avoiding `p`. This is the pivot the
whole proof rests on, and it is fully elementary. -/

/-- **Reduction.** `Present p n ↔ p` prime, `p ≤ n`, and `n − p` has a
distinct-prime representation avoiding `p`. -/
theorem present_iff_residual_repr {p n : ℕ} :
    Present p n ↔ Nat.Prime p ∧ p ≤ n ∧ ReprAvoiding (n - p) p := by
  constructor
  · rintro ⟨S, hprime, hpS, hsum⟩
    have hpp : Nat.Prime p := hprime p hpS
    have hpn : p ≤ n := le_of_mem_repr hsum hpS
    refine ⟨hpp, hpn, S.erase p, ?_, Finset.notMem_erase p S, ?_⟩
    · intro q hq
      exact hprime q (Finset.mem_of_mem_erase hq)
    · -- id p + (S.erase p).sum id = S.sum id = n, so (S.erase p).sum id = n - p
      have hadd : id p + (S.erase p).sum id = S.sum id :=
        Finset.add_sum_erase S id hpS
      have hadd2 : p + (S.erase p).sum id = n := by
        rw [← hsum]; simpa using hadd
      omega
  · rintro ⟨hpp, hpn, S, hprime, hpS, hsum⟩
    refine ⟨insert p S, ?_, Finset.mem_insert_self p S, ?_⟩
    · intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact hpp
      · exact hprime q hq
    · rw [Finset.sum_insert hpS]
      simp only [id] at hsum ⊢
      omega

/-! ## Scaffolding for the representability engine (DEFERRED — `sorry`)

The heavy lifting: every residual `m ≥ 2` other than `1, 4, 6` is a sum of
distinct primes, and can even avoid one forbidden prime `p`. The claimed proof
does this via (1) an enumerated seed block of ≥ 64 consecutive representable
integers from the nine primes `≤ 23`, (2) an interval-extension engine, and
(3) a Bertrand/Ramanujan induction to push the representable interval to
infinity. Each is stated below; the proofs are deferred. -/

/-- **Seed block (DEFERRED).** There is a block of at least 64 consecutive
integers, all representable as sums of distinct primes drawn from
`{2,3,5,7,11,13,17,19,23}` with the forbidden prime `p` removed.

Deferred: this is a `decide`/`Finset.powerset`-computational enumeration over
≤ 2⁹ = 512 subsets for each excluded prime `p`. Keep it kernel-`decide` if
feasible; if the 512-subset search needs `native_decide`, disclose
`Lean.ofReduceBool` and mark the gallery entry `axiomatized`. -/
theorem seed_block (p : ℕ) (hp : Nat.Prime p) :
    ∃ A B : ℕ, 64 ≤ B - A ∧ ∀ m, A ≤ m → m ≤ B → ReprAvoiding m p := by
  sorry

/-- **Interval-extension engine (DEFERRED).** If every integer in `[A, B]` is
representable (avoiding `p`) and an unused prime `q ≤ B − A + 1` larger than `B`
(so `q` is genuinely new and `q ≠ p`) is available, then adding `q` extends
representability continuously up to `B + q`: each `m ∈ (B, B + q]` is
`q + (m − q)` with `m − q ∈ [A, B]`, and `q` is not among the seed primes since
`q > B`. Elementary once the arithmetic of shifting a covered interval by `q`
is set up. -/
theorem interval_extension {p A B q : ℕ}
    (hq : Nat.Prime q) (hqB : B < q)
    (hcover : ∀ m, A ≤ m → m ≤ B → ReprAvoiding m p)
    (hgap : q ≤ B - A + 1) :
    ∀ m, A ≤ m → m ≤ B + q → ReprAvoiding m p := by
  sorry

/-- **Every non-exceptional residual is representable avoiding `p` (DEFERRED).**
Combines `seed_block`, `interval_extension`, and the Bertrand/Ramanujan
induction. The Ramanujan step ("`(q, 2q]` has ≥ 2 primes") is the piece not yet
in Mathlib; it must be built on `Nat.exists_prime_lt_and_le_two_mul`. -/
theorem repr_of_ge_seven_ne (m p : ℕ) (hp : Nat.Prime p)
    (hm : 2 ≤ m) (hne : m ≠ 4 ∧ m ≠ 6) :
    ReprAvoiding m p := by
  sorry

/-! ## Main theorem (DEFERRED assembly) -/

/-- **A054656 main theorem (DEFERRED).** For `n ≥ 23`, the primes absent from
every distinct-prime partition of `n` are exactly `{n−1, n−4, n−6} ∩ P`.

Once `repr_of_ge_seven_ne` is discharged this follows from the verified
reduction `present_iff_residual_repr` together with the three verified
non-representability facts: for a prime `p ≤ n`, `p` is absent iff the residual
`n − p ∈ {1, 4, 6}`, i.e. `p ∈ {n−1, n−4, n−6}`. -/
theorem A054656_main (n : ℕ) (hn : 23 ≤ n) :
    D n = {p | Nat.Prime p ∧ (p = n - 1 ∨ p = n - 4 ∨ p = n - 6)} := by
  sorry

end A054656
