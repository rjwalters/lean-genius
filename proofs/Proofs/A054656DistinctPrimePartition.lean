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

## Status of this file (second iteration, 2026-07-23)

VERIFIED (kernel `decide` only — no `native_decide`):
  * `not_repr_one`, `not_repr_four`, `not_repr_six`
      — 1, 4, 6 are NOT sums of distinct primes.
  * `present_iff_residual_repr`
      — the reduction: `p` present in `n` ↔ `p` prime, `p ≤ n`, and `n − p`
        is a sum of distinct primes avoiding `p`.
  * `residual_avoiding_imp_repr` — an avoiding representation is a representation.
  * `seed_block` (NEW) — the window `[13, 90]` (`B − A = 77 ≥ 64`) is
    representable avoiding any single prime, via the `canSum` kernel subset-sum
    checker over the eleven primes `≤ 31` (soundness bridge `canSum_sound`).
  * `reprAvoiding_add_prime` (NEW) — the top-down fresh-prime extension step,
    REPLACING the first iteration's `interval_extension`, whose hypotheses
    (`B < q` and `q ≤ B − A + 1`) were jointly unsatisfiable (they force
    `A = 0`, and `1` is never representable) — that engine was vacuous.

SCAFFOLDED (`sorry`, deferred):
  * `repr_of_ge_seven_ne` — every residual with `23 ≤ m + p` is representable
    avoiding `p`.  Statement REPAIRED this iteration: without `23 ≤ m + p` it
    was FALSE — counterexamples `(m, p)` = `(2,2), (3,3), (8,3), (9,2), (10,3),
    (11,11), (12,7)`, all with `m + p < 23` (see docstring).
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

/-! ## The representability engine

The heavy lifting: every residual `m ≥ 2` other than `1, 4, 6` is a sum of
distinct primes, and (for `m + p ≥ 23`) can even avoid one forbidden prime `p`.
The engine is (1) an enumerated **seed block** of consecutive representable
integers — PROVED below via a kernel subset-sum checker, (2) a **fresh-prime
extension step** — PROVED below (the original bottom-up interval statement was
vacuous, see `reprAvoiding_add_prime`), and (3) a Bertrand/Ramanujan induction
to push representability to infinity — still DEFERRED (the "two primes in
`(q, 2q]`" ingredient is not in Mathlib). -/

/-- The seed pool: the eleven primes up to `31`.

(The second iteration extended the pool from the nine primes `≤ 23`: with that
smaller pool the longest representable run avoiding `p = 23` is `[7, 70]`,
i.e. `B − A = 63` — one short of the required `64`. With primes up to `31`
the single window `[13, 90]` is representable avoiding *any one* pool prime.) -/
def seedPool : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]

/-- Kernel-friendly subset-sum decision procedure: `canSum l m = true` iff some
subset of the list `l` sums to `m`.  A direct structural recursion (use the
head or don't) — no `Finset.powerset`, so the kernel evaluates it cheaply. -/
def canSum : List ℕ → ℕ → Bool
  | [], m => m == 0
  | q :: rest, m => canSum rest m || (decide (q ≤ m) && canSum rest (m - q))

/-- Soundness of `canSum`: a successful check yields an actual `Finset` of
elements of `l` summing to `m` (duplicate-freeness of `l` makes the chosen
sublist a genuine set). -/
theorem canSum_sound : ∀ {l : List ℕ} {m : ℕ}, l.Nodup → canSum l m = true →
    ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ l) ∧ S.sum id = m := by
  intro l
  induction l with
  | nil =>
    intro m _ h
    simp only [canSum, beq_iff_eq] at h
    exact ⟨∅, by simp, by simp [h]⟩
  | cons q rest ih =>
    intro m hnd h
    simp only [canSum, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨hqm, h⟩
    · obtain ⟨S, hSl, hsum⟩ := ih (List.Nodup.of_cons hnd) h
      exact ⟨S, fun x hx => List.mem_cons_of_mem q (hSl x hx), hsum⟩
    · obtain ⟨S, hSl, hsum⟩ := ih (List.Nodup.of_cons hnd) h
      have hqS : q ∉ S := fun hq => (List.nodup_cons.mp hnd).1 (hSl q hq)
      refine ⟨insert q S, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · simp
        · exact List.mem_cons_of_mem q (hSl x hx)
      · rw [Finset.sum_insert hqS, hsum]
        simp only [id_eq]
        omega

/-- Lift a `canSum` certificate over a list of primes not containing `p` to a
`ReprAvoiding` witness. -/
theorem reprAvoiding_of_canSum {l : List ℕ} {m p : ℕ} (hnd : l.Nodup)
    (hprime : ∀ q ∈ l, Nat.Prime q) (hp : p ∉ l) (h : canSum l m = true) :
    ReprAvoiding m p := by
  obtain ⟨S, hSl, hsum⟩ := canSum_sound hnd h
  exact ⟨S, fun q hq => hprime q (hSl q hq), fun hpS => hp (hSl p hpS), hsum⟩

/-- Window check: every `m ∈ [A, B]` passes `canSum l`. -/
def checkWindow (l : List ℕ) (A B : ℕ) : Bool :=
  (List.range (B + 1 - A)).all fun i => canSum l (A + i)

theorem checkWindow_sound {l : List ℕ} {A B m : ℕ} (h : checkWindow l A B = true)
    (h1 : A ≤ m) (h2 : m ≤ B) : canSum l m = true := by
  have hi : m - A ∈ List.range (B + 1 - A) := List.mem_range.mpr (by omega)
  have hall := List.all_eq_true.mp h _ hi
  simpa [Nat.add_sub_cancel' h1] using hall

/-- Packaged seed case: a duplicate-free list of primes avoiding `p` whose
`checkWindow` certificate covers `[13, 90]` yields the seed interval. -/
private theorem seed_case {p : ℕ} (l : List ℕ) (hnd : l.Nodup)
    (hprime : ∀ q ∈ l, Nat.Prime q) (hp : p ∉ l)
    (hwin : checkWindow l 13 90 = true) :
    ∀ m, 13 ≤ m → m ≤ 90 → ReprAvoiding m p :=
  fun _ h1 h2 => reprAvoiding_of_canSum hnd hprime hp (checkWindow_sound hwin h1 h2)

/-- **Seed block (PROVED, second iteration).** The single window `[13, 90]`
(length `78`, so `B − A = 77 ≥ 64`) is representable avoiding any prime `p`:
if `p` is one of the eleven pool primes, the ten remaining pool primes suffice
(checked by kernel `decide` through `canSum`); if `p` is outside the pool, the
full pool works (its elements are `≤ 31`, so none equals `p` — `p ∉ seedPool`
is exactly the case hypothesis).  Kernel `decide` only — no `native_decide`,
no `Finset.powerset` blow-up. -/
theorem seed_block (p : ℕ) (hp : Nat.Prime p) :
    ∃ A B : ℕ, 64 ≤ B - A ∧ ∀ m, A ≤ m → m ≤ B → ReprAvoiding m p := by
  refine ⟨13, 90, by norm_num, ?_⟩
  by_cases hmem : p ∈ seedPool
  · simp only [seedPool, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact seed_case [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
        (by decide) (by decide) (by decide) (by decide)
    · exact seed_case [2, 5, 7, 11, 13, 17, 19, 23, 29, 31]
        (by decide) (by decide) (by decide) (by decide)
    · exact seed_case [2, 3, 7, 11, 13, 17, 19, 23, 29, 31]
        (by decide) (by decide) (by decide) (by decide)
    · exact seed_case [2, 3, 5, 11, 13, 17, 19, 23, 29, 31]
        (by decide) (by decide) (by decide) (by decide)
    · exact seed_case [2, 3, 5, 7, 13, 17, 19, 23, 29, 31]
        (by decide) (by decide) (by decide) (by decide)
    · exact seed_case [2, 3, 5, 7, 11, 17, 19, 23, 29, 31]
        (by decide) (by decide) (by decide) (by decide)
    · exact seed_case [2, 3, 5, 7, 11, 13, 19, 23, 29, 31]
        (by decide) (by decide) (by decide) (by decide)
    · exact seed_case [2, 3, 5, 7, 11, 13, 17, 23, 29, 31]
        (by decide) (by decide) (by decide) (by decide)
    · exact seed_case [2, 3, 5, 7, 11, 13, 17, 19, 29, 31]
        (by decide) (by decide) (by decide) (by decide)
    · exact seed_case [2, 3, 5, 7, 11, 13, 17, 19, 23, 31]
        (by decide) (by decide) (by decide) (by decide)
    · exact seed_case [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        (by decide) (by decide) (by decide) (by decide)
  · exact seed_case seedPool (by decide) (by decide) hmem (by decide)

/-- **Fresh-prime extension step (REPAIRED + PROVED, second iteration).**
Replaces the first iteration's `interval_extension`, whose hypotheses were
jointly unsatisfiable: it required both `B < q` (freshness) and
`q ≤ B − A + 1` (no gap), which force `A = 0` — and covering `[0, B]` is
impossible since `1` is never representable.  The sound engine is *top-down*:
if the residual `r` is representable avoiding `p` and `r < q` for a fresh prime
`q ≠ p`, then `r + q` is representable avoiding `p` (every element of `r`'s
witness is `≤ r < q`, so `q` is automatically new).  In the Bertrand induction
one takes `q ∈ (m/2, m]`, so `r = m − q < q` holds by construction. -/
theorem reprAvoiding_add_prime {p r q : ℕ} (hq : Nat.Prime q) (hqp : q ≠ p)
    (hr : ReprAvoiding r p) (hrq : r < q) : ReprAvoiding (r + q) p := by
  obtain ⟨S, hprime, hpS, hsum⟩ := hr
  have hqS : q ∉ S := fun hmem => absurd (le_of_mem_repr hsum hmem) (by omega)
  refine ⟨insert q S, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hq
    · exact hprime x hx
  · intro hmem
    rcases Finset.mem_insert.mp hmem with h | h
    · exact hqp h.symm
    · exact hpS h
  · rw [Finset.sum_insert hqS, hsum]
    simp only [id_eq]
    omega

/-- **Every large-enough residual is representable avoiding `p` (DEFERRED;
statement REPAIRED, second iteration).**  The first iteration omitted the
hypothesis `23 ≤ m + p`, making the statement FALSE: e.g. `¬ReprAvoiding 8 3`
(`8 = 3 + 5` is the only distinct-prime partition of `8`, and it contains `3`),
`¬ReprAvoiding 9 2` (`9 = 2 + 7` is the only
partition), `¬ReprAvoiding 10 3` (`10 = 2+3+5 = 3+7`), `¬ReprAvoiding 11 11`
(`11` itself is the only partition), `¬ReprAvoiding 12 7` (`12 = 5+7 = 2+3+7`),
and the degenerate `(m, p) ∈ {(2,2), (3,3)}`.  All counterexamples have
`m + p < 23`; in the application `m = n − p` with `n ≥ 23`, so `23 ≤ m + p`
always holds.  Combines `seed_block`, `reprAvoiding_add_prime`, and the
Bertrand/Ramanujan induction; the Ramanujan step ("`(q, 2q]` has ≥ 2 primes")
is the piece not yet in Mathlib — it must be built on
`Nat.exists_prime_lt_and_le_two_mul`. -/
theorem repr_of_ge_seven_ne (m p : ℕ) (hp : Nat.Prime p)
    (hm : 2 ≤ m) (hne : m ≠ 4 ∧ m ≠ 6) (hnp : 23 ≤ m + p) :
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
