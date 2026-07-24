/-
# OEIS A054656 — primes absent from every distinct-prime partition of n

For every integer `n ≥ 23`, the set of primes `p ≤ n` that occur in **no**
partition of `n` into **distinct** primes equals `{n−1, n−4, n−6} ∩ P`
(`P` = the primes). Equivalently, a prime `p ≤ n` occurs in some distinct-prime
partition of `n` iff the residual `m = n − p` is a sum of distinct primes,
none equal to `p`; the only non-representable residuals are `m ∈ {1, 4, 6}`.

Source: OEIS A054656 (created April 2000, still labeled conjectural). An
AI-claimed elementary proof (GPT-5.6 Pro) is the subject of GitHub issue #41831.
This file turns the whole statement into machine-checked Lean: the elementary
core, the Richert interval engine (seed block + bounded fresh-prime extension +
Bertrand induction), and — via `Proofs/A054656TwoPrimesInterval.lean` — the
Ramanujan-type two-primes-in-`(x, 2x]` input. **0 sorries, 0 axioms.**

## Status of this file (fourth iteration, 2026-07-23): COMPLETE — 0 sorries

VERIFIED (kernel `decide` only — no `native_decide`):
  * `not_repr_one`, `not_repr_four`, `not_repr_six`
      — 1, 4, 6 are NOT sums of distinct primes.
  * `present_iff_residual_repr`
      — the reduction: `p` present in `n` ↔ `p` prime, `p ≤ n`, and `n − p`
        is a sum of distinct primes avoiding `p`.
  * `seed_block_bdd` / `seed_block` — the window `[13, 90]` is representable
    avoiding any single prime, with all witness primes `≤ 31`, via the
    `canSum` kernel subset-sum checker (soundness bridge `canSum_sound`).
  * `reprAvoidingBdd_add_fresh` — sound fresh-prime extension for *bounded*
    representations (a prime above the bound is automatically fresh).
  * **Richert interval induction (NEW, third iteration)**: `EngineInv` /
    `engineInv_step` / `engineInv_reach` — the interval `[13, B]` with witness
    bound `Q` and slack `2Q + 12 ≤ B` grows without bound, one Bertrand prime
    at a time; hence `reprAvoiding_of_thirteen_le` (every `m ≥ 13` is a sum of
    distinct primes avoiding `p`).
  * `repr_of_ge_seven_ne` (NEW: PROVED) — every residual `m ≥ 2`,
    `m ∉ {4, 6}`, with `23 ≤ m + p`, is representable avoiding `p`
    (small `m ≤ 12` by explicit witnesses, `m ≥ 13` by the engine).
  * `A054656_main` (NEW: ASSEMBLED) — the main theorem for `n ≥ 23`.

  * `exists_second_prime_in_Ioc` (FOURTH ITERATION: the former single `sorry`,
    now PROVED) — "`(x, 2x]` containing a prime `p` contains a second prime
    `q ≠ p`" (equivalently: at least TWO primes in `(x, 2x]` for `x ≥ 11`,
    i.e. the second Ramanujan prime `R₂ = 11`). Mathlib has only Bertrand
    (`Nat.exists_prime_lt_and_le_two_mul`, ONE prime in `(x, 2x]`); the
    two-prime version is proved in `Proofs/A054656TwoPrimesInterval.lean`
    (imported below) by re-running Mathlib's Bertrand central binomial
    analysis with one permitted prime removed, plus a descending prime-pair
    chain for `x < 512`. Kernel-only; no `axiom`, no `native_decide`.
    It enters the engine only through `bertrand_avoiding`, and only in the
    collision case `x < p ≤ 2x` (for `p ∉ (x, 2x]` plain Bertrand suffices).
-/

import Mathlib
import Proofs.A054656TwoPrimesInterval

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

/-- Bounded avoiding representation (third iteration): a distinct-prime
representation of `m` avoiding `avoid` whose witness primes are all `≤ bound`.
The bound is what makes the bottom-up Richert interval induction sound: a
freshly added prime strictly above the bound can never collide with the
witness, so no Ramanujan-style "second prime" is needed for *freshness* —
only for the prime *supply* when the forbidden prime blocks the Bertrand
window (see `exists_second_prime_in_Ioc`). -/
def ReprAvoidingBdd (m avoid bound : ℕ) : Prop :=
  ∃ S : Finset ℕ, (∀ q ∈ S, Nat.Prime q) ∧ avoid ∉ S ∧ (∀ q ∈ S, q ≤ bound) ∧
    S.sum id = m

/-- Forgetting the bound. -/
theorem reprAvoiding_of_bdd {m p b : ℕ} (h : ReprAvoidingBdd m p b) :
    ReprAvoiding m p := by
  obtain ⟨S, h1, h2, _, h4⟩ := h
  exact ⟨S, h1, h2, h4⟩

/-- The bound is monotone. -/
theorem reprAvoidingBdd_mono {m p b b' : ℕ} (hb : b ≤ b')
    (h : ReprAvoidingBdd m p b) : ReprAvoidingBdd m p b' := by
  obtain ⟨S, h1, h2, h3, h4⟩ := h
  exact ⟨S, h1, h2, fun q hq => le_trans (h3 q hq) hb, h4⟩

/-- Fresh-prime extension for bounded representations: a prime `q` strictly
above the bound is automatically absent from the witness, so it can always be
added. This is the sound replacement for interval-extension freshness. -/
theorem reprAvoidingBdd_add_fresh {m p b q : ℕ} (hq : Nat.Prime q)
    (hqp : q ≠ p) (hbq : b < q) (h : ReprAvoidingBdd m p b) :
    ReprAvoidingBdd (m + q) p q := by
  obtain ⟨S, h1, h2, h3, h4⟩ := h
  have hqS : q ∉ S := fun hmem => absurd (h3 q hmem) (by omega)
  refine ⟨insert q S, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hq
    · exact h1 x hx
  · intro hmem
    rcases Finset.mem_insert.mp hmem with h | h
    · exact hqp h.symm
    · exact h2 h
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact le_rfl
    · exact le_trans (h3 x hx) (le_of_lt hbq)
  · rw [Finset.sum_insert hqS, h4]
    simp only [id_eq]
    omega

/-- Lift a `canSum` certificate over a list of primes not containing `p`, all
`≤ b`, to a bounded `ReprAvoidingBdd` witness. -/
theorem reprAvoidingBdd_of_canSum {l : List ℕ} {m p b : ℕ} (hnd : l.Nodup)
    (hprime : ∀ q ∈ l, Nat.Prime q) (hp : p ∉ l) (hb : ∀ q ∈ l, q ≤ b)
    (h : canSum l m = true) : ReprAvoidingBdd m p b := by
  obtain ⟨S, hSl, hsum⟩ := canSum_sound hnd h
  exact ⟨S, fun q hq => hprime q (hSl q hq), fun hpS => hp (hSl p hpS),
    fun q hq => hb q (hSl q hq), hsum⟩

/-- Packaged seed case: a duplicate-free list of primes avoiding `p`, all
`≤ 31`, whose `checkWindow` certificate covers `[13, 90]` yields the bounded
seed interval. -/
private theorem seed_case {p : ℕ} (l : List ℕ) (hnd : l.Nodup)
    (hprime : ∀ q ∈ l, Nat.Prime q) (hp : p ∉ l) (hb : ∀ q ∈ l, q ≤ 31)
    (hwin : checkWindow l 13 90 = true) :
    ∀ m, 13 ≤ m → m ≤ 90 → ReprAvoidingBdd m p 31 :=
  fun _ h1 h2 => reprAvoidingBdd_of_canSum hnd hprime hp hb
    (checkWindow_sound hwin h1 h2)

/-- **Seed block (PROVED, second iteration).** The single window `[13, 90]`
(length `78`, so `B − A = 77 ≥ 64`) is representable avoiding any prime `p`:
if `p` is one of the eleven pool primes, the ten remaining pool primes suffice
(checked by kernel `decide` through `canSum`); if `p` is outside the pool, the
full pool works (its elements are `≤ 31`, so none equals `p` — `p ∉ seedPool`
is exactly the case hypothesis).  Kernel `decide` only — no `native_decide`,
no `Finset.powerset` blow-up.  Third iteration: strengthened to the *bounded*
form (all witness primes `≤ 31`), which the Richert interval induction
requires; the original existential form survives as `seed_block` below. -/
theorem seed_block_bdd (p : ℕ) :
    ∀ m, 13 ≤ m → m ≤ 90 → ReprAvoidingBdd m p 31 := by
  by_cases hmem : p ∈ seedPool
  · simp only [seedPool, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact seed_case [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
        (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact seed_case [2, 5, 7, 11, 13, 17, 19, 23, 29, 31]
        (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact seed_case [2, 3, 7, 11, 13, 17, 19, 23, 29, 31]
        (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact seed_case [2, 3, 5, 11, 13, 17, 19, 23, 29, 31]
        (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact seed_case [2, 3, 5, 7, 13, 17, 19, 23, 29, 31]
        (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact seed_case [2, 3, 5, 7, 11, 17, 19, 23, 29, 31]
        (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact seed_case [2, 3, 5, 7, 11, 13, 19, 23, 29, 31]
        (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact seed_case [2, 3, 5, 7, 11, 13, 17, 23, 29, 31]
        (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact seed_case [2, 3, 5, 7, 11, 13, 17, 19, 29, 31]
        (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact seed_case [2, 3, 5, 7, 11, 13, 17, 19, 23, 31]
        (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact seed_case [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact seed_case seedPool (by decide) (by decide) hmem (by decide) (by decide)

theorem seed_block (p : ℕ) (_hp : Nat.Prime p) :
    ∃ A B : ℕ, 64 ≤ B - A ∧ ∀ m, A ≤ m → m ≤ B → ReprAvoiding m p :=
  ⟨13, 90, by norm_num,
    fun m h1 h2 => reprAvoiding_of_bdd (seed_block_bdd p m h1 h2)⟩

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

/-! ## The Richert interval induction (third iteration)

Bottom-up engine: maintain an interval `[13, B]` of residuals representable
avoiding `p` with all witness primes `≤ Q`, plus the slack `2Q + 12 ≤ B`.
Each step adds one fresh prime `q ∈ (Q, 2Q]` with `q ≠ p`, extending the
interval to `[13, B + q]` (the new segment `(B, B + q]` decomposes as
`(m − q) + q` with `m − q ∈ [13, B]`, and `q` is fresh because it exceeds the
old bound `Q`). The slack self-maintains: `2q + 12 ≤ B + q ⇔ q + 12 ≤ B`,
which follows from `q ≤ 2Q ≤ B − 12`.

The prime supply `q ∈ (Q, 2Q]`, `q ≠ p` is Bertrand **except** when the
forbidden prime `p` is itself the only Bertrand witness — i.e. when
`Q < p ≤ 2Q`. Dodging it needs a *second* prime in `(Q, 2Q]`: the
Ramanujan-type strengthening (second Ramanujan prime `R₂ = 11`) that Mathlib
does not have. That single statement, in its sharpest needed form, is proved
in `Proofs/A054656TwoPrimesInterval.lean` and imported here. -/

/- **Second prime in `(x, 2x]` (Ramanujan-type; formerly this file's single
remaining `sorry`).** Now PROVED in `Proofs/A054656TwoPrimesInterval.lean`
(imported above), which supplies `A054656.exists_second_prime_in_Ioc` with
exactly the signature the engine needs: when a prime `p` lies in `(x, 2x]`
with `x ≥ 11`, the window contains another prime `q ≠ p`. The proof re-runs
Mathlib's Bertrand central-binomial analysis with one permitted prime of
factorization exponent ≤ 1 removed (threshold `512`), then descends through
an explicit prime-pair chain `521,523 → 269,271 → … → 17,19` with small-case
witnesses down to `x = 6`. Kernel-only: no `axiom`, no `native_decide`. -/

/-- **Bertrand avoiding one prime.** For `x ≥ 11` there is a prime
`q ∈ (x, 2x]` with `q ≠ p`. Proved from plain Bertrand except in the
collision case `x < p ≤ 2x`, which is delegated to
`exists_second_prime_in_Ioc`. -/
theorem bertrand_avoiding (x p : ℕ) (hx : 11 ≤ x) :
    ∃ q, Nat.Prime q ∧ q ≠ p ∧ x < q ∧ q ≤ 2 * x := by
  obtain ⟨q, hq, hxq, hq2x⟩ :=
    Nat.exists_prime_lt_and_le_two_mul x (by omega)
  by_cases hqp : q = p
  · subst hqp
    exact exists_second_prime_in_Ioc x q hx hq hxq hq2x
  · exact ⟨q, hq, hqp, hxq, hq2x⟩

/-- Engine invariant: every `m ∈ [13, B]` has a `p`-avoiding representation
by primes `≤ Q`, with slack `2Q + 12 ≤ B` (so the next Bertrand prime
`q ≤ 2Q` satisfies `q ≤ B − 12` and the extended segment's residuals stay
`≥ 13`), and `11 ≤ Q` (so Bertrand applies). -/
def EngineInv (p Q B : ℕ) : Prop :=
  11 ≤ Q ∧ 2 * Q + 12 ≤ B ∧
    ∀ m, 13 ≤ m → m ≤ B → ReprAvoidingBdd m p Q

/-- Base state: the kernel-verified seed `[13, 90]` with bound `31`
(`2·31 + 12 = 74 ≤ 90`). -/
theorem engineInv_base (p : ℕ) : EngineInv p 31 90 :=
  ⟨by norm_num, by norm_num, fun m h1 h2 => seed_block_bdd p m h1 h2⟩

/-- Engine step: one fresh prime extends the interval by at least 12. -/
theorem engineInv_step {p Q B : ℕ} (h : EngineInv p Q B) :
    ∃ Q' B', B + 12 ≤ B' ∧ EngineInv p Q' B' := by
  obtain ⟨hQ11, hQB, hcov⟩ := h
  obtain ⟨q, hqprime, hqp, hQq, hq2Q⟩ := bertrand_avoiding Q p hQ11
  refine ⟨q, B + q, by omega, by omega, by omega, ?_⟩
  intro m h13 hm
  by_cases hmB : m ≤ B
  · exact reprAvoidingBdd_mono (le_of_lt hQq) (hcov m h13 hmB)
  · have hr : ReprAvoidingBdd (m - q) p Q :=
      hcov (m - q) (by omega) (by omega)
    have hext := reprAvoidingBdd_add_fresh hqprime hqp hQq hr
    have hmq : m - q + q = m := by omega
    rwa [hmq] at hext

/-- Iterating the engine reaches arbitrarily large intervals. -/
theorem engineInv_reach (p : ℕ) :
    ∀ k : ℕ, ∃ Q B, 90 + 12 * k ≤ B ∧ EngineInv p Q B := by
  intro k
  induction k with
  | zero => exact ⟨31, 90, by norm_num, engineInv_base p⟩
  | succ n ih =>
    obtain ⟨Q, B, hB, hinv⟩ := ih
    obtain ⟨Q', B', hB', hinv'⟩ := engineInv_step hinv
    exact ⟨Q', B', by omega, hinv'⟩

/-- **Every `m ≥ 13` is a sum of distinct primes avoiding `p`** — the
engine's headline, fully machine-checked. -/
theorem reprAvoiding_of_thirteen_le (p m : ℕ) (h13 : 13 ≤ m) :
    ReprAvoiding m p := by
  obtain ⟨Q, B, hB, hinv⟩ := engineInv_reach p m
  exact reprAvoiding_of_bdd (hinv.2.2 m h13 (by omega))

/-- **Every large-enough residual is representable avoiding `p` (DEFERRED;
statement REPAIRED, second iteration).**  The first iteration omitted the
hypothesis `23 ≤ m + p`, making the statement FALSE: e.g. `¬ReprAvoiding 8 3`
(`8 = 3 + 5` is the only distinct-prime partition of `8`, and it contains `3`),
`¬ReprAvoiding 9 2` (`9 = 2 + 7` is the only
partition), `¬ReprAvoiding 10 3` (`10 = 2+3+5 = 3+7`), `¬ReprAvoiding 11 11`
(`11` itself is the only partition), `¬ReprAvoiding 12 7` (`12 = 5+7 = 2+3+7`),
and the degenerate `(m, p) ∈ {(2,2), (3,3)}`.  All counterexamples have
`m + p < 23`; in the application `m = n − p` with `n ≥ 23`, so `23 ≤ m + p`
always holds.  PROVED (third iteration): `m ≥ 13` is the Richert engine
(`reprAvoiding_of_thirteen_le`); `m ≤ 12` forces `p ≥ 11`, so the explicit
small witnesses (`{2}, {3}, {5}, {7}, {3,5}, {2,7}, {3,7}, {11}, {5,7}`)
avoid `p` outright.  Fully machine-checked (the Ramanujan-type input
`exists_second_prime_in_Ioc` is proved in the imported file). -/
theorem repr_of_ge_seven_ne (m p : ℕ) (hp : Nat.Prime p)
    (hm : 2 ≤ m) (hne : m ≠ 4 ∧ m ≠ 6) (hnp : 23 ≤ m + p) :
    ReprAvoiding m p := by
  by_cases h13 : 13 ≤ m
  · exact reprAvoiding_of_thirteen_le p m h13
  · -- `m ≤ 12`, so `p ≥ 23 − m ≥ 11`; explicit small witnesses avoid `p`.
    have h12 : m ≤ 12 := by omega
    have hp2 : 2 ≤ p := hp.two_le
    have hpne12 : p ≠ 12 := by rintro rfl; exact absurd hp (by decide)
    obtain ⟨hne4, hne6⟩ := hne
    interval_cases m
    · -- m = 2, p ≥ 21
      exact ⟨{2}, by decide, by simp only [Finset.mem_singleton]; omega,
        by decide⟩
    · -- m = 3, p ≥ 20
      exact ⟨{3}, by decide, by simp only [Finset.mem_singleton]; omega,
        by decide⟩
    · exact absurd rfl hne4
    · -- m = 5, p ≥ 18
      exact ⟨{5}, by decide, by simp only [Finset.mem_singleton]; omega,
        by decide⟩
    · exact absurd rfl hne6
    · -- m = 7, p ≥ 16
      exact ⟨{7}, by decide, by simp only [Finset.mem_singleton]; omega,
        by decide⟩
    · -- m = 8 = 3 + 5, p ≥ 15
      exact ⟨{3, 5}, by decide,
        by simp only [Finset.mem_insert, Finset.mem_singleton]; omega,
        by decide⟩
    · -- m = 9 = 2 + 7, p ≥ 14
      exact ⟨{2, 7}, by decide,
        by simp only [Finset.mem_insert, Finset.mem_singleton]; omega,
        by decide⟩
    · -- m = 10 = 3 + 7, p ≥ 13
      exact ⟨{3, 7}, by decide,
        by simp only [Finset.mem_insert, Finset.mem_singleton]; omega,
        by decide⟩
    · -- m = 11, p ≥ 12 and p ≠ 12, so p ≥ 13
      exact ⟨{11}, by decide, by simp only [Finset.mem_singleton]; omega,
        by decide⟩
    · -- m = 12 = 5 + 7, p ≥ 11
      exact ⟨{5, 7}, by decide,
        by simp only [Finset.mem_insert, Finset.mem_singleton]; omega,
        by decide⟩

/-! ## Main theorem (ASSEMBLED, third iteration) -/

/-- **A054656 main theorem.** For `n ≥ 23`, the primes absent from
every distinct-prime partition of `n` are exactly `{n−1, n−4, n−6} ∩ P`.

FULLY PROVED (fourth iteration; `#print axioms` = foundational only): for a
prime `p ≤ n`, the reduction
`present_iff_residual_repr` says `p` is absent iff the residual `n − p` has no
`p`-avoiding representation; `repr_of_ge_seven_ne` shows this forces
`n − p ∈ {1, 4, 6}` (the residual `0` is the empty representation), i.e.
`p ∈ {n−1, n−4, n−6}`; conversely those residuals are never representable
(`not_reprAvoiding_of_mem_exceptional`). -/
theorem A054656_main (n : ℕ) (hn : 23 ≤ n) :
    D n = {p | Nat.Prime p ∧ (p = n - 1 ∨ p = n - 4 ∨ p = n - 6)} := by
  ext p
  simp only [D, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hp, hpn, hnpres⟩
    refine ⟨hp, ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h4, h6⟩ := hcon
    apply hnpres
    rw [present_iff_residual_repr]
    refine ⟨hp, hpn, ?_⟩
    rcases Nat.eq_zero_or_pos (n - p) with hm0 | hmpos
    · -- residual 0: the empty representation
      exact ⟨∅, by simp, by simp, by simp [hm0]⟩
    · -- residual ≥ 1 and ∉ {1, 4, 6}: the engine applies
      have hm1 : n - p ≠ 1 := fun h => h1 (by omega)
      have hm4 : n - p ≠ 4 := fun h => h4 (by omega)
      have hm6 : n - p ≠ 6 := fun h => h6 (by omega)
      exact repr_of_ge_seven_ne (n - p) p hp (by omega) ⟨hm4, hm6⟩ (by omega)
  · rintro ⟨hp, hcase⟩
    have hpn : p ≤ n := by rcases hcase with rfl | rfl | rfl <;> omega
    refine ⟨hp, hpn, ?_⟩
    intro hpres
    rw [present_iff_residual_repr] at hpres
    obtain ⟨-, -, hrepr⟩ := hpres
    refine not_reprAvoiding_of_mem_exceptional ?_ hrepr
    rcases hcase with rfl | rfl | rfl
    · left; omega
    · right; left; omega
    · right; right; omega

end A054656
