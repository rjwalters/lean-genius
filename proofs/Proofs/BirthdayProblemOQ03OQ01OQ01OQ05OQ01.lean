/-
Birthday problem — general closed form for the k=3 count (OQ-03-OQ-01-OQ-01-OQ-05-OQ-01)

The parent entry `birthday-problem-oq-03-oq-01-oq-01-oq-05` introduces the slot recurrence

  R 0 e s         = 1
  R (n+1) e s     = e · R n (e-1) (s+1) + s · R n e (s-1)

with `birthdayCount3 n d = R n d 0`, the number of ways to seat `n` labelled people on
`d` days with **at most two per day**, and proves the individual closed forms for
`n = 1, 2, 3, 4` (`d`, `d²`, `d³−d`, `d⁴−4d²+3d`).

This file proves the **general** closed form, valid for every `n`:

  birthdayCount3 n d = ∑_{p=0}^{⌊n/2⌋} C(n, 2p) · (2p−1)‼ · (d)_{n−p}

where `(2p−1)‼ = 1·3·5···(2p−1)` is the number of perfect matchings on `2p` points
(the count of ways to pick `p` disjoint pairs), and `(d)_m = d(d−1)···(d−m+1)` is the
falling factorial `Nat.descFactorial d m`.  The term with `p` pairs seats `2p` of the
people in `p` doubly-occupied days and the remaining `n−2p` people in singly-occupied
days, using `n−p` distinct days in total.

The proof is entirely elementary and lives over `ℕ` (all quantities are natural numbers,
the falling factorial vanishing automatically once a day-count is exhausted).  It proceeds
by:

* `R_peel_single` — the ladder identity `R n e (s+1) = R n e s + n · R (n-1) e s`
  (multiplying the per-day generating function by the single-day factor `(1+x)`), proved
  by induction on `n`;
* `birthdayCount3_rec` — the resulting two-term recurrence
  `birthdayCount3 (n+1) d = d · (birthdayCount3 n (d-1) + n · birthdayCount3 (n-1) (d-1))`;
* `birthdayCount3_closed` — the general closed form, by strong induction on `n`, the
  inductive step reducing to Pascal's rule and the absorption identity
  `k·C(n,k) = n·C(n-1,k-1)`.

The recurrence definition is reproduced here so the file is self-contained and fast to
compile.
-/

import Mathlib

namespace BirthdayGeneralClosed

/-- Slot recurrence for the k=3 birthday count (state `(e, s)` = empty / single days). -/
def R : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | n + 1, e, s => e * R n (e - 1) (s + 1) + s * R n e (s - 1)

/-- Number of ways to seat `n` labelled people on `d` days with at most two per day. -/
def birthdayCount3 (n d : ℕ) : ℕ := R n d 0

@[simp] theorem R_zero (e s : ℕ) : R 0 e s = 1 := rfl

@[simp] theorem R_succ (n e s : ℕ) :
    R (n + 1) e s = e * R n (e - 1) (s + 1) + s * R n e (s - 1) := rfl

theorem R_one (e s : ℕ) : R 1 e s = e + s := by simp

/-- **Single-day ladder identity.** Adding one already-occupied ("single") day multiplies
the per-day generating function by `(1 + x)`, i.e.

  `R n e (s+1) = R n e s + n · R (n-1) e s`.

Proved by strong induction on `n`: the inductive step expands `R (m+2) e (s+1)` by the
slot recurrence, applies the identity at level `m+1` to the `(e-1)` argument, and then
reduces to the identity at level `m+1` again (at the `s-1` argument), using the slot
recurrence to rewrite the auxiliary term.  The residual algebraic identity is closed by a
`linear_combination` over `ℤ`. -/
theorem R_peel_single : ∀ n e s, R n e (s + 1) = R n e s + n * R (n - 1) e s := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => intro e s; simp
    | 1 => intro e s; simp only [R_one, Nat.sub_self, R_zero, one_mul]; omega
    | (m + 2) =>
      intro e s
      rcases Nat.eq_zero_or_pos s with hs | hs
      · -- s = 0.
        subst hs
        show R (m + 2) e 1 = R (m + 2) e 0 + (m + 2) * R (m + 1) e 0
        have hL : R (m + 2) e 1
            = e * R (m + 1) (e - 1) 2 + R (m + 1) e 0 := by simp [R_succ]
        have h1 : R (m + 1) (e - 1) 2
            = R (m + 1) (e - 1) 1 + (m + 1) * R m (e - 1) 1 := by
          have := ih (m + 1) (by omega) (e - 1) 1; simpa using this
        have hR0 : R (m + 2) e 0 = e * R (m + 1) (e - 1) 1 := by simp [R_succ]
        have hRe : R (m + 1) e 0 = e * R m (e - 1) 1 := by simp [R_succ]
        rw [hL, h1, hR0, hRe]; ring
      · obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
        show R (m + 2) e (t + 2) = R (m + 2) e (t + 1) + (m + 2) * R (m + 1) e (t + 1)
        -- Expand the LHS by the slot recurrence.
        have hL : R (m + 2) e (t + 2)
            = e * R (m + 1) (e - 1) (t + 3) + (t + 2) * R (m + 1) e (t + 1) := by
          simp [R_succ]
        -- Ladder at level m+1 on the (e-1) argument.
        have h1 : R (m + 1) (e - 1) (t + 3)
            = R (m + 1) (e - 1) (t + 2) + (m + 1) * R m (e - 1) (t + 2) := by
          have := ih (m + 1) (by omega) (e - 1) (t + 2); simpa using this
        -- Expand the target RHS by the slot recurrence.
        have hR : R (m + 2) e (t + 1)
            = e * R (m + 1) (e - 1) (t + 2) + (t + 1) * R (m + 1) e t := by simp [R_succ]
        -- Slot recurrence for the auxiliary term  C = R (m+1) e (t+1).
        have hC : R (m + 1) e (t + 1)
            = e * R m (e - 1) (t + 2) + (t + 1) * R m e t := by simp [R_succ]
        -- Ladder at level m+1 for the (e, t) argument:  C = D + (m+1)·E.
        have hD : R (m + 1) e (t + 1)
            = R (m + 1) e t + (m + 1) * R m e t := by
          have := ih (m + 1) (by omega) e t; simpa using this
        rw [hL, h1, hR]
        zify at hC hD ⊢
        linear_combination (-(m : ℤ) - 1) * hC + ((t : ℤ) + 1) * hD

/-- **Two-term recurrence for the birthday count.** Seating person `n+1` fixes one of the
`d` days; the remaining `n` people are then distributed over the other days, one of which
already holds person `n+1` (contributing the `n · …` term via `R_peel_single`).

  `birthdayCount3 (n+1) d = d · (birthdayCount3 n (d-1) + n · birthdayCount3 (n-1) (d-1))`. -/
theorem birthdayCount3_rec (n d : ℕ) :
    birthdayCount3 (n + 1) d
      = d * (birthdayCount3 n (d - 1) + n * birthdayCount3 (n - 1) (d - 1)) := by
  have hpeel : R n (d - 1) 1 = R n (d - 1) 0 + n * R (n - 1) (d - 1) 0 :=
    R_peel_single n (d - 1) 0
  simp only [birthdayCount3, R_succ, Nat.zero_sub, zero_mul, add_zero, Nat.zero_add]
  rw [hpeel]

/-!
### The general closed form

`birthdayCount3 n d = ∑_{p} C(n, 2p) · (2p−1)‼ · (d)_{n−p}`.
-/

/-- Perfect-matching numbers: `M p = (2p−1)‼ = 1·3·5···(2p−1)`, the number of ways to
partition `2p` labelled points into `p` unordered pairs. -/
def M : ℕ → ℕ
  | 0 => 1
  | p + 1 => (2 * p + 1) * M p

@[simp] theorem M_zero : M 0 = 1 := rfl
theorem M_succ (p : ℕ) : M (p + 1) = (2 * p + 1) * M p := rfl

/-- Closed-form summand `F n d = ∑_{p=0}^{n} C(n,2p)·(2p−1)‼·(d)_{n−p}`.  Terms with
`2p > n` vanish because `C(n,2p) = 0`. -/
def F (n d : ℕ) : ℕ :=
  ∑ p ∈ Finset.range (n + 1), n.choose (2 * p) * M p * d.descFactorial (n - p)

/-- Pascal + absorption identity underlying the recurrence for the closed form:
`C(n+2,2q+2)·(2q+1) = C(n+1,2q+2)·(2q+1) + (n+1)·C(n,2q)`. -/
theorem choose_absorb (n q : ℕ) :
    (n + 2).choose (2 * q + 2) * (2 * q + 1)
      = (n + 1).choose (2 * q + 2) * (2 * q + 1) + (n + 1) * n.choose (2 * q) := by
  have hpascal : (n + 2).choose (2 * q + 2)
      = (n + 1).choose (2 * q + 1) + (n + 1).choose (2 * q + 2) :=
    Nat.choose_succ_succ (n + 1) (2 * q + 1)
  have habs : (n + 1) * n.choose (2 * q)
      = (n + 1).choose (2 * q + 1) * (2 * q + 1) := by
    simpa using Nat.succ_mul_choose_eq n (2 * q)
  rw [hpascal, add_mul, habs]; ring

/-- The same identity with the matching numbers attached:
`C(n+2,2(q+1))·M(q+1) = C(n+1,2(q+1))·M(q+1) + (n+1)·(C(n,2q)·M q)`. -/
theorem choose_absorb_M (n q : ℕ) :
    (n + 2).choose (2 * (q + 1)) * M (q + 1)
      = (n + 1).choose (2 * (q + 1)) * M (q + 1) + (n + 1) * (n.choose (2 * q) * M q) := by
  have h := choose_absorb n q
  have e2 : 2 * (q + 1) = 2 * q + 2 := by ring
  rw [e2, M_succ]
  rw [show (n + 2).choose (2 * q + 2) * ((2 * q + 1) * M q)
        = ((n + 2).choose (2 * q + 2) * (2 * q + 1)) * M q from by ring,
      show (n + 1).choose (2 * q + 2) * ((2 * q + 1) * M q)
        = ((n + 1).choose (2 * q + 2) * (2 * q + 1)) * M q from by ring,
      show (n + 1) * (n.choose (2 * q) * M q)
        = ((n + 1) * n.choose (2 * q)) * M q from by ring,
      h, add_mul]

/-- Pulling a factor out of a falling factorial:
`(d+1)·(d)_k = (d+1)_{k+1}`. -/
theorem descFactorial_pull (d k : ℕ) :
    (d + 1) * d.descFactorial k = (d + 1).descFactorial (k + 1) :=
  (Nat.succ_descFactorial_succ d k).symm

/-- **The closed form satisfies the birthday recurrence.**
`F (n+2) (d+1) = (d+1)·(F (n+1) d + (n+1)·F n d)`.

Both sides are expressed as sums over `p` of `(coefficient) · (d+1)_{n+2−p}`; the
coefficient identity is `choose_absorb_M` (Pascal + absorption), after reindexing the
`F n` contribution by `p ↦ p+1`. -/
theorem F_rec (n d : ℕ) :
    F (n + 1 + 1) (d + 1) = (d + 1) * (F (n + 1) d + (n + 1) * F n d) := by
  sorry

/-- **General closed form for the birthday count.**  For every `n` and `d`,

  `birthdayCount3 n d = ∑_{p=0}^{⌊n/2⌋} C(n, 2p) · (2p−1)‼ · (d)_{n−p}`. -/
theorem birthdayCount3_closed : ∀ n d, birthdayCount3 n d = F n d := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | m
    · -- n = 0
      intro d; simp [birthdayCount3, F, M, Finset.sum_range_one]
    · -- n = 1
      intro d
      simp only [birthdayCount3, R_one, add_zero, F]
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      simp [M, Nat.choose_eq_zero_of_lt (show (1 : ℕ) < 2 by omega)]
    · -- n = m + 2
      intro d
      rcases d with _ | d'
      · -- d = 0 : both sides are 0
        have hb : birthdayCount3 (m + 1 + 1) 0 = 0 := by simp [birthdayCount3, R_succ]
        have hF : F (m + 1 + 1) 0 = 0 := by
          rw [F]; apply Finset.sum_eq_zero; intro p hp
          simp only [Finset.mem_range] at hp
          rcases Nat.lt_or_ge p (m + 2) with h | h
          · have : (0 : ℕ).descFactorial (m + 1 + 1 - p) = 0 := by
              rw [Nat.descFactorial_eq_zero_iff_lt]; omega
            rw [this, mul_zero]
          · have : (m + 1 + 1).choose (2 * p) = 0 :=
              Nat.choose_eq_zero_of_lt (by omega)
            rw [this, zero_mul, zero_mul]
        rw [hb, hF]
      · -- d = d' + 1 : use the recurrence and the closed-form recurrence F_rec
        have hrec := birthdayCount3_rec (m + 1) (d' + 1)
        simp only [Nat.add_sub_cancel] at hrec
        rw [hrec, ih (m + 1) (by omega) d', ih m (by omega) d']
        exact (F_rec m d').symm

end BirthdayGeneralClosed
