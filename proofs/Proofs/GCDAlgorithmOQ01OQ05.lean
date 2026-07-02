import Mathlib

/-
# Uniqueness of the Euclidean Worst Case: Fibonacci Pairs Are the Only Extremal Pairs

## Open Question OQ-01-OQ-05 (from `gcd-algorithm-oq-01`)

Lamé's theorem gives the tight lower bounds on the inputs of the Euclidean
algorithm: a pair `(a, b)` with `0 < b < a` requiring `n` division steps
satisfies

  `fib (n+1) ≤ b`      and      `fib (n+2) ≤ a`,

and consecutive Fibonacci numbers `(fib (n+2), fib (n+1))` realise `n` steps,
so both bounds are attained.  The parent entry `gcd-algorithm-oq-01` proves the
`b`-bound (`fib (n+1)` is the minimal second input); its sharp sibling
`gcd-algorithm-oq-01-oq-03-oq-01` proves both bounds.  Neither settles the
**uniqueness** question this open question asks:

> Show any pair requiring `n` division steps satisfies `a ≥ F_{n+2}`,
> `b ≥ F_{n+1}`, with equality forcing `(a, b) = (F_{n+2}, F_{n+1})`.

This entry proves that the Fibonacci pair is the **unique** extremal pair:

* `steps_a_lower_bound`    — `fib (n+2) ≤ a`  (the `a`-side of Lamé, on the
  canonical step counter, re-derived here for a self-contained account);
* `worst_case_forces_fib`  — **the forcing/uniqueness result**: if a pair with
  `0 < b < a` takes `n` steps and attains the `a`-bound (`a = fib (n+2)`), then
  `b` is forced to the exact value `fib (n+1)`;
* `worst_case_pair_unique` — the packaged pair statement
  `a = fib (n+2) ∧ b = fib (n+1)`;
* `worst_case_iff`         — the full characterisation: for `n ≥ 1` the pairs
  `(a, b)` with `0 < b < a`, `n` steps, and `a = fib (n+2)` are *exactly*
  `{(fib (n+2), fib (n+1))}`;
* `steps_sum_lower_bound`  — the size bound `fib (n+3) ≤ a + b`.

## Why the forcing is one-directional

Attaining the `b`-bound does **not** force the Fibonacci pair: e.g. `n = 2`,
`b = fib 3 = 2`, `a = 5` also takes `2` steps (`euclideanSteps 5 2 = 2`), yet
`5 ≠ fib 4 = 3`.  The *larger* input is the rigid one: once `a` hits its minimum
`fib (n+2)`, the interval `fib (n+1) ≤ b < a = fib (n+1) + fib n` is squeezed —
the remainder bound `fib n ≤ a % b` (from Lamé applied one level down) forces
`b ≤ fib (n+1)`, collapsing `b` to `fib (n+1)`.

## Proof engine

Everything runs off a single strong-induction Lamé bound
`lame_pair_bound`, which returns *both* `fib (n+1) ≤ b` and, one level down,
`fib n ≤ a % b`.  The forcing then follows from the linear arithmetic
`a = fib n + fib (n+1)`, `a % b = a - b` (valid because `a < 2b`), and
`fib n ≤ a % b`.  Small Fibonacci values are discharged by `decide` (kernel
reduction, no `Lean.ofReduceBool`), keeping the entry axiom-free.

## References

- Lamé, G. (1844). Note sur la limite du nombre des divisions dans la recherche
  du plus grand commun diviseur entre deux nombres entiers.
- Parent `gcd-algorithm-oq-01` (Lamé's theorem, `fib (n+1)` minimal `b`).
- Sibling `gcd-algorithm-oq-01-oq-03-oq-01` (both Lamé bounds, sharp side).

## Axioms: 0 | Sorries: 0
-/

namespace GCDAlgorithmOQ01OQ05

open Nat

/-! ## Self-contained step counter and its basic lemmas

We recount the Euclidean division steps with the same well-founded definition
used by the parent, so that this entry stands alone. -/

/-- Count division steps in the Euclidean algorithm. -/
def euclideanSteps (a b : ℕ) : ℕ :=
  if b = 0 then 0
  else euclideanSteps b (a % b) + 1
termination_by b
decreasing_by exact Nat.mod_lt a (Nat.pos_of_ne_zero ‹b ≠ 0›)

@[simp] theorem euclideanSteps_zero (a : ℕ) : euclideanSteps a 0 = 0 := by
  rw [euclideanSteps]; simp

/-- Unfolding lemma for a positive second argument. -/
theorem euclideanSteps_pos_eq (a b : ℕ) (hb : 0 < b) :
    euclideanSteps a b = euclideanSteps b (a % b) + 1 := by
  rw [euclideanSteps]; simp [Nat.pos_iff_ne_zero.mp hb]

theorem euclideanSteps_ge_one (a : ℕ) {b : ℕ} (hb : 0 < b) :
    1 ≤ euclideanSteps a b := by
  rw [euclideanSteps_pos_eq a b hb]; omega

theorem euclideanSteps_eq_zero_iff (a b : ℕ) :
    euclideanSteps a b = 0 ↔ b = 0 := by
  constructor
  · intro h
    by_contra hb
    have : 0 < b := Nat.pos_of_ne_zero hb
    have := euclideanSteps_ge_one a this
    omega
  · intro h; rw [h, euclideanSteps_zero]

/-- `fib (n+2) % fib (n+1) = fib n` for `n ≥ 2`. -/
theorem fib_mod_fib (n : ℕ) (hn : 2 ≤ n) :
    fib (n + 2) % fib (n + 1) = fib n := by
  have h1 : fib (n + 2) = fib n + fib (n + 1) := fib_add_two
  have h2 : fib n < fib (n + 1) := fib_lt_fib_succ hn
  rw [h1, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt h2

/-! ## The two-sided Lamé bound (strong induction)

If the algorithm takes `n` steps on `(a, b)` with `b > 0`, then
`fib (n+1) ≤ b`, and moreover `fib n ≤ a % b` once `n ≥ 2`.  This is the single
engine driving every result below. -/

/-- Core Lamé bound by strong induction on the step count. -/
theorem lame_pair_bound (n : ℕ) :
    ∀ a b, euclideanSteps a b = n → 0 < b →
    fib (n + 1) ≤ b ∧ (2 ≤ n → fib n ≤ a % b) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro a b hsteps hb
  match n with
  | 0 =>
    rw [euclideanSteps_pos_eq a b hb] at hsteps; omega
  | 1 =>
    rw [euclideanSteps_pos_eq a b hb] at hsteps
    have hr : a % b = 0 := by
      by_contra h
      have hpos : 0 < a % b := Nat.pos_of_ne_zero h
      have := euclideanSteps_ge_one b hpos; omega
    constructor
    · show fib (1 + 1) ≤ b
      have : fib (1 + 1) = 1 := by decide
      omega
    · intro h; omega
  | n + 2 =>
    rw [euclideanSteps_pos_eq a b hb] at hsteps
    set r := a % b with hr_def
    have hr_lt : r < b := Nat.mod_lt a hb
    have hsteps' : euclideanSteps b r = n + 1 := by omega
    by_cases hr0 : r = 0
    · rw [hr0, euclideanSteps_zero] at hsteps'; omega
    · have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
      have ⟨ib_r, ir⟩ := ih (n + 1) (by omega) b r hsteps' hr_pos
      constructor
      · show fib (n + 2 + 1) ≤ b
        rw [show n + 2 + 1 = (n + 1) + 2 from by omega, fib_add_two]
        have h_eq := Nat.div_add_mod b r
        have hq : 1 ≤ b / r := Nat.div_pos (by omega) hr_pos
        have hqr : r ≤ b / r * r := le_mul_of_one_le_left (Nat.zero_le r) hq
        match n with
        | 0 =>
          change fib 3 ≤ b
          have h3 : fib 3 = 2 := by decide
          have h2 : fib 2 = 1 := by decide
          have : fib 2 ≤ r := ib_r
          omega
        | n + 1 =>
          have ir' := ir (by omega)
          linarith
      · intro _
        exact ib_r

/-- **Lamé (`b`-side).** `fib (n+1) ≤ b` whenever `(a, b)` takes `n` steps and
`b > 0`. -/
theorem lame_b_lower_bound (n a b : ℕ) (hsteps : euclideanSteps a b = n)
    (hb : 0 < b) : fib (n + 1) ≤ b :=
  (lame_pair_bound n a b hsteps hb).1

/-! ## The Fibonacci pair achieves `n` steps -/

/-- Consecutive Fibonacci numbers realise the worst case:
`euclideanSteps (fib (n+2)) (fib (n+1)) = n` for `n ≥ 1`. -/
theorem euclideanSteps_fib : ∀ n : ℕ, 1 ≤ n →
    euclideanSteps (fib (n + 2)) (fib (n + 1)) = n := by
  intro n hn
  induction n with
  | zero => omega
  | succ k ih =>
    show euclideanSteps (fib (k + 3)) (fib (k + 2)) = k + 1
    cases k with
    | zero =>
      show euclideanSteps (fib 3) (fib 2) = 1
      rw [show fib 3 = 2 from by decide, show fib 2 = 1 from by decide,
          euclideanSteps_pos_eq 2 1 (by norm_num), Nat.mod_one, euclideanSteps_zero]
    | succ k =>
      have hfk2_pos : 0 < fib (k + 2 + 1) := Nat.fib_pos.mpr (by omega)
      have hmod : fib (k + 2 + 2) % fib (k + 2 + 1) = fib (k + 2) :=
        fib_mod_fib (k + 2) (by omega)
      rw [show k + 1 + 3 = k + 2 + 2 from by omega,
          show k + 1 + 2 = k + 2 + 1 from by omega]
      rw [euclideanSteps_pos_eq _ _ hfk2_pos, hmod]
      have := ih (by omega)
      rw [show k + 1 + 2 = k + 3 from by omega, show k + 1 + 1 = k + 2 from by omega] at this
      rw [show k + 2 + 1 = k + 3 from by omega]
      omega

/-! ## The `a`-side bound -/

/-- **Lamé (`a`-side).** The larger input is bounded below by `fib (n+2)`:
if `(a, b)` takes `n ≥ 1` steps with `0 < b < a`, then `fib (n+2) ≤ a`.

For `n = 1` the remainder vanishes, so `b ∣ a` with `a > b` gives `a ≥ 2b ≥ 2`.
For `n ≥ 2` the remainder bound `fib n ≤ a % b` combines with `fib (n+1) ≤ b`
through `a = b·(a/b) + a % b ≥ b + a % b`. -/
theorem steps_a_lower_bound (n a b : ℕ) (hn : 1 ≤ n)
    (hsteps : euclideanSteps a b = n) (hb : 0 < b) (hba : b < a) :
    fib (n + 2) ≤ a := by
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · have hn1 : n = 1 := by omega
    subst hn1
    have hpos : euclideanSteps a b = euclideanSteps b (a % b) + 1 :=
      euclideanSteps_pos_eq a b hb
    rw [hsteps] at hpos
    have hz : euclideanSteps b (a % b) = 0 := by omega
    have hr0 : a % b = 0 := (euclideanSteps_eq_zero_iff b (a % b)).mp hz
    have hdvd : b ∣ a := Nat.dvd_of_mod_eq_zero hr0
    obtain ⟨c, rfl⟩ := hdvd
    have hc2 : 2 ≤ c := by rcases c with _ | _ | c <;> omega
    have h3 : fib (1 + 2) = 2 := by decide
    rw [h3]
    calc (2 : ℕ) = 1 * 2 := by ring
      _ ≤ b * c := Nat.mul_le_mul (by omega) hc2
  · obtain ⟨hb_fib, hr_fib⟩ := lame_pair_bound n a b hsteps hb
    have hr : fib n ≤ a % b := hr_fib hge
    have hdm : b * (a / b) + a % b = a := Nat.div_add_mod a b
    have hq1 : 1 ≤ a / b := (Nat.one_le_div_iff hb).mpr (le_of_lt hba)
    have hge_b : b ≤ b * (a / b) := by
      have := Nat.mul_le_mul (le_refl b) hq1
      simpa using this
    have hfib2 : fib (n + 2) = fib n + fib (n + 1) := fib_add_two
    omega

/-! ## The forcing / uniqueness result -/

/-- **Uniqueness of the Euclidean worst case.** If a pair `(a, b)` with
`0 < b < a` takes `n ≥ 1` steps and attains the minimal larger input
`a = fib (n+2)`, then the smaller input is forced to `b = fib (n+1)`.

Hence the Fibonacci pair is the *unique* pair attaining the `a`-bound: no other
`b` in the window `[fib (n+1), fib (n+2))` reaches `n` steps against
`a = fib (n+2)`. -/
theorem worst_case_forces_fib (n a b : ℕ) (hn : 1 ≤ n)
    (hsteps : euclideanSteps a b = n) (hb : 0 < b) (hba : b < a)
    (ha : a = fib (n + 2)) : b = fib (n + 1) := by
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · have hn1 : n = 1 := by omega
    subst hn1
    have h3 : fib (1 + 2) = 2 := by decide
    have h2 : fib (1 + 1) = 1 := by decide
    rw [ha, h3] at hba
    rw [h2]; omega
  · obtain ⟨hb_fib, hr_fib⟩ := lame_pair_bound n a b hsteps hb
    have hr : fib n ≤ a % b := hr_fib hge
    have hlt' : fib n < fib (n + 1) := fib_lt_fib_succ hge
    have hfib2 : fib (n + 2) = fib n + fib (n + 1) := fib_add_two
    have hle : b ≤ a := le_of_lt hba
    have hlt2b : a < 2 * b := by omega
    have hmod : a % b = a - b := by
      rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt (by omega)]
    omega

/-- **The unique extremal pair.** Under the hypotheses of
`worst_case_forces_fib`, the pair is exactly `(fib (n+2), fib (n+1))`. -/
theorem worst_case_pair_unique (n a b : ℕ) (hn : 1 ≤ n)
    (hsteps : euclideanSteps a b = n) (hb : 0 < b) (hba : b < a)
    (ha : a = fib (n + 2)) : a = fib (n + 2) ∧ b = fib (n + 1) :=
  ⟨ha, worst_case_forces_fib n a b hn hsteps hb hba ha⟩

/-- **Full characterisation.** For `n ≥ 1`, the pairs `(a, b)` with `0 < b < a`
taking `n` steps and attaining `a = fib (n+2)` are *precisely* the single
Fibonacci pair `(fib (n+2), fib (n+1))`. -/
theorem worst_case_iff (n a b : ℕ) (hn : 1 ≤ n) :
    (euclideanSteps a b = n ∧ 0 < b ∧ b < a ∧ a = fib (n + 2)) ↔
      (a = fib (n + 2) ∧ b = fib (n + 1)) := by
  constructor
  · rintro ⟨hs, hb, hba, ha⟩
    exact ⟨ha, worst_case_forces_fib n a b hn hs hb hba ha⟩
  · rintro ⟨ha, hbf⟩
    subst ha; subst hbf
    refine ⟨euclideanSteps_fib n hn, Nat.fib_pos.mpr (by omega), ?_, rfl⟩
    exact fib_lt_fib_succ (show 2 ≤ n + 1 by omega)

/-! ## Size bound -/

/-- **Sum lower bound.** Any pair taking `n ≥ 1` steps with `0 < b < a` has
`a + b ≥ fib (n+3)`, with equality for the Fibonacci pair
(`fib (n+2) + fib (n+1) = fib (n+3)`). -/
theorem steps_sum_lower_bound (n a b : ℕ) (hn : 1 ≤ n)
    (hsteps : euclideanSteps a b = n) (hb : 0 < b) (hba : b < a) :
    fib (n + 3) ≤ a + b := by
  have ha := steps_a_lower_bound n a b hn hsteps hb hba
  have hbf := lame_b_lower_bound n a b hsteps hb
  have hsum : fib (n + 3) = fib (n + 1) + fib (n + 2) := fib_add_two
  omega

/-! ## Numerical sanity checks (Fibonacci values are `decide`-reducible) -/

/-- The `n = 4` worst pair is `(fib 6, fib 5) = (8, 5)`. -/
theorem worst_pair_four : fib (4 + 2) = 8 ∧ fib (4 + 1) = 5 := by decide

/-- `fib (n+2) + fib (n+1) = fib (n+3)` at `n = 4`: `8 + 5 = 13 = fib 7`. -/
theorem sum_seven : fib (4 + 2) + fib (4 + 1) = fib (4 + 3) := by decide

#print axioms steps_a_lower_bound
#print axioms worst_case_forces_fib
#print axioms worst_case_iff
#print axioms steps_sum_lower_bound
#print axioms euclideanSteps_fib

end GCDAlgorithmOQ01OQ05
