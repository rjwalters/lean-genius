import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-
# Complexity of the Extended Euclidean Algorithm (Lamé's Theorem)

## Open Question Origin

From bezout-identity-oq-02-oq-02-oq-01 (Constructive Divisibility Algorithm via
Bézout Coefficients), open question 3:

"Can the complexity bound O(log min(a,b)) for extGcd be formalized in Lean?"

## Answer: YES

The extended Euclidean algorithm `extGcd` of the parent entry recurses via
`(a, b+1) ↦ (b+1, a % (b+1))`. We count its division steps with `steps a b`
and prove the two sides of the Θ(log) characterization:

* **Upper bound (Lamé, the O part):** `steps a b ≤ 2 * Nat.log 2 b + 2`.
  The proof rests on the fact that the remainder *more than halves every two
  steps*: if `0 < b ≤ a` then `2 * (a % b) < a`. Hence after two recursive
  calls the controlling argument has dropped below half its value, giving at
  most `2 ⌊log₂ b⌋ + 2` steps.

* **Worst case (the Ω part):** consecutive Fibonacci numbers achieve exactly
  `n` steps: `steps (fib (n+2)) (fib (n+1)) = n`. Since `fib (n+1) ≍ φⁿ`, this
  family forces a step count growing like `log_φ b ≈ 1.44 · log₂ b`, so the
  logarithmic upper bound is tight up to a constant. This is Gabriel Lamé's
  1844 theorem — historically the first complexity bound proved for any
  algorithm.

`steps` mirrors `extGcd`'s recursion exactly, so the step count proved here is
the number of recursive calls (and hence of integer divisions) `extGcd`
performs. Zero axioms, zero sorries.
-/

namespace BezoutIdentityOQ02OQ02OQ01OQ03

/-
## Part I: Step counter for the (extended) Euclidean algorithm
-/

/-- Number of division steps performed by the extended Euclidean algorithm
    `extGcd` on input `(a, b)`. The recursion `(a, b+1) ↦ (b+1, a % (b+1))`
    is identical to that of `extGcd` in the parent entry, so this counts the
    number of recursive calls `extGcd a b` makes. -/
def steps : ℕ → ℕ → ℕ
  | _, 0 => 0
  | a, b + 1 =>
    have : a % (b + 1) < b + 1 := Nat.mod_lt a (Nat.succ_pos b)
    steps (b + 1) (a % (b + 1)) + 1

@[simp] theorem steps_zero (a : ℕ) : steps a 0 = 0 := by simp [steps]

theorem steps_succ (a b : ℕ) :
    steps a (b + 1) = steps (b + 1) (a % (b + 1)) + 1 := by
  simp [steps]

/-- One-step unfolding for any positive second argument. -/
theorem steps_pos (a b : ℕ) (hb : 0 < b) :
    steps a b = steps b (a % b) + 1 := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  exact steps_succ a c

/-
## Part II: The halving lemma

Each Euclidean step at least follows `a = q·b + r` with `q ≥ 1` (when `b ≤ a`),
which forces the remainder strictly below half of `a`.
-/

/-- **The remainder more than halves.** If `0 < b ≤ a` then `2 * (a % b) < a`.
    Either `b ≤ a/2`, so `a % b < b ≤ a/2`; or `a/2 < b ≤ a`, so the quotient
    is `1` and `a % b = a - b < a/2`. -/
theorem two_mul_mod_lt {a b : ℕ} (hb : 0 < b) (hab : b ≤ a) : 2 * (a % b) < a := by
  rcases le_or_gt (2 * b) a with h | h
  · have hlt : a % b < b := Nat.mod_lt a hb
    omega
  · have hmod : a % b = a - b := by
      rw [Nat.mod_eq_sub_mod hab, Nat.mod_eq_of_lt (by omega)]
    omega

/-
## Part III: The logarithmic upper bound (Lamé's theorem, O direction)
-/

/-- **Lamé's upper bound.** The Euclidean algorithm on `(a, b)` with `b > 0`
    performs at most `2 ⌊log₂ b⌋ + 2` division steps — i.e. `O(log b)`. The
    proof is strong induction on `b`: after two recursive calls the controlling
    argument `r''` satisfies `2 * r'' < b`, so `⌊log₂ r''⌋ + 1 ≤ ⌊log₂ b⌋`. -/
theorem steps_le_log :
    ∀ b, 0 < b → ∀ a, steps a b ≤ 2 * Nat.log 2 b + 2 := by
  intro b
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro hb a
    rw [steps_pos _ _ hb]
    have hrb : a % b < b := Nat.mod_lt a hb
    rcases Nat.eq_zero_or_pos (a % b) with hr0 | hr0
    · -- one step: a % b = 0
      rw [hr0, steps_zero]; omega
    · rw [steps_pos _ _ hr0]
      have hsr : 2 * (b % (a % b)) < b := two_mul_mod_lt hr0 (le_of_lt hrb)
      rcases Nat.eq_zero_or_pos (b % (a % b)) with hs0 | hs0
      · -- two steps: b % (a % b) = 0
        rw [hs0, steps_zero]; omega
      · -- general: the controlling argument has more than halved
        have hsb : b % (a % b) < b := by omega
        have hih := ih (b % (a % b)) hsb hs0 (a % b)
        have hlog : Nat.log 2 (b % (a % b)) + 1 ≤ Nat.log 2 b := by
          have e : Nat.log 2 (b % (a % b) * 2) = Nat.log 2 (b % (a % b)) + 1 :=
            Nat.log_mul_base (by norm_num) (by omega)
          have hmono : Nat.log 2 (b % (a % b) * 2) ≤ Nat.log 2 b :=
            Nat.log_mono_right (by omega)
          omega
        omega

/-- The same bound stated for the smaller of the two inputs: when `b ≤ a` the
    second argument is `min a b`, so the algorithm runs in `O(log min(a,b))`. -/
theorem steps_le_log_min (a b : ℕ) (hb : 0 < b) (hab : b ≤ a) :
    steps a b ≤ 2 * Nat.log 2 (min a b) + 2 := by
  rw [Nat.min_eq_right hab]
  exact steps_le_log b hb a

/-
## Part IV: The Fibonacci worst case (Lamé's theorem, Ω direction)
-/

/-- **Consecutive Fibonacci numbers are the worst case.** The Euclidean
    algorithm on `(fib (n+2), fib (n+1))` takes exactly `n` steps, because each
    step reduces a Fibonacci pair to the previous one:
    `fib (n+3) % fib (n+2) = fib (n+1)`. Since `fib (n+1)` grows like `φⁿ`, this
    family attains the logarithmic upper bound up to a constant factor. -/
theorem steps_fib : ∀ n, 1 ≤ n → steps (Nat.fib (n + 2)) (Nat.fib (n + 1)) = n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    show steps (Nat.fib 3) (Nat.fib 2) = 1
    have hb : 0 < Nat.fib 2 := Nat.fib_pos.mpr (by norm_num)
    rw [steps_pos _ _ hb, show Nat.fib 3 % Nat.fib 2 = 0 from by decide, steps_zero]
  | succ n hn ih =>
    show steps (Nat.fib (n + 3)) (Nat.fib (n + 2)) = n + 1
    have hb : 0 < Nat.fib (n + 2) := Nat.fib_pos.mpr (by omega)
    rw [steps_pos _ _ hb]
    have key : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := by
      have h : n + 3 = n + 1 + 2 := by omega
      rw [h, Nat.fib_add_two]
    have hlt : Nat.fib (n + 1) < Nat.fib (n + 2) := by
      have hpos : 0 < Nat.fib n := Nat.fib_pos.mpr (by omega)
      have h2 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
      omega
    rw [key, Nat.add_mod_right, Nat.mod_eq_of_lt hlt, ih]

/-
## Part V: Tightness of Lamé's bound (the Θ characterization)

Parts III and IV give the two halves of a complexity result but do not yet
*meet*: Part III bounds every input from above by `2 log₂ b + 2`, and Part IV
exhibits a family attaining `n` steps. To conclude the bound is genuinely
`Θ(log b)` — and in particular cannot be improved to `o(log b)` — we need a
matching *lower* bound on the worst case in terms of `log₂ b`. The missing
ingredient is that Fibonacci numbers grow no faster than powers of two, so
`log₂ (fib (n+1)) ≤ n`; combined with `steps_fib` this lower-bounds the step
count by `log₂ b`.
-/

/-- `fib (n+1) ≤ 2 ^ n`: Fibonacci numbers grow no faster than powers of two.
    A two-step induction (`fib (n+3) = fib (n+1) + fib (n+2) ≤ 2ⁿ + 2ⁿ⁺¹ ≤
    2ⁿ⁺²`). This is what converts the Fibonacci worst case into a logarithmic
    lower bound on the step count. -/
theorem fib_succ_le_two_pow : ∀ n, Nat.fib (n + 1) ≤ 2 ^ n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih1 ih2 =>
    -- bridge `ih2`'s `fib (n+1+1)` to the `fib (n+2)` shape omega sees in the goal
    have ih2' : Nat.fib (n + 2) ≤ 2 ^ (n + 1) := ih2
    have hfib : Nat.fib (n + 1 + 2) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
    have hstep : (2 : ℕ) ^ n ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpow : (2 : ℕ) ^ (n + 2) = 2 ^ (n + 1) + 2 ^ (n + 1) := by rw [pow_succ]; ring
    rw [show n + 2 + 1 = n + 1 + 2 from by omega, hfib]
    omega

/-- **Lamé's bound is tight: the lower half of the Θ(log) characterization.**
    On the Fibonacci worst case `(fib (n+2), fib (n+1))` the step count is at
    least `⌊log₂ b⌋` where `b = fib (n+1)` is the controlling input. Together
    with `steps_le_log` (the `O` direction) this shows the Euclidean algorithm
    runs in `Θ(log b)` steps and the logarithmic upper bound cannot be improved
    to `o(log b)`. -/
theorem log_le_steps_fib (n : ℕ) (hn : 1 ≤ n) :
    Nat.log 2 (Nat.fib (n + 1)) ≤ steps (Nat.fib (n + 2)) (Nat.fib (n + 1)) := by
  rw [steps_fib n hn]
  calc Nat.log 2 (Nat.fib (n + 1))
      ≤ Nat.log 2 (2 ^ n) := Nat.log_mono_right (fib_succ_le_two_pow n)
    _ = n := Nat.log_pow (by norm_num) n

/-- **The two-sided sandwich.** For the Fibonacci worst case the step count is
    pinned between `⌊log₂ b⌋` and `2⌊log₂ b⌋ + 2`, with `b = fib (n+1)`. This is
    the precise sense in which the extended Euclidean algorithm is `Θ(log b)`. -/
theorem steps_fib_theta (n : ℕ) (hn : 1 ≤ n) :
    Nat.log 2 (Nat.fib (n + 1)) ≤ steps (Nat.fib (n + 2)) (Nat.fib (n + 1)) ∧
      steps (Nat.fib (n + 2)) (Nat.fib (n + 1)) ≤ 2 * Nat.log 2 (Nat.fib (n + 1)) + 2 :=
  ⟨log_le_steps_fib n hn,
    steps_le_log (Nat.fib (n + 1)) (Nat.fib_pos.mpr (by omega)) (Nat.fib (n + 2))⟩

/-
## Part VI: The sharp Lamé bound — Fibonacci inputs are the smallest

Parts III–V pin the step count to `Θ(log b)` but only *up to the constant 2*:
the upper bound is `2⌊log₂ b⌋ + 2`, while the Fibonacci family forces about
`log_φ b ≈ 1.44 log₂ b`. The classical *sharp* form of Lamé's theorem closes
this gap from the input side. If the algorithm takes `steps a b = n` divisions
and `b > 0`, then `b ≥ fib (n+1)`: consecutive Fibonacci numbers are the
**smallest inputs requiring a given number of steps**. `steps_fib` exhibits the
attaining family (`b = fib (n+1)`, `a = fib (n+2)`); the bound below shows
nothing smaller can reach `n` steps.

The proof is a genuine two-step descent. One Euclidean step sends `(a, b)` to
`(b, r)` with `r = a % b`; a second sends it to `(r, s)` with `s = b % r`. The
quotient `b / r ≥ 1` forces `r + s ≤ b`, exactly mirroring the Fibonacci
recurrence `fib (j+3) = fib (j+2) + fib (j+1)` that drives the worst case.
-/

/-- **Lamé's theorem, sharp form (input lower bound).** Whenever `b > 0`, the
    Euclidean step count satisfies `fib (steps a b + 1) ≤ b`. Hence consecutive
    Fibonacci numbers are the *smallest* inputs attaining a given step count
    (`steps_fib` realizes equality with `b = fib (n+1)`). This is strictly
    sharper than `steps_le_log`: it is the exact characterization of the worst
    case rather than a bound up to the factor-of-2 slack in `2⌊log₂ b⌋ + 2`. -/
theorem fib_succ_le : ∀ b, 0 < b → ∀ a, Nat.fib (steps a b + 1) ≤ b := by
  intro b
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro hb a
    rw [steps_pos _ _ hb]
    set r := a % b with hr_def
    have hrb : r < b := Nat.mod_lt a hb
    rcases Nat.eq_zero_or_pos r with hr0 | hr0
    · -- one step: `r = 0`, so `steps a b = 1` and `fib 2 = 1 ≤ b`
      rw [hr0, steps_zero]
      simpa using hb
    · -- `r > 0`: descend a second step to `(r, s)` with `s = b % r`
      have hk : steps b r = steps r (b % r) + 1 := steps_pos b r hr0
      set s := b % r with hs_def
      have hsr : s < r := Nat.mod_lt b hr0
      -- `r + s ≤ b`, the arithmetic shadow of `fib (j+3) = fib (j+2) + fib (j+1)`
      have hsum : r + s ≤ b := by
        have hdm : r * (b / r) + s = b := by
          have h := Nat.div_add_mod b r
          rwa [← hs_def] at h
        have hq : 1 ≤ b / r := (Nat.one_le_div_iff hr0).mpr (le_of_lt hrb)
        have hge : r * 1 ≤ r * (b / r) := Nat.mul_le_mul_left r hq
        rw [Nat.mul_one] at hge
        omega
      rcases Nat.eq_zero_or_pos s with hs0 | hs0
      · -- two steps: `s = 0`, so `steps a b = 2` and `fib 3 = 2 ≤ b`
        rw [hk, hs0, steps_zero]
        have hb2 : 2 ≤ b := by omega
        calc Nat.fib (0 + 1 + 1 + 1) = 2 := by decide
          _ ≤ b := hb2
      · -- general case: `fib (k+2) = fib k + fib (k+1) ≤ s + r ≤ b`
        have hA : Nat.fib (steps b r + 1) ≤ r := ih r hrb hr0 b
        have hB : Nat.fib (steps r s + 1) ≤ s := ih s (lt_trans hsr hrb) hs0 r
        have hBk : Nat.fib (steps b r) ≤ s := by rw [hk]; exact hB
        have hfib : Nat.fib (steps b r + 1 + 1)
            = Nat.fib (steps b r) + Nat.fib (steps b r + 1) := Nat.fib_add_two
        omega

/-- **Contrapositive: small inputs cannot force many steps.** If `b < fib (n+1)`
    then the Euclidean algorithm on `(a, b)` finishes in fewer than `n` steps.
    Equivalently, reaching `n` steps *requires* `b ≥ fib (n+1)`. -/
theorem steps_lt_of_lt_fib (a b n : ℕ) (hb : 0 < b) (h : b < Nat.fib (n + 1)) :
    steps a b < n := by
  by_contra hcon
  push_neg at hcon
  have hmono : Nat.fib (n + 1) ≤ Nat.fib (steps a b + 1) :=
    Nat.fib_mono (by omega)
  have hle := fib_succ_le b hb a
  omega

/-- **Fibonacci numbers are the exact minimal inputs (the sharp Lamé theorem).**
    For `n ≥ 1`, `fib (n+1)` is the smallest positive second argument for which
    some first argument makes the extended Euclidean algorithm take exactly `n`
    division steps: it is *attained* by `(fib (n+2), fib (n+1))` (`steps_fib`),
    and no smaller `b > 0` admits any `a` reaching `n` steps (`fib_succ_le`).
    This upgrades the Θ(log) characterization to an exact worst-case identity. -/
theorem fib_isLeast_input (n : ℕ) (hn : 1 ≤ n) :
    steps (Nat.fib (n + 2)) (Nat.fib (n + 1)) = n ∧
      ∀ a b, 0 < b → steps a b = n → Nat.fib (n + 1) ≤ b := by
  refine ⟨steps_fib n hn, fun a b hb hstep => ?_⟩
  have hle := fib_succ_le b hb a
  rw [hstep] at hle
  exact hle

end BezoutIdentityOQ02OQ02OQ01OQ03
