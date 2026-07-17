import Mathlib

/-!
# Collatz OQ-02-03 — Part XIII: Constant-term bound & the uniform *eventual*-drop theorem (self-contained)

The residue-drop engine in the mother module `Proofs.CollatzStructuredOQ02OQ03` certifies a
residue class `n ≡ r (mod M)` by an affine parity certificate `AffValid v c d`, whose realized
`v.length`-step iterate is `collatz^[v.length] (c·m + d) = A·m + D` with
`(A, D) = affOrbit v (c, d)` (`affOrbit_realize`).  Its drop-below corollaries
(`affine_residue_attainsBelow`, `parityVector_attainsBelow`) all require **two** conditions:

* `A < c` — the Terras leading-coefficient criterion, i.e. `3^a < 2^b` for a power-of-two window
  (enough halvings to beat the triplings); and
* `D < r` — a hand-checked bound on the **constant term**, needed to force the drop at the
  boundary member `m = 0`.

The second condition is *not* structural: many determined-drop classes have `D ≥ r` (their `m = 0`
representative does not itself drop within the window), yet every *large* member of the class still
drops, because the leading term `(c − A)·m` eventually swamps the constant.  Nothing in the mother
module captures this — the constant term `D` of a certified window was never bounded.

This file settles it.  The key new fact is a clean, uniform bound on the constant term:

* `affOrbit_snd_bound` — `D + 1 ≤ 3 ^ (#odd steps) · (d + 1)`.  The constant fold `d ↦ 3d+1`
  (odd) / `d ↦ ⌊d/2⌋` (even) never grows past `3^a·(d+1)`.  A short structural induction; the
  even step *shrinks* `d`, the odd step multiplies by `3` and the `+1` is absorbed by the `(d+1)`
  slack.
* `affOrbit_snd_mono` — the constant fold is monotone in `d` (same certificate, same bit sequence).
* `affine_value_lt` / `affine_value_lt_of_threshold` — the affine drop: once `A < c`, the value
  `A·m + D` falls below `c·m + d` for every `m` past the explicit threshold
  `3^a·(d+1) ≤ (c − A)·m`; the constant bound turns "for large `m`" into a *closed-form* threshold.
* `affValid_attainsBelow_of_large` — the Collatz payoff: **every** class member `c·m + d` with
  `A < c` and `m` past the threshold satisfies `AttainsBelow`.  No `D < r` side condition — this
  covers exactly the determined-drop classes the mother's corollaries could not reach.
* `affValid_attainsBelow_of_large_pow` — the headline in classical `3^a < 2^b` form for a
  power-of-two window (`c = 2 ^ #even`).

So the mother's engine drops the *whole* class only when the boundary member cooperates (`D < r`);
this file shows the determined-drop criterion `A < c` alone forces the drop for **cofinitely many**
members of every class, with an explicit threshold — the honest structural content of "3^a < 2^b
⇒ drops below" without the boundary caveat.

Self-contained: `collatz`, the affine machinery (`leadCoeff`, `affStep`, `affOrbit`, `AffValid`,
`affOrbit_realize`), and `AttainsBelow` are re-declared here exactly as in the mother module
(which sits at the Lean kernel-memory ceiling and is expensive/fragile to rebuild), so these
theorems stand on their own with only `import Mathlib`.  Axiom-free; nothing here uses `decide`.

Reference: Terras (1976) parity vectors / stopping time; the residue-determined-window coding of
the Collatz map.
-/

namespace CollatzStructuredOQ02OQ03ConstBound

/-! ## Re-declared machinery (verbatim from the mother module) -/

/-- The Collatz step: halve if even, `3n+1` if odd. -/
def collatz (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

theorem collatz_even {n : ℕ} (h : n % 2 = 0) : collatz n = n / 2 := by
  simp [collatz, h]

theorem collatz_odd {n : ℕ} (h : n % 2 = 1) : collatz n = 3 * n + 1 := by
  unfold collatz
  rw [if_neg (by omega)]

/-- `n` attains a value strictly below itself in a positive number of steps
(the finite-stopping-time event). -/
def AttainsBelow (n : ℕ) : Prop := ∃ k, 0 < k ∧ collatz^[k] n < n

/-- The leading-coefficient fold: an odd step triples, an even step halves. -/
def leadCoeff : List Bool → ℕ → ℕ
  | [],          c => c
  | true  :: v,  c => leadCoeff v (3 * c)
  | false :: v,  c => leadCoeff v (c / 2)

/-- **Terras leading-coefficient law (general multiplicative form).** -/
theorem leadCoeff_mul (v : List Bool) :
    ∀ p q : ℕ, v.count false ≤ q →
      leadCoeff v (3 ^ p * 2 ^ q)
        = 3 ^ (p + v.count true) * 2 ^ (q - v.count false) := by
  induction v with
  | nil => intro p q _; simp [leadCoeff]
  | cons b v ih =>
    intro p q hq
    cases b with
    | true =>
      have cf : (true :: v).count false = v.count false := by simp
      have ct : (true :: v).count true = v.count true + 1 := by simp
      rw [cf] at hq
      show leadCoeff v (3 * (3 ^ p * 2 ^ q))
          = 3 ^ (p + (true :: v).count true) * 2 ^ (q - (true :: v).count false)
      rw [show 3 * (3 ^ p * 2 ^ q) = 3 ^ (p + 1) * 2 ^ q from by rw [pow_succ]; ring,
          ih (p + 1) q hq, cf, ct,
          show p + 1 + v.count true = p + (v.count true + 1) from by omega]
    | false =>
      have cf : (false :: v).count false = v.count false + 1 := by simp
      have ct : (false :: v).count true = v.count true := by simp
      rw [cf] at hq
      have h2 : 3 ^ p * 2 ^ q / 2 = 3 ^ p * 2 ^ (q - 1) := by
        have e : 2 ^ q = 2 ^ (q - 1) * 2 := by
          conv_lhs => rw [show q = (q - 1) + 1 from by omega]
          rw [pow_succ]
        rw [e, ← mul_assoc, Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
      show leadCoeff v (3 ^ p * 2 ^ q / 2)
          = 3 ^ (p + (false :: v).count true) * 2 ^ (q - (false :: v).count false)
      rw [h2, ih p (q - 1) (by omega), cf, ct,
          show q - 1 - v.count false = q - (v.count false + 1) from by omega]

/-- Power-of-two specialization: a window whose halvings match the modulus exponent ends with
leading coefficient `3 ^ (#odd steps)`. -/
theorem leadCoeff_two_pow (v : List Bool) :
    leadCoeff v (2 ^ v.count false) = 3 ^ v.count true := by
  have := leadCoeff_mul v 0 (v.count false) (le_refl _)
  simpa using this

/-- One affine step on `(c, d)` driven by a parity bit. -/
def affStep : Bool → ℕ × ℕ → ℕ × ℕ
  | true,  p => (3 * p.1, 3 * p.2 + 1)
  | false, p => (p.1 / 2, p.2 / 2)

/-- Fold the affine coefficient pair along a parity vector. -/
def affOrbit : List Bool → ℕ × ℕ → ℕ × ℕ
  | [],     p => p
  | b :: v, p => affOrbit v (affStep b p)

/-- The leading coefficient of the affine orbit is `leadCoeff` — independent of the constant. -/
theorem affOrbit_fst (v : List Bool) :
    ∀ c d : ℕ, (affOrbit v (c, d)).1 = leadCoeff v c := by
  induction v with
  | nil => intro c d; rfl
  | cons b v ih =>
    intro c d
    cases b with
    | true => exact ih (3 * c) (3 * d + 1)
    | false => exact ih (c / 2) (d / 2)

/-- A parity vector is *valid* for the affine class `c·m + d` when each recorded parity matches
the forced value parity along the orbit (independent of `m`). -/
inductive AffValid : List Bool → ℕ → ℕ → Prop
  | nil  {c d} : AffValid [] c d
  | odd  {v c d} : c % 2 = 0 → d % 2 = 1 → AffValid v (3 * c) (3 * d + 1) →
      AffValid (true :: v) c d
  | even {v c d} : c % 2 = 0 → d % 2 = 0 → AffValid v (c / 2) (d / 2) →
      AffValid (false :: v) c d

/-- **General orbit-realization.**  A valid certificate `v` for `c·m + d` makes the
`v.length`-step Collatz iterate the affine value read off `affOrbit`. -/
theorem affOrbit_realize : ∀ {v : List Bool} {c d : ℕ}, AffValid v c d →
    ∀ m : ℕ, collatz^[v.length] (c * m + d)
      = (affOrbit v (c, d)).1 * m + (affOrbit v (c, d)).2 := by
  intro v c d hv
  induction hv with
  | nil => intro m; rfl
  | @odd v c d hc hd _ ih =>
    obtain ⟨c', rfl⟩ : ∃ c', c = 2 * c' := ⟨c / 2, by omega⟩
    intro m
    have hcm : 2 * c' * m = 2 * (c' * m) := by ring
    have hodd : (2 * c' * m + d) % 2 = 1 := by omega
    have hstep : collatz (2 * c' * m + d) = (3 * (2 * c')) * m + (3 * d + 1) := by
      rw [collatz_odd hodd]; ring
    show collatz^[v.length + 1] (2 * c' * m + d) = _
    rw [Function.iterate_succ_apply, hstep]
    exact ih m
  | @even v c d hc hd _ ih =>
    obtain ⟨c', rfl⟩ : ∃ c', c = 2 * c' := ⟨c / 2, by omega⟩
    obtain ⟨d', rfl⟩ : ∃ d', d = 2 * d' := ⟨d / 2, by omega⟩
    intro m
    have hcm : 2 * c' * m = 2 * (c' * m) := by ring
    have hstep : collatz (2 * c' * m + 2 * d') = c' * m + d' := by
      have he : (2 * c' * m + 2 * d') % 2 = 0 := by omega
      rw [collatz_even he]; omega
    show collatz^[v.length + 1] (2 * c' * m + 2 * d') = _
    rw [Function.iterate_succ_apply, hstep]
    have e1 : (2 * c') / 2 = c' := by omega
    have e2 : (2 * d') / 2 = d' := by omega
    have key := ih m
    rw [e1, e2] at key
    show collatz^[v.length] (c' * m + d')
        = (affOrbit v ((2 * c') / 2, (2 * d') / 2)).1 * m
          + (affOrbit v ((2 * c') / 2, (2 * d') / 2)).2
    rw [e1, e2]
    exact key

/-! ## Part XIII: the constant-term bound and the uniform eventual-drop theorem (new) -/

/-- **Constant-term bound.**  The constant term `D = (affOrbit v (c, d)).2` of any window never
exceeds `3 ^ (#odd steps) · (d + 1)`: the odd fold `d ↦ 3d+1` multiplies by three (the `+1`
absorbed by the `(d+1)` slack), the even fold `d ↦ ⌊d/2⌋` only shrinks.  This is the missing
control on the constant that lets the leading-coefficient criterion `A < c` force a drop by itself.
Structural induction on `v`, generalized over both coordinates. -/
theorem affOrbit_snd_bound (v : List Bool) :
    ∀ c d : ℕ, (affOrbit v (c, d)).2 + 1 ≤ 3 ^ v.count true * (d + 1) := by
  induction v with
  | nil => intro c d; simp [affOrbit]
  | cons b v ih =>
    intro c d
    cases b with
    | true =>
      have hc : (true :: v).count true = v.count true + 1 := by simp
      show (affOrbit v (3 * c, 3 * d + 1)).2 + 1 ≤ 3 ^ (true :: v).count true * (d + 1)
      calc (affOrbit v (3 * c, 3 * d + 1)).2 + 1
            ≤ 3 ^ v.count true * (3 * d + 1 + 1) := ih (3 * c) (3 * d + 1)
        _ ≤ 3 ^ v.count true * (3 * (d + 1)) := by gcongr; omega
        _ = 3 ^ (true :: v).count true * (d + 1) := by rw [hc, pow_succ]; ring
    | false =>
      have hc : (false :: v).count true = v.count true := by simp
      show (affOrbit v (c / 2, d / 2)).2 + 1 ≤ 3 ^ (false :: v).count true * (d + 1)
      rw [hc]
      calc (affOrbit v (c / 2, d / 2)).2 + 1
            ≤ 3 ^ v.count true * (d / 2 + 1) := ih (c / 2) (d / 2)
        _ ≤ 3 ^ v.count true * (d + 1) := by gcongr; omega

/-- **Monotonicity of the constant fold.**  Along a fixed parity certificate, the constant term of
the affine orbit is monotone in the starting constant `d` (the leading coefficient is unaffected,
`affOrbit_fst`).  A companion to the bound: the two together sandwich the constant term. -/
theorem affOrbit_snd_mono (v : List Bool) :
    ∀ c d₁ d₂ : ℕ, d₁ ≤ d₂ → (affOrbit v (c, d₁)).2 ≤ (affOrbit v (c, d₂)).2 := by
  induction v with
  | nil => intro c d₁ d₂ h; simpa [affOrbit] using h
  | cons b v ih =>
    intro c d₁ d₂ h
    cases b with
    | true =>
      show (affOrbit v (3 * c, 3 * d₁ + 1)).2 ≤ (affOrbit v (3 * c, 3 * d₂ + 1)).2
      exact ih (3 * c) (3 * d₁ + 1) (3 * d₂ + 1) (by omega)
    | false =>
      show (affOrbit v (c / 2, d₁ / 2)).2 ≤ (affOrbit v (c / 2, d₂ / 2)).2
      exact ih (c / 2) (d₁ / 2) (d₂ / 2) (Nat.div_le_div_right h)

/-- **Affine drop (raw form).**  If the leading coefficient `A` is below the modulus `c` and the
constant term `D` is below `(c − A)·m`, then the affine value `A·m + D` falls below `c·m + d`
(the `+d` on the right only helps).  This is the drop condition stripped to its arithmetic core. -/
theorem affine_value_lt {v : List Bool} {c d m : ℕ}
    (hlt : (affOrbit v (c, d)).1 < c)
    (hm : (affOrbit v (c, d)).2 < (c - (affOrbit v (c, d)).1) * m) :
    (affOrbit v (c, d)).1 * m + (affOrbit v (c, d)).2 < c * m + d := by
  set A := (affOrbit v (c, d)).1 with hA
  set D := (affOrbit v (c, d)).2 with hD
  have key : A * m + (c - A) * m = c * m := by
    rw [← add_mul]; congr 1; omega
  omega

/-- **Affine drop (closed-form threshold).**  The constant bound turns the hypothesis of
`affine_value_lt` into the explicit threshold `3 ^ (#odd steps) · (d + 1) ≤ (c − A)·m`: once the
leading criterion `A < c` holds, every `m` past this threshold makes the window drop. -/
theorem affine_value_lt_of_threshold {v : List Bool} {c d m : ℕ}
    (hlt : (affOrbit v (c, d)).1 < c)
    (hm : 3 ^ v.count true * (d + 1) ≤ (c - (affOrbit v (c, d)).1) * m) :
    (affOrbit v (c, d)).1 * m + (affOrbit v (c, d)).2 < c * m + d := by
  apply affine_value_lt hlt
  have hb := affOrbit_snd_bound v c d
  omega

/-- **Uniform eventual drop (Collatz payoff).**  For a non-empty valid certificate `v` of the
class `c·m + d` whose leading coefficient is below the modulus (`A < c`), *every* class member
`c·m + d` with `m` past the explicit threshold `3 ^ (#odd) · (d + 1) ≤ (c − A)·m` attains a value
below itself.  Unlike `affine_residue_attainsBelow` / `parityVector_attainsBelow`, there is **no**
`D < r` side condition: the determined-drop criterion `A < c` alone forces the drop for cofinitely
many members of the class. -/
theorem affValid_attainsBelow_of_large {v : List Bool} {c d : ℕ}
    (hv : AffValid v c d) (hlen : 0 < v.length)
    (hlt : (affOrbit v (c, d)).1 < c)
    {m : ℕ} (hm : 3 ^ v.count true * (d + 1) ≤ (c - (affOrbit v (c, d)).1) * m) :
    AttainsBelow (c * m + d) := by
  refine ⟨v.length, hlen, ?_⟩
  rw [affOrbit_realize hv m]
  exact affine_value_lt_of_threshold hlt hm

/-- **Uniform eventual drop, classical `3^a < 2^b` form.**  For a residue-determined power-of-two
window (`c = 2 ^ (#even steps)`), the leading criterion is the classical `3^a < 2^b`, and every
class member `2^b·m + d` with `m ≥ 3^a·(d+1)/(2^b − 3^a)` drops below itself.  This is the honest,
boundary-caveat-free reading of "enough halvings to beat the triplings ⇒ the class drops". -/
theorem affValid_attainsBelow_of_large_pow {v : List Bool} {d : ℕ}
    (hv : AffValid v (2 ^ v.count false) d) (hlen : 0 < v.length)
    (hlt : 3 ^ v.count true < 2 ^ v.count false)
    {m : ℕ}
    (hm : 3 ^ v.count true * (d + 1) ≤ (2 ^ v.count false - 3 ^ v.count true) * m) :
    AttainsBelow (2 ^ v.count false * m + d) := by
  have hfst : (affOrbit v (2 ^ v.count false, d)).1 = 3 ^ v.count true := by
    rw [affOrbit_fst]; exact leadCoeff_two_pow v
  refine affValid_attainsBelow_of_large hv hlen ?_ ?_
  · rw [hfst]; exact hlt
  · rw [hfst]; exact hm

end CollatzStructuredOQ02OQ03ConstBound
