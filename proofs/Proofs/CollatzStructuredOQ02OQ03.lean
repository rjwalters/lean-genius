/-
# OQ-02 OQ-03: Tao's 2019 Almost-All Bound — A Feasibility Anchor

Open question OQ-03 of `collatz-structured-oq-02` (Collatz Cycles):

  "Can Tao's 2019 almost-all result (logarithmic density 1) be formalized in Lean
   using Mathlib's measure theory and ergodic theory libraries?"

Tao (2019, *Forum Math. Pi*, "Almost all orbits of the Collatz map attain almost
bounded values") proved: for every `f : ℕ → ℝ` with `f n → ∞`, the set of starting
values `n` whose orbit minimum `Col_min(n)` drops below `f n` has **logarithmic
density 1**.  This subsumes the classical Terras/Korec "almost all have finite
stopping time" statements and pushes the bound from "below `n`" down to "below any
slowly growing `f`".

## What resists formalization (honest assessment)

Tao's proof is genuinely analytic and is **out of reach of a direct Lean proof
today** (BLOCKED, >> 1000 lines):

  * It runs the Collatz/Syracuse dynamics against a carefully chosen family of
    measures on the 3-adics / on residue classes, and controls the evolution of
    those measures (a transport/coupling argument), establishing that the pushed
    forward measures concentrate.
  * The quantitative heart is a **stable point estimate** obtained from a
    `3`-adic large-deviation / entropy bound, combined with a Fourier-analytic
    input.  Mathlib currently has the general measure-theory and `Tendsto`
    plumbing used below, but not the specialised concentration/transport
    estimates Tao needs; building those is the real cost.

So, mirroring the sibling files `CollatzStructuredOQ02OQ01.lean` (which axiomatized
the Eliahou bound) and `CollatzStructuredOQ02OQ02.lean` (which proved Eliahou's
algebraic core and isolated the finite-check residue), this file:

  * gives a **precise, machine-checkable statement** of Tao's theorem
    (`tao_2019`) so the open question is no longer informal, and the
    "logarithmic density 1" target is pinned down as `HasLogDensityOne`;
  * proves, **unconditionally and axiom-free**, that several large explicit families
    of starting values already satisfy the "drops below itself" conclusion — the
    even numbers, the powers of two, the odd residue class `n ≡ 1 (mod 4)`
    (`n ≥ 5`), the odd residue class `n ≡ 3 (mod 16)`, and the two odd classes
    `n ≡ 11, 23 (mod 32)`, and the three classes `n ≡ 7, 15, 59 (mod 128)` — so the
    elementary part of the almost-all picture is real Lean content, not scaffolding on the
    axiom.  The evens together with `1 + 4ℕ`, `3 + 16ℕ`, `11 + 32ℕ`, `23 + 32ℕ`, and
    `7, 15, 59 (mod 128)` cover **one hundred fifteen one-hundred-twenty-eighths**
    (`115/128`) of the integers via elementary residue dynamics
    (`attainsBelow_density_lower_128`, a machine-checked `≥ 115/128` lower density,
    sharpening the earlier `≥ 7/8` of `attainsBelow_density_lower_32` and `≥ 13/16` of
    `attainsBelow_density_lower_16`), and the `mod 4`/`mod 16`/`mod 32`/`mod 128` families
    exercise the non-trivial `3n+1` branch of the map.  The dyadic refinement is genuine: of
    the odd classes `n ≡ 3 (mod 4)`, only `n ≡ 3 (mod 16)` drops within its residue-determined
    window at level `16`; passing to level `32` two more half-classes stabilise —
    `11 (mod 32)` (from the unstable `11 (mod 16)`) and `23 (mod 32)` (from `7 (mod 16)`),
    each in eight forced steps.  Level `64` adds **no** new stable class, but level `128`
    adds exactly three — `7, 15, 59 (mod 128)`, each dropping in eleven forced steps to
    `81m + d` (`81 = 3^4 < 2^7 = 128`) — while the remaining refinements of
    `7, 15, 27, 31 (mod 32)` stay `m`-dependent.

References:
- Tao, T. (2019). "Almost all orbits of the Collatz map attain almost bounded
  values." *Forum Math. Pi* 8, e9.
- Terras, R. (1976). "A stopping time problem on the positive integers."
- Korec, I. (1994). "A density estimate for the 3x+1 problem."
-/
import Mathlib

namespace CollatzStructuredOQ02OQ03

open Filter

/-! ## Part I: The Collatz map (self-contained) -/

/-- The Collatz function: `n ↦ n/2` if even, `n ↦ 3n+1` if odd. -/
def collatz (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

theorem collatz_even {n : ℕ} (h : n % 2 = 0) : collatz n = n / 2 := by
  simp [collatz, h]

theorem collatz_odd {n : ℕ} (h : n % 2 = 1) : collatz n = 3 * n + 1 := by
  unfold collatz
  rw [if_neg (by omega)]

theorem collatz_two_mul (n : ℕ) : collatz (2 * n) = n := by
  simp [collatz, Nat.mul_mod_right]

/-- The Collatz map sends positive numbers to positive numbers: `n/2 ≥ 1` for a
positive even `n` and `3n+1 ≥ 1` always.  This keeps `0` out of every orbit. -/
theorem collatz_pos {n : ℕ} (hn : 0 < n) : 0 < collatz n := by
  unfold collatz
  split <;> omega

/-- Positivity propagates along the whole orbit: no iterate of a positive start
is ever `0`. -/
theorem collatz_iterate_pos {n : ℕ} (hn : 0 < n) (k : ℕ) : 0 < collatz^[k] n := by
  induction k with
  | zero => simpa using hn
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact collatz_pos ih

/-! ## Part II: Explicit residue families that drop below their start

These are the unconditional, axiom-free part of the almost-all picture: whatever
Tao's analytic argument gives for *almost all* `n`, the even numbers, the powers
of two, and the odd residue classes `n ≡ 1 (mod 4)` (`n ≥ 5`) and `n ≡ 3 (mod 16)`
are handled by elementary explicit dynamics. -/

/-- `n` *attains a value below itself*: some positive number of Collatz steps
takes `n` to a strictly smaller value.  This is the "finite stopping time"
event whose almost-all behaviour Tao controls. -/
def AttainsBelow (n : ℕ) : Prop := ∃ k, 0 < k ∧ collatz^[k] n < n

/-- Every positive **even** number drops below itself in a single step. -/
theorem even_attainsBelow {n : ℕ} (hn : 1 ≤ n) (he : n % 2 = 0) : AttainsBelow n :=
  ⟨1, one_pos, by
    rw [Function.iterate_one, collatz_even he]
    exact Nat.div_lt_self hn (by norm_num)⟩

/-- A power of two collapses to `1` after exactly that many steps:
`collatz^[k] (2^k) = 1`. -/
theorem pow_two_reaches_one (k : ℕ) : collatz^[k] (2 ^ k) = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    have hstep : collatz (2 ^ (k + 1)) = 2 ^ k := by
      rw [pow_succ']
      exact collatz_two_mul (2 ^ k)
    rw [hstep, ih]

/-- Every power of two `2^k` with `k ≥ 1` drops below itself (all the way to 1). -/
theorem pow_two_attainsBelow {k : ℕ} (hk : 1 ≤ k) : AttainsBelow (2 ^ k) := by
  refine ⟨k, hk, ?_⟩
  rw [pow_two_reaches_one]
  have h2 : (2 : ℕ) ≤ 2 ^ k := by
    simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hk
  omega

/-- Every `n ≡ 1 (mod 4)` with `n ≥ 5` drops below itself in exactly three steps:
`4m+1 ↦ 12m+4 ↦ 6m+2 ↦ 3m+1`, and `3m+1 < 4m+1` once `m ≥ 1`.  Unlike the even
numbers and the powers of two, this is a *positive-density* (one-quarter) family of
genuinely **odd** starting values, so it adds new unconditional content beyond the
trivially-even cases: the first Collatz step here is the non-trivial `3n+1` branch. -/
theorem mod_four_one_attainsBelow {n : ℕ} (hn : 5 ≤ n) (h : n % 4 = 1) :
    AttainsBelow n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 4 * m + 1 := ⟨n / 4, by omega⟩
  refine ⟨3, by norm_num, ?_⟩
  have step1 : collatz (4 * m + 1) = 12 * m + 4 := by
    rw [collatz_odd (by omega)]; ring
  have step2 : collatz (12 * m + 4) = 6 * m + 2 := by
    rw [collatz_even (by omega)]; omega
  have step3 : collatz (6 * m + 2) = 3 * m + 1 := by
    rw [collatz_even (by omega)]; omega
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', Function.iterate_zero_apply,
      step1, step2, step3]
  omega

/-- **General residue-determined drop.**  Suppose that on the residue class
`n ≡ r (mod M)` the `k`-step Collatz iterate is the affine value `c·m + d`, where
`n = M·m + r`.  If the leading coefficient `c` is strictly below the modulus `M`
*and* the additive constant `d` is strictly below the residue `r`, then **every**
member of the class drops below itself within `k` steps.

This packages the common shape of every residue-class family below.  Each such family
is a trajectory whose parities are forced by `n mod M`, ending in an affine map whose
leading coefficient is `c = 3^a · M / 2^b` where `a` is the number of `3n+1` steps and
`b = k - a` the number of halvings.  The drop criterion `c < M` is then **exactly**
`3^a < 2^b`: there are enough halvings to overcome the triplings.  Only the
class-specific affine-iterate identity `hiter` (the trajectory chase) is supplied by the
caller; the descent bookkeeping — rewriting `n = M·m + r`, monotonicity of `c·m ≤ M·m`,
and the final comparison — is shared here.

The strict hypothesis `d < r` covers the residue classes whose drop holds for **all**
`m ≥ 0`.  The boundary case `d = r` (e.g. `n ≡ 1 (mod 4)`, where `c·m + d = 3m+1` only
beats `4m+1` once `m ≥ 1`) genuinely needs the extra lower bound `n ≥ M + r` and is
handled separately. -/
theorem affine_residue_attainsBelow {M r k c d : ℕ}
    (hk : 0 < k) (hc : c < M) (hd : d < r)
    (hiter : ∀ m : ℕ, collatz^[k] (M * m + r) = c * m + d)
    {n : ℕ} (hn : n % M = r) : AttainsBelow n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = M * m + r := by
    refine ⟨n / M, ?_⟩
    have hdm := Nat.div_add_mod n M
    rw [hn] at hdm
    omega
  refine ⟨k, hk, ?_⟩
  rw [hiter]
  have hcm : c * m ≤ M * m := Nat.mul_le_mul_right m hc.le
  omega

/-! ### Reusable affine step-composition lemmas (Terras leading-coefficient law)

The per-residue trajectory chases above all share the same skeleton: track the
orbit of a residue class `M·m + r` as an **affine function** `c·m + d`, and at
each Collatz step read the parity off the *constant* coefficient `d` because the
leading coefficient `c` is held **even** (so the parity of `c·m + d` is `d mod 2`,
independent of `m`).  The two lemmas below package one such step each, turning the
hand-written `collatz_odd …; ring` / `collatz_even …; omega` boilerplate into a
reusable composition primitive.

This is exactly the affine recurrence of the Terras parity-vector law
(`collatz^[b] n = (3^a · n + C_v)/2^b` with leading coefficient `3^a/2^b`): an
even step halves `(c, d) ↦ (c/2, d/2)`, an odd step maps `(c, d) ↦ (3c, 3d+1)`,
and the window drops below its start exactly when the accumulated `c < M`, i.e.
`3^a < 2^b`.  Both lemmas are axiom-free. -/

/-- **Affine even step.**  If after `i` Collatz steps the residue class `M·m + r`
has reached the affine form `c·m + d` with `c = 2c'` and `d = 2d'` both even, then
`c·m + d` is even for every `m`, so the next step halves it to `c'·m + d'`. -/
theorem affine_step_even {M r c d c' d' i : ℕ}
    (hc : c = 2 * c') (hd : d = 2 * d')
    (hi : ∀ m : ℕ, collatz^[i] (M * m + r) = c * m + d) :
    ∀ m : ℕ, collatz^[i + 1] (M * m + r) = c' * m + d' := by
  subst hc hd
  intro m
  rw [Function.iterate_succ_apply', hi m]
  have he : (2 * c' * m + 2 * d') % 2 = 0 := by
    rw [show 2 * c' * m + 2 * d' = 2 * (c' * m + d') from by ring]; omega
  rw [collatz_even he, show 2 * c' * m + 2 * d' = 2 * (c' * m + d') from by ring]
  omega

/-- **Affine odd step.**  If after `i` Collatz steps the residue class `M·m + r`
has reached the affine form `c·m + d` with `c = 2c'` even and `d` odd, then
`c·m + d` is odd for every `m`, so the next step maps it to `(3c)·m + (3d+1)`.
The caller supplies the normalised next coefficients `cn = 3c`, `dn = 3d + 1`. -/
theorem affine_step_odd {M r c d c' cn dn i : ℕ}
    (hc : c = 2 * c') (hd : d % 2 = 1) (hcn : cn = 3 * c) (hdn : dn = 3 * d + 1)
    (hi : ∀ m : ℕ, collatz^[i] (M * m + r) = c * m + d) :
    ∀ m : ℕ, collatz^[i + 1] (M * m + r) = cn * m + dn := by
  subst hc hcn hdn
  intro m
  rw [Function.iterate_succ_apply', hi m]
  have ho : (2 * c' * m + d) % 2 = 1 := by
    rw [show 2 * c' * m + d = 2 * (c' * m) + d from by ring]; omega
  rw [collatz_odd ho]
  ring

/-- **Worked template / validation** for the affine step-composition lemmas: the
`n ≡ 3 (mod 16)` trajectory `16m+3 ↦ 48m+10 ↦ 24m+5 ↦ 72m+16 ↦ 36m+8 ↦ 18m+4 ↦
9m+2` derived purely by chaining `affine_step_odd`/`affine_step_even` (parities
odd, even, odd, even, even, even), with no per-step `ring`/`omega` bookkeeping —
each step only names the next `(c, d)` and discharges the arithmetic side
conditions by `rfl`.  Used below to give `mod_sixteen_three_attainsBelow` a
one-line `hiter`. -/
theorem mod_sixteen_three_trajectory (m : ℕ) :
    collatz^[6] (16 * m + 3) = 9 * m + 2 := by
  have h0 : ∀ m : ℕ, collatz^[0] (16 * m + 3) = 16 * m + 3 := fun _ => rfl
  have h1 := affine_step_odd  (c := 16) (c' := 8)  (cn := 48) (dn := 10) (d := 3)
              rfl rfl rfl rfl h0
  have h2 := affine_step_even (c := 48) (c' := 24) (d := 10) (d' := 5)  rfl rfl h1
  have h3 := affine_step_odd  (c := 24) (c' := 12) (cn := 72) (dn := 16) (d := 5)
              rfl rfl rfl rfl h2
  have h4 := affine_step_even (c := 72) (c' := 36) (d := 16) (d' := 8) rfl rfl h3
  have h5 := affine_step_even (c := 36) (c' := 18) (d := 8)  (d' := 4) rfl rfl h4
  have h6 := affine_step_even (c := 18) (c' := 9)  (d := 4)  (d' := 2) rfl rfl h5
  exact h6 m

/-- Every `n ≡ 3 (mod 16)` drops below itself in exactly six steps:
`16m+3 ↦ 48m+10 ↦ 24m+5 ↦ 72m+16 ↦ 36m+8 ↦ 18m+4 ↦ 9m+2`, and `9m+2 < 16m+3` for
every `m ≥ 0`.  All six parities are forced by the residue `mod 16` alone (independent
of `m`), so this is a genuine residue-class drop, not a per-number accident.  It is the
*one* new residue that stabilises at level `16`: of the odd classes `n ≡ 3 (mod 4)`
(i.e. `n mod 16 ∈ {3, 7, 11, 15}`), only `n ≡ 3` drops within its residue-determined
window — the classes `7, 11, 15 (mod 16)` have `m`-dependent stopping times and require
a finer modulus.  Adding this class lifts the unconditional density floor from `3/4` to
`13/16`. -/
theorem mod_sixteen_three_attainsBelow {n : ℕ} (h : n % 16 = 3) : AttainsBelow n :=
  -- M = 16, r = 3, k = 6, c = 9, d = 2; here a = 2 odd steps, b = 4 halvings,
  -- and `c = 9 = 3^2 < 16` is `3^2 < 2^4`.
  affine_residue_attainsBelow (M := 16) (r := 3) (k := 6) (c := 9) (d := 2)
    (by norm_num) (by norm_num) (by norm_num)
    mod_sixteen_three_trajectory h

/-- Every `n ≡ 11 (mod 32)` drops below itself in exactly eight residue-determined steps:
`32m+11 ↦ 96m+34 ↦ 48m+17 ↦ 144m+52 ↦ 72m+26 ↦ 36m+13 ↦ 108m+40 ↦ 54m+20 ↦ 27m+10`,
and `27m+10 < 32m+11` for every `m ≥ 0`.  All eight parities are forced by the residue
`mod 32` alone.  This is one of the *two* new residues that stabilise only at level `32`:
its class `11 (mod 16)` had an `m`-dependent stopping time at level `16`, but the finer
split `{11, 27} (mod 32)` separates the stable half (`11`) from the unstable half (`27`). -/
theorem mod_thirtytwo_eleven_attainsBelow {n : ℕ} (h : n % 32 = 11) : AttainsBelow n :=
  -- M = 32, r = 11, k = 8, c = 27, d = 10; here a = 3 odd steps, b = 5 halvings,
  -- and `c = 27 = 3^3 < 32` is `3^3 < 2^5`.
  affine_residue_attainsBelow (M := 32) (r := 11) (k := 8) (c := 27) (d := 10)
    (by norm_num) (by norm_num) (by norm_num)
    (fun m => by
      have s1 : collatz (32 * m + 11) = 96 * m + 34 := by rw [collatz_odd (by omega)]; ring
      have s2 : collatz (96 * m + 34) = 48 * m + 17 := by rw [collatz_even (by omega)]; omega
      have s3 : collatz (48 * m + 17) = 144 * m + 52 := by rw [collatz_odd (by omega)]; ring
      have s4 : collatz (144 * m + 52) = 72 * m + 26 := by rw [collatz_even (by omega)]; omega
      have s5 : collatz (72 * m + 26) = 36 * m + 13 := by rw [collatz_even (by omega)]; omega
      have s6 : collatz (36 * m + 13) = 108 * m + 40 := by rw [collatz_odd (by omega)]; ring
      have s7 : collatz (108 * m + 40) = 54 * m + 20 := by rw [collatz_even (by omega)]; omega
      have s8 : collatz (54 * m + 20) = 27 * m + 10 := by rw [collatz_even (by omega)]; omega
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_zero_apply, s1, s2, s3, s4, s5, s6, s7, s8])
    h

/-- Every `n ≡ 23 (mod 32)` drops below itself in exactly eight residue-determined steps:
`32m+23 ↦ 96m+70 ↦ 48m+35 ↦ 144m+106 ↦ 72m+53 ↦ 216m+160 ↦ 108m+80 ↦ 54m+40 ↦ 27m+20`,
and `27m+20 < 32m+23` for every `m ≥ 0`.  All eight parities are forced by the residue
`mod 32` alone.  This is the second new residue stabilising only at level `32`: its class
`7 (mod 16)` was unstable at level `16`, and the split `{7, 23} (mod 32)` isolates the
stable half (`23`) from the unstable half (`7`).  The remaining unstable classes
`7, 15, 27, 31 (mod 32)` still have `m`-dependent stopping times and need a finer modulus. -/
theorem mod_thirtytwo_twentythree_attainsBelow {n : ℕ} (h : n % 32 = 23) : AttainsBelow n :=
  -- M = 32, r = 23, k = 8, c = 27, d = 20; here a = 3 odd steps, b = 5 halvings,
  -- and `c = 27 = 3^3 < 32` is `3^3 < 2^5`.
  affine_residue_attainsBelow (M := 32) (r := 23) (k := 8) (c := 27) (d := 20)
    (by norm_num) (by norm_num) (by norm_num)
    (fun m => by
      have s1 : collatz (32 * m + 23) = 96 * m + 70 := by rw [collatz_odd (by omega)]; ring
      have s2 : collatz (96 * m + 70) = 48 * m + 35 := by rw [collatz_even (by omega)]; omega
      have s3 : collatz (48 * m + 35) = 144 * m + 106 := by rw [collatz_odd (by omega)]; ring
      have s4 : collatz (144 * m + 106) = 72 * m + 53 := by rw [collatz_even (by omega)]; omega
      have s5 : collatz (72 * m + 53) = 216 * m + 160 := by rw [collatz_odd (by omega)]; ring
      have s6 : collatz (216 * m + 160) = 108 * m + 80 := by rw [collatz_even (by omega)]; omega
      have s7 : collatz (108 * m + 80) = 54 * m + 40 := by rw [collatz_even (by omega)]; omega
      have s8 : collatz (54 * m + 40) = 27 * m + 20 := by rw [collatz_even (by omega)]; omega
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_zero_apply, s1, s2, s3, s4, s5, s6, s7, s8])
    h

/-- Every `n ≡ 7 (mod 128)` drops below itself in exactly eleven residue-determined steps:
`128m+7 ↦ 384m+22 ↦ 192m+11 ↦ 576m+34 ↦ 288m+17 ↦ 864m+52 ↦ 432m+26 ↦ 216m+13 ↦ 648m+40
↦ 324m+20 ↦ 162m+10 ↦ 81m+5`, and `81m+5 < 128m+7` for every `m ≥ 0`.  All eleven parities
are forced by the residue `mod 128` alone.  This is the first of *three* new residues that
stabilise only at level `128`: its class `7 (mod 32)` was unstable at level `32` (and stayed
unstable at level `64`), but the finer split at level `128` isolates the stable half `7`. -/
theorem mod_onetwentyeight_seven_attainsBelow {n : ℕ} (h : n % 128 = 7) : AttainsBelow n :=
  -- M = 128, r = 7, k = 11, c = 81, d = 5; here a = 4 odd steps, b = 7 halvings,
  -- and `c = 81 = 3^4 < 128` is `3^4 < 2^7`.
  affine_residue_attainsBelow (M := 128) (r := 7) (k := 11) (c := 81) (d := 5)
    (by norm_num) (by norm_num) (by norm_num)
    (fun m => by
      have s1 : collatz (128 * m + 7) = 384 * m + 22 := by rw [collatz_odd (by omega)]; ring
      have s2 : collatz (384 * m + 22) = 192 * m + 11 := by rw [collatz_even (by omega)]; omega
      have s3 : collatz (192 * m + 11) = 576 * m + 34 := by rw [collatz_odd (by omega)]; ring
      have s4 : collatz (576 * m + 34) = 288 * m + 17 := by rw [collatz_even (by omega)]; omega
      have s5 : collatz (288 * m + 17) = 864 * m + 52 := by rw [collatz_odd (by omega)]; ring
      have s6 : collatz (864 * m + 52) = 432 * m + 26 := by rw [collatz_even (by omega)]; omega
      have s7 : collatz (432 * m + 26) = 216 * m + 13 := by rw [collatz_even (by omega)]; omega
      have s8 : collatz (216 * m + 13) = 648 * m + 40 := by rw [collatz_odd (by omega)]; ring
      have s9 : collatz (648 * m + 40) = 324 * m + 20 := by rw [collatz_even (by omega)]; omega
      have s10 : collatz (324 * m + 20) = 162 * m + 10 := by rw [collatz_even (by omega)]; omega
      have s11 : collatz (162 * m + 10) = 81 * m + 5 := by rw [collatz_even (by omega)]; omega
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply', Function.iterate_zero_apply,
          s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11])
    h

/-- Every `n ≡ 15 (mod 128)` drops below itself in exactly eleven residue-determined steps:
`128m+15 ↦ 384m+46 ↦ 192m+23 ↦ 576m+70 ↦ 288m+35 ↦ 864m+106 ↦ 432m+53 ↦ 1296m+160 ↦ 648m+80
↦ 324m+40 ↦ 162m+20 ↦ 81m+10`, and `81m+10 < 128m+15` for every `m ≥ 0`.  All eleven parities
are forced by the residue `mod 128` alone.  This is the second new residue stabilising only at
level `128`: its class `15 (mod 32)` was unstable at levels `32` and `64`. -/
theorem mod_onetwentyeight_fifteen_attainsBelow {n : ℕ} (h : n % 128 = 15) : AttainsBelow n :=
  -- M = 128, r = 15, k = 11, c = 81, d = 10; a = 4 odd steps, b = 7 halvings, `3^4 < 2^7`.
  affine_residue_attainsBelow (M := 128) (r := 15) (k := 11) (c := 81) (d := 10)
    (by norm_num) (by norm_num) (by norm_num)
    (fun m => by
      have s1 : collatz (128 * m + 15) = 384 * m + 46 := by rw [collatz_odd (by omega)]; ring
      have s2 : collatz (384 * m + 46) = 192 * m + 23 := by rw [collatz_even (by omega)]; omega
      have s3 : collatz (192 * m + 23) = 576 * m + 70 := by rw [collatz_odd (by omega)]; ring
      have s4 : collatz (576 * m + 70) = 288 * m + 35 := by rw [collatz_even (by omega)]; omega
      have s5 : collatz (288 * m + 35) = 864 * m + 106 := by rw [collatz_odd (by omega)]; ring
      have s6 : collatz (864 * m + 106) = 432 * m + 53 := by rw [collatz_even (by omega)]; omega
      have s7 : collatz (432 * m + 53) = 1296 * m + 160 := by rw [collatz_odd (by omega)]; ring
      have s8 : collatz (1296 * m + 160) = 648 * m + 80 := by rw [collatz_even (by omega)]; omega
      have s9 : collatz (648 * m + 80) = 324 * m + 40 := by rw [collatz_even (by omega)]; omega
      have s10 : collatz (324 * m + 40) = 162 * m + 20 := by rw [collatz_even (by omega)]; omega
      have s11 : collatz (162 * m + 20) = 81 * m + 10 := by rw [collatz_even (by omega)]; omega
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply', Function.iterate_zero_apply,
          s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11])
    h

/-- Every `n ≡ 59 (mod 128)` drops below itself in exactly eleven residue-determined steps:
`128m+59 ↦ 384m+178 ↦ 192m+89 ↦ 576m+268 ↦ 288m+134 ↦ 144m+67 ↦ 432m+202 ↦ 216m+101 ↦ 648m+304
↦ 324m+152 ↦ 162m+76 ↦ 81m+38`, and `81m+38 < 128m+59` for every `m ≥ 0`.  All eleven parities
are forced by the residue `mod 128` alone.  This is the third new residue stabilising only at
level `128`: its class `27 (mod 32)` was unstable at levels `32` and `64`.  The remaining odd
classes mod `128` that refine `{7, 15, 27, 31} (mod 32)` still have `m`-dependent stopping
times and need a finer modulus. -/
theorem mod_onetwentyeight_fiftynine_attainsBelow {n : ℕ} (h : n % 128 = 59) : AttainsBelow n :=
  -- M = 128, r = 59, k = 11, c = 81, d = 38; a = 4 odd steps, b = 7 halvings, `3^4 < 2^7`.
  affine_residue_attainsBelow (M := 128) (r := 59) (k := 11) (c := 81) (d := 38)
    (by norm_num) (by norm_num) (by norm_num)
    (fun m => by
      have s1 : collatz (128 * m + 59) = 384 * m + 178 := by rw [collatz_odd (by omega)]; ring
      have s2 : collatz (384 * m + 178) = 192 * m + 89 := by rw [collatz_even (by omega)]; omega
      have s3 : collatz (192 * m + 89) = 576 * m + 268 := by rw [collatz_odd (by omega)]; ring
      have s4 : collatz (576 * m + 268) = 288 * m + 134 := by rw [collatz_even (by omega)]; omega
      have s5 : collatz (288 * m + 134) = 144 * m + 67 := by rw [collatz_even (by omega)]; omega
      have s6 : collatz (144 * m + 67) = 432 * m + 202 := by rw [collatz_odd (by omega)]; ring
      have s7 : collatz (432 * m + 202) = 216 * m + 101 := by rw [collatz_even (by omega)]; omega
      have s8 : collatz (216 * m + 101) = 648 * m + 304 := by rw [collatz_odd (by omega)]; ring
      have s9 : collatz (648 * m + 304) = 324 * m + 152 := by rw [collatz_even (by omega)]; omega
      have s10 : collatz (324 * m + 152) = 162 * m + 76 := by rw [collatz_even (by omega)]; omega
      have s11 : collatz (162 * m + 76) = 81 * m + 38 := by rw [collatz_even (by omega)]; omega
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply', Function.iterate_zero_apply,
          s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11])
    h

/-- Packaging: every positive `n` that is **even** or lies in `1 + 4ℕ` (with `n ≥ 5`)
attains a value below itself.  Together these cover three-quarters of the integers,
all handled by elementary dynamics with no appeal to Tao's axiom. -/
theorem even_or_mod_four_one_attainsBelow {n : ℕ} (hn : 1 ≤ n)
    (h : n % 2 = 0 ∨ (5 ≤ n ∧ n % 4 = 1)) : AttainsBelow n := by
  rcases h with he | ⟨h5, h1⟩
  · exact even_attainsBelow hn he
  · exact mod_four_one_attainsBelow h5 h1

/-- Extended packaging: every positive `n` that is **even**, lies in `1 + 4ℕ` (`n ≥ 5`),
or lies in `3 + 16ℕ` attains a value below itself.  These three elementary families
together cover thirteen-sixteenths of the integers — the current unconditional floor
beneath Tao's density-one theorem, with no appeal to the axiom. -/
theorem even_or_mod_four_one_or_mod_sixteen_three_attainsBelow {n : ℕ} (hn : 1 ≤ n)
    (h : n % 2 = 0 ∨ (5 ≤ n ∧ n % 4 = 1) ∨ n % 16 = 3) : AttainsBelow n := by
  rcases h with he | h1 | h3
  · exact even_attainsBelow hn he
  · exact mod_four_one_attainsBelow h1.1 h1.2
  · exact mod_sixteen_three_attainsBelow h3

/-- Fully extended packaging: every positive `n` that is **even**, lies in `1 + 4ℕ`
(`n ≥ 5`), `3 + 16ℕ`, `11 + 32ℕ`, or `23 + 32ℕ` attains a value below itself.  These
five elementary families together cover seven-eighths of the integers — the current
unconditional floor beneath Tao's density-one theorem, with no appeal to the axiom. -/
theorem even_or_mod_four_one_or_mod_thirtytwo_attainsBelow {n : ℕ} (hn : 1 ≤ n)
    (h : n % 2 = 0 ∨ (5 ≤ n ∧ n % 4 = 1) ∨ n % 16 = 3 ∨ n % 32 = 11 ∨ n % 32 = 23) :
    AttainsBelow n := by
  rcases h with he | h1 | h3 | h11 | h23
  · exact even_attainsBelow hn he
  · exact mod_four_one_attainsBelow h1.1 h1.2
  · exact mod_sixteen_three_attainsBelow h3
  · exact mod_thirtytwo_eleven_attainsBelow h11
  · exact mod_thirtytwo_twentythree_attainsBelow h23

/-- Maximally extended packaging: every positive `n` that is **even**, lies in `1 + 4ℕ`
(`n ≥ 5`), `3 + 16ℕ`, `11 + 32ℕ`, `23 + 32ℕ`, `7 + 128ℕ`, `15 + 128ℕ`, or `59 + 128ℕ`
attains a value below itself.  These eight elementary families together cover
`115/128` of the integers — the current unconditional floor beneath Tao's density-one
theorem, with no appeal to the axiom. -/
theorem even_or_mod_four_one_or_mod_onetwentyeight_attainsBelow {n : ℕ} (hn : 1 ≤ n)
    (h : n % 2 = 0 ∨ (5 ≤ n ∧ n % 4 = 1) ∨ n % 16 = 3 ∨ n % 32 = 11 ∨ n % 32 = 23 ∨
         n % 128 = 7 ∨ n % 128 = 15 ∨ n % 128 = 59) :
    AttainsBelow n := by
  rcases h with he | h1 | h3 | h11 | h23 | h7 | h15 | h59
  · exact even_attainsBelow hn he
  · exact mod_four_one_attainsBelow h1.1 h1.2
  · exact mod_sixteen_three_attainsBelow h3
  · exact mod_thirtytwo_eleven_attainsBelow h11
  · exact mod_thirtytwo_twentythree_attainsBelow h23
  · exact mod_onetwentyeight_seven_attainsBelow h7
  · exact mod_onetwentyeight_fifteen_attainsBelow h15
  · exact mod_onetwentyeight_fiftynine_attainsBelow h59

/-! ## Part II.5: A quantitative density floor of 3/4

The prose "these families cover three-quarters of the integers" is upgraded here to
a machine-checked counting bound: among the first `4N` positive integers, at least
`3N - 1` already attain a value below themselves (the `2N` evens together with the
`N - 1` members of `1 + 4ℕ` that are `≥ 5`).  Dividing by `4N` and letting `N → ∞`,
the drop-below set has **lower natural density `≥ 3/4`** — the unconditional,
axiom-free floor underneath Tao's density-one theorem. -/

open Classical in
/-- **Quantitative density lower bound.**  At least `3N - 1` of the integers in
`[1, 4N]` attain a value below themselves.  The witnesses are the evens (an
injective image of `[1, 2N]` under `j ↦ 2j`) and the class `1 + 4ℕ` with value `≥ 5`
(an injective image of `[1, N-1]` under `j ↦ 4j+1`); these are disjoint by parity,
giving `2N + (N-1) = 3N - 1` distinct drop-below starts. -/
theorem attainsBelow_density_lower (N : ℕ) :
    3 * N - 1 ≤
      ((Finset.Icc 1 (4 * N)).filter (fun n => AttainsBelow n)).card := by
  classical
  -- The evens `2, 4, …, 4N`, as an injective image of `[1, 2N]`.
  set E : Finset ℕ := (Finset.Icc 1 (2 * N)).image (fun j => 2 * j) with hE
  -- The class `1 + 4ℕ` with value `≥ 5`: `5, 9, …, 4N-3`, an image of `[1, N-1]`.
  set O : Finset ℕ := (Finset.Icc 1 (N - 1)).image (fun j => 4 * j + 1) with hO
  have hEinj : Function.Injective (fun j : ℕ => 2 * j) :=
    fun a b h => by have h' : 2 * a = 2 * b := h; omega
  have hOinj : Function.Injective (fun j : ℕ => 4 * j + 1) :=
    fun a b h => by have h' : 4 * a + 1 = 4 * b + 1 := h; omega
  have hEcard : E.card = 2 * N := by
    rw [hE, Finset.card_image_of_injective _ hEinj, Nat.card_Icc]; omega
  have hOcard : O.card = N - 1 := by
    rw [hO, Finset.card_image_of_injective _ hOinj, Nat.card_Icc]; omega
  -- Parity separates the two families.
  have hEeven : ∀ x ∈ E, x % 2 = 0 := by
    intro x hx; rw [hE, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx; show 2 * i % 2 = 0; omega
  have hOodd : ∀ x ∈ O, x % 2 = 1 := by
    intro x hx; rw [hO, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx; show (4 * i + 1) % 2 = 1; omega
  have hdisj : Disjoint E O :=
    Finset.disjoint_left.mpr fun a haE haO => by
      have h1 := hEeven a haE; have h2 := hOodd a haO; omega
  -- Both families consist of drop-below starts in range.
  have hsub : E ∪ O ⊆ (Finset.Icc 1 (4 * N)).filter (fun n => AttainsBelow n) := by
    intro x hx
    rw [Finset.mem_union] at hx
    rw [Finset.mem_filter, Finset.mem_Icc]
    rcases hx with hxE | hxO
    · rw [hE, Finset.mem_image] at hxE
      obtain ⟨j, hj, rfl⟩ := hxE
      rw [Finset.mem_Icc] at hj
      show (1 ≤ 2 * j ∧ 2 * j ≤ 4 * N) ∧ AttainsBelow (2 * j)
      exact ⟨⟨by omega, by omega⟩, even_attainsBelow (by omega) (by omega)⟩
    · rw [hO, Finset.mem_image] at hxO
      obtain ⟨j, hj, rfl⟩ := hxO
      rw [Finset.mem_Icc] at hj
      show (1 ≤ 4 * j + 1 ∧ 4 * j + 1 ≤ 4 * N) ∧ AttainsBelow (4 * j + 1)
      exact ⟨⟨by omega, by omega⟩, mod_four_one_attainsBelow (by omega) (by omega)⟩
  calc 3 * N - 1 ≤ E.card + O.card := by rw [hEcard, hOcard]; omega
    _ = (E ∪ O).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ _ := Finset.card_le_card hsub

open Classical in
/-- **Sharpened quantitative density lower bound (`13/16`).**  Adjoining the residue
class `3 + 16ℕ` to the evens and `1 + 4ℕ` lifts the count: among the integers in
`[1, 16N]`, at least `13N - 1` already attain a value below themselves — the `8N` evens,
the `4N - 1` members of `1 + 4ℕ` that are `≥ 5`, and the `N` members of `3 + 16ℕ`.
The three families are pairwise disjoint (evens by parity; `1 + 4ℕ` vs `3 + 16ℕ` by their
residues `1` and `3` mod `4`), giving `8N + (4N - 1) + N = 13N - 1` distinct drop-below
starts.  Dividing by `16N` and letting `N → ∞`, the drop-below set has **lower natural
density `≥ 13/16`** — strictly above the previous `3/4` floor. -/
theorem attainsBelow_density_lower_16 (N : ℕ) :
    13 * N - 1 ≤
      ((Finset.Icc 1 (16 * N)).filter (fun n => AttainsBelow n)).card := by
  classical
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0; simp
  -- The evens `2, 4, …, 16N`, an injective image of `[1, 8N]`.
  set E : Finset ℕ := (Finset.Icc 1 (8 * N)).image (fun j => 2 * j) with hE
  -- The class `1 + 4ℕ` with value `≥ 5`: `5, 9, …, 16N-3`, an image of `[1, 4N-1]`.
  set O1 : Finset ℕ := (Finset.Icc 1 (4 * N - 1)).image (fun j => 4 * j + 1) with hO1
  -- The class `3 + 16ℕ`: `3, 19, …, 16N-13`, an image of `[0, N-1]`.
  set O3 : Finset ℕ := (Finset.Icc 0 (N - 1)).image (fun j => 16 * j + 3) with hO3
  have hEinj : Function.Injective (fun j : ℕ => 2 * j) :=
    fun a b h => by have h' : 2 * a = 2 * b := h; omega
  have hO1inj : Function.Injective (fun j : ℕ => 4 * j + 1) :=
    fun a b h => by have h' : 4 * a + 1 = 4 * b + 1 := h; omega
  have hO3inj : Function.Injective (fun j : ℕ => 16 * j + 3) :=
    fun a b h => by have h' : 16 * a + 3 = 16 * b + 3 := h; omega
  have hEcard : E.card = 8 * N := by
    rw [hE, Finset.card_image_of_injective _ hEinj, Nat.card_Icc]; omega
  have hO1card : O1.card = 4 * N - 1 := by
    rw [hO1, Finset.card_image_of_injective _ hO1inj, Nat.card_Icc]; omega
  have hO3card : O3.card = N := by
    rw [hO3, Finset.card_image_of_injective _ hO3inj, Nat.card_Icc]; omega
  -- Residues separate the three families.
  have hEeven : ∀ x ∈ E, x % 2 = 0 := by
    intro x hx; rw [hE, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx; show 2 * i % 2 = 0; omega
  have hO1mod4 : ∀ x ∈ O1, x % 4 = 1 := by
    intro x hx; rw [hO1, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx; show (4 * i + 1) % 4 = 1; omega
  have hO3mod4 : ∀ x ∈ O3, x % 4 = 3 := by
    intro x hx; rw [hO3, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx; show (16 * i + 3) % 4 = 3; omega
  have hd_E_O1 : Disjoint E O1 :=
    Finset.disjoint_left.mpr fun a ha hb => by
      have := hEeven a ha; have := hO1mod4 a hb; omega
  have hd_E_O3 : Disjoint E O3 :=
    Finset.disjoint_left.mpr fun a ha hb => by
      have := hEeven a ha; have := hO3mod4 a hb; omega
  have hd_O1_O3 : Disjoint O1 O3 :=
    Finset.disjoint_left.mpr fun a ha hb => by
      have := hO1mod4 a ha; have := hO3mod4 a hb; omega
  have hd_EO1_O3 : Disjoint (E ∪ O1) O3 :=
    Finset.disjoint_union_left.mpr ⟨hd_E_O3, hd_O1_O3⟩
  have hcard : (E ∪ O1 ∪ O3).card = E.card + O1.card + O3.card := by
    rw [Finset.card_union_of_disjoint hd_EO1_O3, Finset.card_union_of_disjoint hd_E_O1]
  -- All three families consist of drop-below starts in range.
  have hsub : E ∪ O1 ∪ O3 ⊆ (Finset.Icc 1 (16 * N)).filter (fun n => AttainsBelow n) := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_Icc]
    rw [Finset.mem_union, Finset.mem_union] at hx
    rcases hx with (hxE | hxO1) | hxO3
    · rw [hE, Finset.mem_image] at hxE
      obtain ⟨j, hj, rfl⟩ := hxE; rw [Finset.mem_Icc] at hj
      show (1 ≤ 2 * j ∧ 2 * j ≤ 16 * N) ∧ AttainsBelow (2 * j)
      exact ⟨⟨by omega, by omega⟩, even_attainsBelow (by omega) (by omega)⟩
    · rw [hO1, Finset.mem_image] at hxO1
      obtain ⟨j, hj, rfl⟩ := hxO1; rw [Finset.mem_Icc] at hj
      show (1 ≤ 4 * j + 1 ∧ 4 * j + 1 ≤ 16 * N) ∧ AttainsBelow (4 * j + 1)
      exact ⟨⟨by omega, by omega⟩, mod_four_one_attainsBelow (by omega) (by omega)⟩
    · rw [hO3, Finset.mem_image] at hxO3
      obtain ⟨j, hj, rfl⟩ := hxO3; rw [Finset.mem_Icc] at hj
      show (1 ≤ 16 * j + 3 ∧ 16 * j + 3 ≤ 16 * N) ∧ AttainsBelow (16 * j + 3)
      exact ⟨⟨by omega, by omega⟩, mod_sixteen_three_attainsBelow (by omega)⟩
  calc 13 * N - 1 ≤ E.card + O1.card + O3.card := by rw [hEcard, hO1card, hO3card]; omega
    _ = (E ∪ O1 ∪ O3).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

open Classical in
/-- **Sharpened quantitative density lower bound (`7/8`).**  Adjoining the two new
residue classes `11 + 32ℕ` and `23 + 32ℕ` lifts the count further: among the integers
in `[1, 32N]`, at least `28N - 1` already attain a value below themselves — the `16N`
evens, the `8N - 1` members of `1 + 4ℕ` that are `≥ 5`, the `2N` members of `3 + 16ℕ`,
the `N` members of `11 + 32ℕ`, and the `N` members of `23 + 32ℕ`.  The five families are
pairwise disjoint (by their residues mod `2`, `4`, and `16`), giving
`16N + (8N - 1) + 2N + N + N = 28N - 1` distinct drop-below starts.  Dividing by `32N`
and letting `N → ∞`, the drop-below set has **lower natural density `≥ 7/8`** — strictly
above the previous `13/16` floor. -/
theorem attainsBelow_density_lower_32 (N : ℕ) :
    28 * N - 1 ≤
      ((Finset.Icc 1 (32 * N)).filter (fun n => AttainsBelow n)).card := by
  classical
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0; simp
  -- The evens `2, 4, …, 32N`, an injective image of `[1, 16N]`.
  set E : Finset ℕ := (Finset.Icc 1 (16 * N)).image (fun j => 2 * j) with hE
  -- The class `1 + 4ℕ` with value `≥ 5`: `5, 9, …, 32N-3`, an image of `[1, 8N-1]`.
  set O1 : Finset ℕ := (Finset.Icc 1 (8 * N - 1)).image (fun j => 4 * j + 1) with hO1
  -- The class `3 + 16ℕ`: `3, 19, …, 32N-13`, an image of `[0, 2N-1]`.
  set O3 : Finset ℕ := (Finset.Icc 0 (2 * N - 1)).image (fun j => 16 * j + 3) with hO3
  -- The class `11 + 32ℕ`: `11, 43, …, 32N-21`, an image of `[0, N-1]`.
  set O11 : Finset ℕ := (Finset.Icc 0 (N - 1)).image (fun j => 32 * j + 11) with hO11
  -- The class `23 + 32ℕ`: `23, 55, …, 32N-9`, an image of `[0, N-1]`.
  set O23 : Finset ℕ := (Finset.Icc 0 (N - 1)).image (fun j => 32 * j + 23) with hO23
  have hEinj : Function.Injective (fun j : ℕ => 2 * j) :=
    fun a b h => by have h' : 2 * a = 2 * b := h; omega
  have hO1inj : Function.Injective (fun j : ℕ => 4 * j + 1) :=
    fun a b h => by have h' : 4 * a + 1 = 4 * b + 1 := h; omega
  have hO3inj : Function.Injective (fun j : ℕ => 16 * j + 3) :=
    fun a b h => by have h' : 16 * a + 3 = 16 * b + 3 := h; omega
  have hO11inj : Function.Injective (fun j : ℕ => 32 * j + 11) :=
    fun a b h => by have h' : 32 * a + 11 = 32 * b + 11 := h; omega
  have hO23inj : Function.Injective (fun j : ℕ => 32 * j + 23) :=
    fun a b h => by have h' : 32 * a + 23 = 32 * b + 23 := h; omega
  have hEcard : E.card = 16 * N := by
    rw [hE, Finset.card_image_of_injective _ hEinj, Nat.card_Icc]; omega
  have hO1card : O1.card = 8 * N - 1 := by
    rw [hO1, Finset.card_image_of_injective _ hO1inj, Nat.card_Icc]; omega
  have hO3card : O3.card = 2 * N := by
    rw [hO3, Finset.card_image_of_injective _ hO3inj, Nat.card_Icc]; omega
  have hO11card : O11.card = N := by
    rw [hO11, Finset.card_image_of_injective _ hO11inj, Nat.card_Icc]; omega
  have hO23card : O23.card = N := by
    rw [hO23, Finset.card_image_of_injective _ hO23inj, Nat.card_Icc]; omega
  -- Residues mod 2 / 4 / 16 separate the five families.
  have hEeven : ∀ x ∈ E, x % 2 = 0 := by
    intro x hx; rw [hE, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx; show 2 * i % 2 = 0; omega
  have hO1mod4 : ∀ x ∈ O1, x % 4 = 1 := by
    intro x hx; rw [hO1, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx; show (4 * i + 1) % 4 = 1; omega
  have hO3mod16 : ∀ x ∈ O3, x % 16 = 3 := by
    intro x hx; rw [hO3, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx; show (16 * i + 3) % 16 = 3; omega
  have hO11mod16 : ∀ x ∈ O11, x % 16 = 11 := by
    intro x hx; rw [hO11, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx; show (32 * i + 11) % 16 = 11; omega
  have hO23mod16 : ∀ x ∈ O23, x % 16 = 7 := by
    intro x hx; rw [hO23, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx; show (32 * i + 23) % 16 = 7; omega
  -- Pairwise disjointness (each pair contradicts via a residue computation).
  have hd_E_O1 : Disjoint E O1 :=
    Finset.disjoint_left.mpr fun a ha hb => by
      have := hEeven a ha; have := hO1mod4 a hb; omega
  have hd_E_O3 : Disjoint E O3 :=
    Finset.disjoint_left.mpr fun a ha hb => by
      have := hEeven a ha; have := hO3mod16 a hb; omega
  have hd_E_O11 : Disjoint E O11 :=
    Finset.disjoint_left.mpr fun a ha hb => by
      have := hEeven a ha; have := hO11mod16 a hb; omega
  have hd_E_O23 : Disjoint E O23 :=
    Finset.disjoint_left.mpr fun a ha hb => by
      have := hEeven a ha; have := hO23mod16 a hb; omega
  have hd_O1_O3 : Disjoint O1 O3 :=
    Finset.disjoint_left.mpr fun a ha hb => by
      have := hO1mod4 a ha; have := hO3mod16 a hb; omega
  have hd_O1_O11 : Disjoint O1 O11 :=
    Finset.disjoint_left.mpr fun a ha hb => by
      have := hO1mod4 a ha; have := hO11mod16 a hb; omega
  have hd_O1_O23 : Disjoint O1 O23 :=
    Finset.disjoint_left.mpr fun a ha hb => by
      have := hO1mod4 a ha; have := hO23mod16 a hb; omega
  have hd_O3_O11 : Disjoint O3 O11 :=
    Finset.disjoint_left.mpr fun a ha hb => by
      have := hO3mod16 a ha; have := hO11mod16 a hb; omega
  have hd_O3_O23 : Disjoint O3 O23 :=
    Finset.disjoint_left.mpr fun a ha hb => by
      have := hO3mod16 a ha; have := hO23mod16 a hb; omega
  have hd_O11_O23 : Disjoint O11 O23 :=
    Finset.disjoint_left.mpr fun a ha hb => by
      have := hO11mod16 a ha; have := hO23mod16 a hb; omega
  -- Build disjointness of the nested unions for the card computation.
  have hd_EO1_O3 : Disjoint (E ∪ O1) O3 :=
    Finset.disjoint_union_left.mpr ⟨hd_E_O3, hd_O1_O3⟩
  have hd_EO1O3_O11 : Disjoint (E ∪ O1 ∪ O3) O11 :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr ⟨hd_E_O11, hd_O1_O11⟩, hd_O3_O11⟩
  have hd_EO1O3O11_O23 : Disjoint (E ∪ O1 ∪ O3 ∪ O11) O23 :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_union_left.mpr ⟨hd_E_O23, hd_O1_O23⟩, hd_O3_O23⟩, hd_O11_O23⟩
  have hcard : (E ∪ O1 ∪ O3 ∪ O11 ∪ O23).card =
      E.card + O1.card + O3.card + O11.card + O23.card := by
    rw [Finset.card_union_of_disjoint hd_EO1O3O11_O23,
        Finset.card_union_of_disjoint hd_EO1O3_O11,
        Finset.card_union_of_disjoint hd_EO1_O3,
        Finset.card_union_of_disjoint hd_E_O1]
  -- All five families consist of drop-below starts in range.
  have hsub : E ∪ O1 ∪ O3 ∪ O11 ∪ O23 ⊆
      (Finset.Icc 1 (32 * N)).filter (fun n => AttainsBelow n) := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_Icc]
    rw [Finset.mem_union, Finset.mem_union, Finset.mem_union, Finset.mem_union] at hx
    rcases hx with (((hxE | hxO1) | hxO3) | hxO11) | hxO23
    · rw [hE, Finset.mem_image] at hxE
      obtain ⟨j, hj, rfl⟩ := hxE; rw [Finset.mem_Icc] at hj
      show (1 ≤ 2 * j ∧ 2 * j ≤ 32 * N) ∧ AttainsBelow (2 * j)
      exact ⟨⟨by omega, by omega⟩, even_attainsBelow (by omega) (by omega)⟩
    · rw [hO1, Finset.mem_image] at hxO1
      obtain ⟨j, hj, rfl⟩ := hxO1; rw [Finset.mem_Icc] at hj
      show (1 ≤ 4 * j + 1 ∧ 4 * j + 1 ≤ 32 * N) ∧ AttainsBelow (4 * j + 1)
      exact ⟨⟨by omega, by omega⟩, mod_four_one_attainsBelow (by omega) (by omega)⟩
    · rw [hO3, Finset.mem_image] at hxO3
      obtain ⟨j, hj, rfl⟩ := hxO3; rw [Finset.mem_Icc] at hj
      show (1 ≤ 16 * j + 3 ∧ 16 * j + 3 ≤ 32 * N) ∧ AttainsBelow (16 * j + 3)
      exact ⟨⟨by omega, by omega⟩, mod_sixteen_three_attainsBelow (by omega)⟩
    · rw [hO11, Finset.mem_image] at hxO11
      obtain ⟨j, hj, rfl⟩ := hxO11; rw [Finset.mem_Icc] at hj
      show (1 ≤ 32 * j + 11 ∧ 32 * j + 11 ≤ 32 * N) ∧ AttainsBelow (32 * j + 11)
      exact ⟨⟨by omega, by omega⟩, mod_thirtytwo_eleven_attainsBelow (by omega)⟩
    · rw [hO23, Finset.mem_image] at hxO23
      obtain ⟨j, hj, rfl⟩ := hxO23; rw [Finset.mem_Icc] at hj
      show (1 ≤ 32 * j + 23 ∧ 32 * j + 23 ≤ 32 * N) ∧ AttainsBelow (32 * j + 23)
      exact ⟨⟨by omega, by omega⟩, mod_thirtytwo_twentythree_attainsBelow (by omega)⟩
  calc 28 * N - 1
      ≤ E.card + O1.card + O3.card + O11.card + O23.card := by
        rw [hEcard, hO1card, hO3card, hO11card, hO23card]; omega
    _ = (E ∪ O1 ∪ O3 ∪ O11 ∪ O23).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

open Classical in
/-- **Sharpened quantitative density lower bound (`115/128`).**  Adjoining the three new
residue classes `7 + 128ℕ`, `15 + 128ℕ`, and `59 + 128ℕ` lifts the count further: among the
integers in `[1, 128N]`, at least `115N - 1` already attain a value below themselves — the
`64N` evens, the `32N - 1` members of `1 + 4ℕ` that are `≥ 5`, the `8N` members of `3 + 16ℕ`,
the `4N` members of `11 + 32ℕ`, the `4N` members of `23 + 32ℕ`, and `N` members from each of
`7 + 128ℕ`, `15 + 128ℕ`, and `59 + 128ℕ` (the three classes that stabilise only at level
`128`).  The eight families are pairwise disjoint (separated by their residues mod `2`, `4`,
`16`, and `32`), giving `64N + (32N - 1) + 8N + 4N + 4N + N + N + N = 115N - 1` distinct
drop-below starts.  Dividing by `128N` and letting `N → ∞`, the drop-below set has **lower
natural density `≥ 115/128`** — strictly above the previous `7/8 = 112/128` floor. -/
theorem attainsBelow_density_lower_128 (N : ℕ) :
    115 * N - 1 ≤
      ((Finset.Icc 1 (128 * N)).filter (fun n => AttainsBelow n)).card := by
  classical
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0; simp
  set E : Finset ℕ := (Finset.Icc 1 (64 * N)).image (fun j : ℕ => 2 * j) with hE
  set O1 : Finset ℕ := (Finset.Icc 1 (32 * N - 1)).image (fun j : ℕ => 4 * j + 1) with hO1
  set O3 : Finset ℕ := (Finset.Icc 0 (8 * N - 1)).image (fun j : ℕ => 16 * j + 3) with hO3
  set O11 : Finset ℕ := (Finset.Icc 0 (4 * N - 1)).image (fun j : ℕ => 32 * j + 11) with hO11
  set O23 : Finset ℕ := (Finset.Icc 0 (4 * N - 1)).image (fun j : ℕ => 32 * j + 23) with hO23
  set O7 : Finset ℕ := (Finset.Icc 0 (N - 1)).image (fun j : ℕ => 128 * j + 7) with hO7
  set O15 : Finset ℕ := (Finset.Icc 0 (N - 1)).image (fun j : ℕ => 128 * j + 15) with hO15
  set O59 : Finset ℕ := (Finset.Icc 0 (N - 1)).image (fun j : ℕ => 128 * j + 59) with hO59
  have hEinj : Function.Injective (fun j : ℕ => 2 * j) :=
    fun a b h => by have h' : (2 * a) = (2 * b) := h; omega
  have hO1inj : Function.Injective (fun j : ℕ => 4 * j + 1) :=
    fun a b h => by have h' : (4 * a + 1) = (4 * b + 1) := h; omega
  have hO3inj : Function.Injective (fun j : ℕ => 16 * j + 3) :=
    fun a b h => by have h' : (16 * a + 3) = (16 * b + 3) := h; omega
  have hO11inj : Function.Injective (fun j : ℕ => 32 * j + 11) :=
    fun a b h => by have h' : (32 * a + 11) = (32 * b + 11) := h; omega
  have hO23inj : Function.Injective (fun j : ℕ => 32 * j + 23) :=
    fun a b h => by have h' : (32 * a + 23) = (32 * b + 23) := h; omega
  have hO7inj : Function.Injective (fun j : ℕ => 128 * j + 7) :=
    fun a b h => by have h' : (128 * a + 7) = (128 * b + 7) := h; omega
  have hO15inj : Function.Injective (fun j : ℕ => 128 * j + 15) :=
    fun a b h => by have h' : (128 * a + 15) = (128 * b + 15) := h; omega
  have hO59inj : Function.Injective (fun j : ℕ => 128 * j + 59) :=
    fun a b h => by have h' : (128 * a + 59) = (128 * b + 59) := h; omega
  have hEcard : E.card = 64 * N := by
    rw [hE, Finset.card_image_of_injective _ hEinj, Nat.card_Icc]; omega
  have hO1card : O1.card = 32 * N - 1 := by
    rw [hO1, Finset.card_image_of_injective _ hO1inj, Nat.card_Icc]; omega
  have hO3card : O3.card = 8 * N := by
    rw [hO3, Finset.card_image_of_injective _ hO3inj, Nat.card_Icc]; omega
  have hO11card : O11.card = 4 * N := by
    rw [hO11, Finset.card_image_of_injective _ hO11inj, Nat.card_Icc]; omega
  have hO23card : O23.card = 4 * N := by
    rw [hO23, Finset.card_image_of_injective _ hO23inj, Nat.card_Icc]; omega
  have hO7card : O7.card = N := by
    rw [hO7, Finset.card_image_of_injective _ hO7inj, Nat.card_Icc]; omega
  have hO15card : O15.card = N := by
    rw [hO15, Finset.card_image_of_injective _ hO15inj, Nat.card_Icc]; omega
  have hO59card : O59.card = N := by
    rw [hO59, Finset.card_image_of_injective _ hO59inj, Nat.card_Icc]; omega
  have hEres : ∀ x ∈ E, x % 2 = 0 := by
    intro x hx; rw [hE, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx; show (2 * i) % 2 = 0; omega
  have hO1res : ∀ x ∈ O1, x % 4 = 1 := by
    intro x hx; rw [hO1, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx; show (4 * i + 1) % 4 = 1; omega
  have hO3res : ∀ x ∈ O3, x % 16 = 3 := by
    intro x hx; rw [hO3, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx; show (16 * i + 3) % 16 = 3; omega
  have hO11res : ∀ x ∈ O11, x % 32 = 11 := by
    intro x hx; rw [hO11, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx; show (32 * i + 11) % 32 = 11; omega
  have hO23res : ∀ x ∈ O23, x % 32 = 23 := by
    intro x hx; rw [hO23, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx; show (32 * i + 23) % 32 = 23; omega
  have hO7res : ∀ x ∈ O7, x % 32 = 7 := by
    intro x hx; rw [hO7, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx; show (128 * i + 7) % 32 = 7; omega
  have hO15res : ∀ x ∈ O15, x % 32 = 15 := by
    intro x hx; rw [hO15, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx; show (128 * i + 15) % 32 = 15; omega
  have hO59res : ∀ x ∈ O59, x % 32 = 27 := by
    intro x hx; rw [hO59, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx; show (128 * i + 59) % 32 = 27; omega
  have hd_E_O1 : Disjoint E O1 :=
    Finset.disjoint_left.mpr fun z ha hb => by
      have := hEres z ha; have := hO1res z hb; omega
  have hd_E_O3 : Disjoint E O3 :=
    Finset.disjoint_left.mpr fun z ha hb => by
      have := hEres z ha; have := hO3res z hb; omega
  have hd_E_O11 : Disjoint E O11 :=
    Finset.disjoint_left.mpr fun z ha hb => by
      have := hEres z ha; have := hO11res z hb; omega
  have hd_E_O23 : Disjoint E O23 :=
    Finset.disjoint_left.mpr fun z ha hb => by
      have := hEres z ha; have := hO23res z hb; omega
  have hd_E_O7 : Disjoint E O7 :=
    Finset.disjoint_left.mpr fun z ha hb => by
      have := hEres z ha; have := hO7res z hb; omega
  have hd_E_O15 : Disjoint E O15 :=
    Finset.disjoint_left.mpr fun z ha hb => by
      have := hEres z ha; have := hO15res z hb; omega
  have hd_E_O59 : Disjoint E O59 :=
    Finset.disjoint_left.mpr fun z ha hb => by
      have := hEres z ha; have := hO59res z hb; omega
  have hd_O1_O3 : Disjoint O1 O3 :=
    Finset.disjoint_left.mpr fun z ha hb => by
      have := hO1res z ha; have := hO3res z hb; omega
  have hd_O1_O11 : Disjoint O1 O11 :=
    Finset.disjoint_left.mpr fun z ha hb => by
      have := hO1res z ha; have := hO11res z hb; omega
  have hd_O1_O23 : Disjoint O1 O23 :=
    Finset.disjoint_left.mpr fun z ha hb => by
      have := hO1res z ha; have := hO23res z hb; omega
  have hd_O1_O7 : Disjoint O1 O7 :=
    Finset.disjoint_left.mpr fun z ha hb => by
      have := hO1res z ha; have := hO7res z hb; omega
  have hd_O1_O15 : Disjoint O1 O15 :=
    Finset.disjoint_left.mpr fun z ha hb => by
      have := hO1res z ha; have := hO15res z hb; omega
  have hd_O1_O59 : Disjoint O1 O59 :=
    Finset.disjoint_left.mpr fun z ha hb => by
      have := hO1res z ha; have := hO59res z hb; omega
  have hd_O3_O11 : Disjoint O3 O11 :=
    Finset.disjoint_left.mpr fun z ha hb => by
      have := hO3res z ha; have := hO11res z hb; omega
  have hd_O3_O23 : Disjoint O3 O23 :=
    Finset.disjoint_left.mpr fun z ha hb => by
      have := hO3res z ha; have := hO23res z hb; omega
  have hd_O3_O7 : Disjoint O3 O7 :=
    Finset.disjoint_left.mpr fun z ha hb => by
      have := hO3res z ha; have := hO7res z hb; omega
  have hd_O3_O15 : Disjoint O3 O15 :=
    Finset.disjoint_left.mpr fun z ha hb => by
      have := hO3res z ha; have := hO15res z hb; omega
  have hd_O3_O59 : Disjoint O3 O59 :=
    Finset.disjoint_left.mpr fun z ha hb => by
      have := hO3res z ha; have := hO59res z hb; omega
  have hd_O11_O23 : Disjoint O11 O23 :=
    Finset.disjoint_left.mpr fun z ha hb => by
      have := hO11res z ha; have := hO23res z hb; omega
  have hd_O11_O7 : Disjoint O11 O7 :=
    Finset.disjoint_left.mpr fun z ha hb => by
      have := hO11res z ha; have := hO7res z hb; omega
  have hd_O11_O15 : Disjoint O11 O15 :=
    Finset.disjoint_left.mpr fun z ha hb => by
      have := hO11res z ha; have := hO15res z hb; omega
  have hd_O11_O59 : Disjoint O11 O59 :=
    Finset.disjoint_left.mpr fun z ha hb => by
      have := hO11res z ha; have := hO59res z hb; omega
  have hd_O23_O7 : Disjoint O23 O7 :=
    Finset.disjoint_left.mpr fun z ha hb => by
      have := hO23res z ha; have := hO7res z hb; omega
  have hd_O23_O15 : Disjoint O23 O15 :=
    Finset.disjoint_left.mpr fun z ha hb => by
      have := hO23res z ha; have := hO15res z hb; omega
  have hd_O23_O59 : Disjoint O23 O59 :=
    Finset.disjoint_left.mpr fun z ha hb => by
      have := hO23res z ha; have := hO59res z hb; omega
  have hd_O7_O15 : Disjoint O7 O15 :=
    Finset.disjoint_left.mpr fun z ha hb => by
      have := hO7res z ha; have := hO15res z hb; omega
  have hd_O7_O59 : Disjoint O7 O59 :=
    Finset.disjoint_left.mpr fun z ha hb => by
      have := hO7res z ha; have := hO59res z hb; omega
  have hd_O15_O59 : Disjoint O15 O59 :=
    Finset.disjoint_left.mpr fun z ha hb => by
      have := hO15res z ha; have := hO59res z hb; omega
  have hdU1 : Disjoint (E) O1 := hd_E_O1
  have hdU2 : Disjoint (E ∪ O1) O3 := (Finset.disjoint_union_left.mpr ⟨hd_E_O3, hd_O1_O3⟩)
  have hdU3 : Disjoint (E ∪ O1 ∪ O3) O11 := (Finset.disjoint_union_left.mpr ⟨(Finset.disjoint_union_left.mpr ⟨hd_E_O11, hd_O1_O11⟩), hd_O3_O11⟩)
  have hdU4 : Disjoint (E ∪ O1 ∪ O3 ∪ O11) O23 := (Finset.disjoint_union_left.mpr ⟨(Finset.disjoint_union_left.mpr ⟨(Finset.disjoint_union_left.mpr ⟨hd_E_O23, hd_O1_O23⟩), hd_O3_O23⟩), hd_O11_O23⟩)
  have hdU5 : Disjoint (E ∪ O1 ∪ O3 ∪ O11 ∪ O23) O7 := (Finset.disjoint_union_left.mpr ⟨(Finset.disjoint_union_left.mpr ⟨(Finset.disjoint_union_left.mpr ⟨(Finset.disjoint_union_left.mpr ⟨hd_E_O7, hd_O1_O7⟩), hd_O3_O7⟩), hd_O11_O7⟩), hd_O23_O7⟩)
  have hdU6 : Disjoint (E ∪ O1 ∪ O3 ∪ O11 ∪ O23 ∪ O7) O15 := (Finset.disjoint_union_left.mpr ⟨(Finset.disjoint_union_left.mpr ⟨(Finset.disjoint_union_left.mpr ⟨(Finset.disjoint_union_left.mpr ⟨(Finset.disjoint_union_left.mpr ⟨hd_E_O15, hd_O1_O15⟩), hd_O3_O15⟩), hd_O11_O15⟩), hd_O23_O15⟩), hd_O7_O15⟩)
  have hdU7 : Disjoint (E ∪ O1 ∪ O3 ∪ O11 ∪ O23 ∪ O7 ∪ O15) O59 := (Finset.disjoint_union_left.mpr ⟨(Finset.disjoint_union_left.mpr ⟨(Finset.disjoint_union_left.mpr ⟨(Finset.disjoint_union_left.mpr ⟨(Finset.disjoint_union_left.mpr ⟨(Finset.disjoint_union_left.mpr ⟨hd_E_O59, hd_O1_O59⟩), hd_O3_O59⟩), hd_O11_O59⟩), hd_O23_O59⟩), hd_O7_O59⟩), hd_O15_O59⟩)
  have hcard : (E ∪ O1 ∪ O3 ∪ O11 ∪ O23 ∪ O7 ∪ O15 ∪ O59).card =
      E.card + O1.card + O3.card + O11.card + O23.card + O7.card + O15.card + O59.card := by
    rw [Finset.card_union_of_disjoint hdU7, Finset.card_union_of_disjoint hdU6, Finset.card_union_of_disjoint hdU5, Finset.card_union_of_disjoint hdU4, Finset.card_union_of_disjoint hdU3, Finset.card_union_of_disjoint hdU2, Finset.card_union_of_disjoint hdU1]
  have hsub : E ∪ O1 ∪ O3 ∪ O11 ∪ O23 ∪ O7 ∪ O15 ∪ O59 ⊆
      (Finset.Icc 1 (128 * N)).filter (fun n => AttainsBelow n) := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_Icc]
    rw [Finset.mem_union, Finset.mem_union, Finset.mem_union, Finset.mem_union, Finset.mem_union, Finset.mem_union, Finset.mem_union] at hx
    rcases hx with (((((((hxE | hxO1) | hxO3) | hxO11) | hxO23) | hxO7) | hxO15) | hxO59)
    · rw [hE, Finset.mem_image] at hxE
      obtain ⟨j, hj, rfl⟩ := hxE; rw [Finset.mem_Icc] at hj
      show (1 ≤ 2 * j ∧ 2 * j ≤ 128 * N) ∧ AttainsBelow (2 * j)
      exact ⟨⟨by omega, by omega⟩, even_attainsBelow (by omega) (by omega)⟩
    · rw [hO1, Finset.mem_image] at hxO1
      obtain ⟨j, hj, rfl⟩ := hxO1; rw [Finset.mem_Icc] at hj
      show (1 ≤ 4 * j + 1 ∧ 4 * j + 1 ≤ 128 * N) ∧ AttainsBelow (4 * j + 1)
      exact ⟨⟨by omega, by omega⟩, mod_four_one_attainsBelow (by omega) (by omega)⟩
    · rw [hO3, Finset.mem_image] at hxO3
      obtain ⟨j, hj, rfl⟩ := hxO3; rw [Finset.mem_Icc] at hj
      show (1 ≤ 16 * j + 3 ∧ 16 * j + 3 ≤ 128 * N) ∧ AttainsBelow (16 * j + 3)
      exact ⟨⟨by omega, by omega⟩, mod_sixteen_three_attainsBelow (by omega)⟩
    · rw [hO11, Finset.mem_image] at hxO11
      obtain ⟨j, hj, rfl⟩ := hxO11; rw [Finset.mem_Icc] at hj
      show (1 ≤ 32 * j + 11 ∧ 32 * j + 11 ≤ 128 * N) ∧ AttainsBelow (32 * j + 11)
      exact ⟨⟨by omega, by omega⟩, mod_thirtytwo_eleven_attainsBelow (by omega)⟩
    · rw [hO23, Finset.mem_image] at hxO23
      obtain ⟨j, hj, rfl⟩ := hxO23; rw [Finset.mem_Icc] at hj
      show (1 ≤ 32 * j + 23 ∧ 32 * j + 23 ≤ 128 * N) ∧ AttainsBelow (32 * j + 23)
      exact ⟨⟨by omega, by omega⟩, mod_thirtytwo_twentythree_attainsBelow (by omega)⟩
    · rw [hO7, Finset.mem_image] at hxO7
      obtain ⟨j, hj, rfl⟩ := hxO7; rw [Finset.mem_Icc] at hj
      show (1 ≤ 128 * j + 7 ∧ 128 * j + 7 ≤ 128 * N) ∧ AttainsBelow (128 * j + 7)
      exact ⟨⟨by omega, by omega⟩, mod_onetwentyeight_seven_attainsBelow (by omega)⟩
    · rw [hO15, Finset.mem_image] at hxO15
      obtain ⟨j, hj, rfl⟩ := hxO15; rw [Finset.mem_Icc] at hj
      show (1 ≤ 128 * j + 15 ∧ 128 * j + 15 ≤ 128 * N) ∧ AttainsBelow (128 * j + 15)
      exact ⟨⟨by omega, by omega⟩, mod_onetwentyeight_fifteen_attainsBelow (by omega)⟩
    · rw [hO59, Finset.mem_image] at hxO59
      obtain ⟨j, hj, rfl⟩ := hxO59; rw [Finset.mem_Icc] at hj
      show (1 ≤ 128 * j + 59 ∧ 128 * j + 59 ≤ 128 * N) ∧ AttainsBelow (128 * j + 59)
      exact ⟨⟨by omega, by omega⟩, mod_onetwentyeight_fiftynine_attainsBelow (by omega)⟩
  calc 115 * N - 1
      ≤ E.card + O1.card + O3.card + O11.card + O23.card + O7.card + O15.card + O59.card := by
        rw [hEcard, hO1card, hO3card, hO11card, hO23card, hO7card, hO15card, hO59card]; omega
    _ = (E ∪ O1 ∪ O3 ∪ O11 ∪ O23 ∪ O7 ∪ O15 ∪ O59).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

/-! ## Part III: The orbit minimum and logarithmic density -/

/-- The **orbit minimum** of `n`: the infimum of the values visited by the
Collatz orbit of `n` (including `n` itself).  `Col_min` in Tao's notation. -/
noncomputable def colMin (n : ℕ) : ℕ := sInf {m | ∃ k, collatz^[k] n = m}

/-- The orbit minimum never exceeds the starting value (`k = 0` visits `n`). -/
theorem colMin_le_self (n : ℕ) : colMin n ≤ n :=
  Nat.sInf_le ⟨0, Function.iterate_zero_apply collatz n⟩

/-- The orbit of a power of two reaches `1`, so its orbit minimum is `≤ 1`. -/
theorem colMin_pow_two_le_one (k : ℕ) : colMin (2 ^ k) ≤ 1 :=
  Nat.sInf_le ⟨k, pow_two_reaches_one k⟩

/-- The orbit minimum of a positive start is itself positive: `0` never occurs in
the orbit (`collatz_iterate_pos`), and the orbit is non-empty, so its infimum is
`≥ 1`. -/
theorem colMin_pos {n : ℕ} (hn : 0 < n) : 0 < colMin n := by
  unfold colMin
  rw [Nat.pos_iff_ne_zero]
  intro h
  rw [Nat.sInf_eq_zero] at h
  rcases h with h0 | hempty
  · obtain ⟨k, hk⟩ := h0
    have := collatz_iterate_pos hn k
    rw [hk] at this
    exact absurd this (lt_irrefl 0)
  · have hmem : n ∈ {m | ∃ k, collatz^[k] n = m} :=
      ⟨0, Function.iterate_zero_apply collatz n⟩
    rw [hempty] at hmem
    exact hmem

/-- The orbit minimum is **attained**: some iterate of `n` equals `colMin n`.
This is what "`Col_min`" means — the infimum over the orbit is achieved, since the
orbit is a non-empty set of naturals (`Nat.sInf_mem`). -/
theorem colMin_mem_orbit (n : ℕ) : ∃ k, collatz^[k] n = colMin n := by
  have hne : ({m | ∃ k, collatz^[k] n = m} : Set ℕ).Nonempty :=
    ⟨n, 0, Function.iterate_zero_apply collatz n⟩
  exact Nat.sInf_mem hne

/-- The orbit minimum can only **grow** along one Collatz step: the orbit of
`collatz n` is the tail `{collatz^[k+1] n}` of the orbit of `n`, a subset, so its
infimum is at least `colMin n`. -/
theorem colMin_le_collatz (n : ℕ) : colMin n ≤ colMin (collatz n) := by
  obtain ⟨k, hk⟩ := colMin_mem_orbit (collatz n)
  exact Nat.sInf_le ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

/-- The orbit minimum bounds **every** value on the orbit, not just the start:
`colMin n ≤ collatz^[k] n` for all `k`.  The `k`-th iterate lies in the orbit set,
so the infimum is `≤` it (`Nat.sInf_le`).  Generalises `colMin_le_self` (`k = 0`). -/
theorem colMin_le_iterate (n k : ℕ) : colMin n ≤ collatz^[k] n :=
  Nat.sInf_le ⟨k, rfl⟩

/-- The orbit minimum is **non-increasing along the whole trajectory**:
`colMin n ≤ colMin (collatz^[k] n)` for all `k`.  Each further step passes to a
sub-orbit whose infimum can only grow (`colMin_le_collatz`), and iterating this gives
the bound for every `k`.  Generalises `colMin_le_collatz` (`k = 1`); combined with
`colMin_le_iterate` it shows the orbit minimum of any iterate is sandwiched:
`colMin n ≤ colMin (collatz^[k] n) ≤ collatz^[k] n`. -/
theorem colMin_le_colMin_iterate (n k : ℕ) : colMin n ≤ colMin (collatz^[k] n) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact le_trans ih (colMin_le_collatz _)

/-- **The orbit-minimum recursion** (the Bellman/dynamic-programming identity for
`Col_min`): `colMin n = min n (colMin (collatz n))`.  The minimum over the orbit of
`n` is either attained at `n` itself (step `0`) or somewhere in the orbit of its
successor.  `≤` is `colMin_le_self` together with `colMin_le_collatz`; `≥` uses that
`colMin n` is attained at some step `k` (`colMin_mem_orbit`) — if `k = 0` it equals
`n`, and if `k ≥ 1` it lies in the orbit of `collatz n`, so it is `≥ colMin (collatz n)`. -/
theorem colMin_eq_min_collatz (n : ℕ) : colMin n = min n (colMin (collatz n)) := by
  refine Nat.le_antisymm (le_min (colMin_le_self n) (colMin_le_collatz n)) ?_
  obtain ⟨k, hk⟩ := colMin_mem_orbit n
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [hk0, Function.iterate_zero_apply] at hk
    rw [← hk]; exact min_le_left _ _
  · have hk1 : k - 1 + 1 = k := by omega
    have hcn : colMin (collatz n) ≤ colMin n := by
      rw [← hk]
      apply Nat.sInf_le
      refine ⟨k - 1, ?_⟩
      have hstep : collatz^[k - 1 + 1] n = collatz^[k - 1] (collatz n) :=
        Function.iterate_succ_apply collatz (k - 1) n
      rw [hk1] at hstep
      exact hstep.symm
    exact le_trans (min_le_right _ _) hcn

/-- Sharpening `colMin_pow_two_le_one`: the orbit minimum of `2^k` is **exactly**
`1` (the orbit hits `1` and, being positive, never goes lower). -/
theorem colMin_pow_two_eq_one (k : ℕ) : colMin (2 ^ k) = 1 := by
  have hle := colMin_pow_two_le_one k
  have hpos := colMin_pos (n := 2 ^ k) (by positivity)
  omega

/-- **Bridge between Parts II and III.**  Any number that attains a value below
itself has orbit minimum strictly below its start: `colMin n < n`.  This connects
the explicit drop-below families to Tao's `Col_min` predicate (the `f n = n`
specialisation). -/
theorem attainsBelow_colMin_lt {n : ℕ} (h : AttainsBelow n) : colMin n < n := by
  obtain ⟨k, _, hlt⟩ := h
  refine lt_of_le_of_lt ?_ hlt
  exact Nat.sInf_le ⟨k, rfl⟩

/-- **The bridge is an exact equivalence.**  The converse of `attainsBelow_colMin_lt`
also holds: `colMin n < n` forces `AttainsBelow n`.  Since the orbit minimum is
*attained* (`colMin_mem_orbit`), a strict drop of the minimum below the start must
happen at a *positive* step — step `0` returns `n` itself.  So the finite-stopping-time
event `AttainsBelow n` and the `Col_min` drop `colMin n < n` are the **same** predicate:
`colMin n < n ↔ AttainsBelow n`.  This closes the Part II ↔ Part III loop, promoting the
one-directional bridge to a definitional characterization of Tao's `Col_min < n` event. -/
theorem colMin_lt_iff_attainsBelow {n : ℕ} : colMin n < n ↔ AttainsBelow n := by
  refine ⟨fun h => ?_, attainsBelow_colMin_lt⟩
  obtain ⟨k, hk⟩ := colMin_mem_orbit n
  refine ⟨k, ?_, by rw [hk]; exact h⟩
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [hk0, Function.iterate_zero_apply] at hk
    omega
  · exact hkpos

/-- **Self-minimal characterization.**  Because `colMin n ≤ n` always, the orbit
minimum equals the start exactly when `n` never drops below itself: `colMin n = n ↔
¬ AttainsBelow n`.  Such an `n` is a *valley* — a record low never subsequently beaten.
Under the Collatz conjecture the only positive valley is `1` (`colMin_pow_two_eq_one`
shows powers of two are *not* valleys). -/
theorem colMin_eq_self_iff {n : ℕ} : colMin n = n ↔ ¬ AttainsBelow n := by
  rw [← colMin_lt_iff_attainsBelow]
  have := colMin_le_self n
  omega

/-- The valley condition unwound to the trajectory: `n` is its own orbit minimum
exactly when every iterate stays at or above `n`.  A direct restatement of
`colMin_eq_self_iff` in terms of the raw orbit values, useful when the drop witness
is more convenient than the negated `AttainsBelow`. -/
theorem colMin_eq_self_iff_forall_le {n : ℕ} :
    colMin n = n ↔ ∀ k, n ≤ collatz^[k] n := by
  constructor
  · intro h k
    have := colMin_le_iterate n k
    omega
  · intro h
    obtain ⟨k, hk⟩ := colMin_mem_orbit n
    have hle := colMin_le_self n
    have hk' := h k
    rw [hk] at hk'
    omega

/-- **Idempotence / closure of the orbit minimum.**  Applying `colMin` twice gives
nothing new: `colMin (colMin n) = colMin n`.  The orbit minimum is itself a valley —
it appears on its own orbit (`colMin_mem_orbit`) as the global minimum, so it cannot
descend further.  Equivalently, `colMin n` is a fixed point of `colMin`
(`colMin_eq_self_iff` then says `¬ AttainsBelow (colMin n)`): the orbit minimum is the
canonical valley reached from `n`. -/
theorem colMin_idempotent (n : ℕ) : colMin (colMin n) = colMin n := by
  obtain ⟨k, hk⟩ := colMin_mem_orbit n
  refine Nat.le_antisymm (colMin_le_self _) ?_
  have h := colMin_le_colMin_iterate n k
  rw [hk] at h
  exact h

/-- **The terminal value `1` never drops below itself.**  Every Collatz iterate of a
positive number is positive (`collatz_iterate_pos`), so no iterate of `1` is `< 1`:
`1` is not an `AttainsBelow` number.  This is the ground truth that makes `1` the
unique positive valley — the endpoint every Collatz trajectory is conjectured to
reach and then stay at. -/
theorem not_attainsBelow_one : ¬ AttainsBelow 1 := by
  rintro ⟨k, _, hlt⟩
  have := collatz_iterate_pos (n := 1) one_pos k
  omega

/-- **The orbit minimum of `1` is `1`.**  The terminal value `1` is its own orbit
minimum: it never drops below itself (`not_attainsBelow_one`), so `colMin_eq_self_iff`
gives `colMin 1 = 1`.  This is the base/valley companion of `colMin_pow_two_eq_one`
(`colMin (2^k) = 1`): powers of two descend *to* `1`, and `1` is where the descent
stops. -/
theorem colMin_one : colMin 1 = 1 :=
  colMin_eq_self_iff.mpr not_attainsBelow_one

/-- The orbit of `0` is constantly `0`: `collatz 0 = 0 / 2 = 0`, so no iterate of `0`
is ever positive.  This is the degenerate companion of `collatz_iterate_pos` (which keeps
`0` out of every *positive* orbit) and is exactly what forces a start that reaches `1`
to be positive. -/
theorem collatz_iterate_zero (k : ℕ) : collatz^[k] 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; simp [collatz]

/-- **The orbit minimum is `1` exactly when the trajectory reaches `1`.**  The Collatz
conjecture asserts every positive integer eventually reaches `1`; this lemma re-expresses
that terminal event through the file's central object, the orbit minimum:
`colMin n = 1 ↔ ∃ k, collatz^[k] n = 1`.  Forward, `1` is the *attained* minimum, so it
literally occurs on the orbit (`colMin_mem_orbit`).  Backward, an orbit value `1` forces
the start positive — the orbit of `0` is constantly `0` (`collatz_iterate_zero`) — whence
`1 ≤ colMin n ≤ 1` by `colMin_pos` and `colMin_le_iterate`.  So `colMin n = 1` is precisely
the statement "the Collatz conjecture holds for `n`", pinning the conjecture to a single
value of the orbit minimum. -/
theorem colMin_eq_one_iff_reaches_one {n : ℕ} :
    colMin n = 1 ↔ ∃ k, collatz^[k] n = 1 := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := colMin_mem_orbit n
    exact ⟨k, by rw [hk, h]⟩
  · rintro ⟨k, hk⟩
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · rw [h0, collatz_iterate_zero k] at hk; omega
      · exact hpos
    have hle : colMin n ≤ 1 := by rw [← hk]; exact colMin_le_iterate n k
    have hpos := colMin_pos hn
    omega

/-- **Collatz conjecture, orbit-minimum form.**  The Collatz conjecture ("every positive
integer reaches `1`") is *equivalent* to the assertion that every positive integer has
orbit minimum exactly `1`:
`(∀ n, 0 < n → ∃ k, collatz^[k] n = 1) ↔ (∀ n, 0 < n → colMin n = 1)`.  This is the global
package of the per-`n` characterization `colMin_eq_one_iff_reaches_one`, recasting the whole
conjecture as a statement purely about `colMin` — the same object whose *strict* drop
`colMin n < n` this file certifies for `115/128` of the integers. -/
theorem collatz_conjecture_iff_colMin_eq_one :
    (∀ n, 0 < n → ∃ k, collatz^[k] n = 1) ↔ (∀ n, 0 < n → colMin n = 1) := by
  constructor
  · intro h n hn; exact colMin_eq_one_iff_reaches_one.mpr (h n hn)
  · intro h n hn; exact colMin_eq_one_iff_reaches_one.mp (h n hn)

/-- Consequently the entire three-quarters family of Part II — the even numbers
and the odd class `1 + 4ℕ` (`n ≥ 5`) — has orbit minimum strictly below the start,
unconditionally and without Tao's axiom. -/
theorem even_or_mod_four_one_colMin_lt {n : ℕ} (hn : 1 ≤ n)
    (h : n % 2 = 0 ∨ (5 ≤ n ∧ n % 4 = 1)) : colMin n < n :=
  attainsBelow_colMin_lt (even_or_mod_four_one_attainsBelow hn h)

/-- The new residue class `3 + 16ℕ` likewise has orbit minimum strictly below its start,
unconditionally and without Tao's axiom. -/
theorem mod_sixteen_three_colMin_lt {n : ℕ} (h : n % 16 = 3) : colMin n < n :=
  attainsBelow_colMin_lt (mod_sixteen_three_attainsBelow h)

/-- The full thirteen-sixteenths family — evens, `1 + 4ℕ` (`n ≥ 5`), and `3 + 16ℕ` —
has orbit minimum strictly below the start. -/
theorem even_or_mod_four_one_or_mod_sixteen_three_colMin_lt {n : ℕ} (hn : 1 ≤ n)
    (h : n % 2 = 0 ∨ (5 ≤ n ∧ n % 4 = 1) ∨ n % 16 = 3) : colMin n < n :=
  attainsBelow_colMin_lt (even_or_mod_four_one_or_mod_sixteen_three_attainsBelow hn h)

/-- The new residue class `11 + 32ℕ` has orbit minimum strictly below its start. -/
theorem mod_thirtytwo_eleven_colMin_lt {n : ℕ} (h : n % 32 = 11) : colMin n < n :=
  attainsBelow_colMin_lt (mod_thirtytwo_eleven_attainsBelow h)

/-- The new residue class `23 + 32ℕ` has orbit minimum strictly below its start. -/
theorem mod_thirtytwo_twentythree_colMin_lt {n : ℕ} (h : n % 32 = 23) : colMin n < n :=
  attainsBelow_colMin_lt (mod_thirtytwo_twentythree_attainsBelow h)

/-- The full seven-eighths family — evens, `1 + 4ℕ` (`n ≥ 5`), `3 + 16ℕ`, `11 + 32ℕ`,
and `23 + 32ℕ` — has orbit minimum strictly below the start, unconditionally and without
Tao's axiom. -/
theorem even_or_mod_four_one_or_mod_thirtytwo_colMin_lt {n : ℕ} (hn : 1 ≤ n)
    (h : n % 2 = 0 ∨ (5 ≤ n ∧ n % 4 = 1) ∨ n % 16 = 3 ∨ n % 32 = 11 ∨ n % 32 = 23) :
    colMin n < n :=
  attainsBelow_colMin_lt (even_or_mod_four_one_or_mod_thirtytwo_attainsBelow hn h)

/-- The new residue class `7 + 128ℕ` has orbit minimum strictly below its start. -/
theorem mod_onetwentyeight_seven_colMin_lt {n : ℕ} (h : n % 128 = 7) : colMin n < n :=
  attainsBelow_colMin_lt (mod_onetwentyeight_seven_attainsBelow h)

/-- The new residue class `15 + 128ℕ` has orbit minimum strictly below its start. -/
theorem mod_onetwentyeight_fifteen_colMin_lt {n : ℕ} (h : n % 128 = 15) : colMin n < n :=
  attainsBelow_colMin_lt (mod_onetwentyeight_fifteen_attainsBelow h)

/-- The new residue class `59 + 128ℕ` has orbit minimum strictly below its start. -/
theorem mod_onetwentyeight_fiftynine_colMin_lt {n : ℕ} (h : n % 128 = 59) : colMin n < n :=
  attainsBelow_colMin_lt (mod_onetwentyeight_fiftynine_attainsBelow h)

/-- The full `115/128` family — evens, `1 + 4ℕ` (`n ≥ 5`), `3 + 16ℕ`, `11 + 32ℕ`, `23 + 32ℕ`,
`7 + 128ℕ`, `15 + 128ℕ`, and `59 + 128ℕ` — has orbit minimum strictly below the start,
unconditionally and without Tao's axiom. -/
theorem even_or_mod_four_one_or_mod_onetwentyeight_colMin_lt {n : ℕ} (hn : 1 ≤ n)
    (h : n % 2 = 0 ∨ (5 ≤ n ∧ n % 4 = 1) ∨ n % 16 = 3 ∨ n % 32 = 11 ∨ n % 32 = 23 ∨
         n % 128 = 7 ∨ n % 128 = 15 ∨ n % 128 = 59) : colMin n < n :=
  attainsBelow_colMin_lt (even_or_mod_four_one_or_mod_onetwentyeight_attainsBelow hn h)

/-- The logarithmic-density partial average of a set `S` up to `N`:
`(∑_{n≤N, n∈S} 1/n) / (∑_{n≤N} 1/n)`. -/
noncomputable def logDensity (S : Set ℕ) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 N, S.indicator (fun m => (1 : ℝ) / m) n)
    / (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n)

/-- `S` has **logarithmic density one** if its partial averages tend to `1`. -/
def HasLogDensityOne (S : Set ℕ) : Prop :=
  Tendsto (logDensity S) atTop (nhds 1)

/-! ## Part IV: Tao's theorem (axiomatized, deep)

The precise statement of Tao (2019).  This is the result whose formalization the
open question asks about; we record it as a single axiom and document above why a
direct Lean proof is currently out of reach.  No theorem in this file is derived
from it — the content of Parts II–III stands on its own. -/

/--
**Tao (2019):** for every `f : ℕ → ℝ` tending to infinity, the set of positive
starting values whose orbit minimum is eventually below `f n` has logarithmic
density one.  Taking `f n = n` recovers "almost all `n` have finite stopping
time"; the strength of the theorem is that `f` may grow arbitrarily slowly.
-/
axiom tao_2019 :
    ∀ f : ℕ → ℝ, Tendsto f atTop atTop →
      HasLogDensityOne {n : ℕ | 0 < n ∧ (colMin n : ℝ) < f n}

/-! ## Part V: The Terras leading-coefficient law — a general residue-drop engine

Every per-residue trajectory chase of Part II instantiates one structural law.  A
*parity vector* `v : List Bool` records the parity forced at each step of a
residue-determined window (`true` = odd, `false` = even).  Reading the orbit of the
affine class `c·m + d` along `v` keeps it affine: an odd step sends
`(c, d) ↦ (3c, 3d+1)` and an even step sends `(c, d) ↦ (c/2, d/2)` (`affStep` /
`affOrbit`).  Three facts assemble these into an engine:

* `affOrbit_realize` discharges the orbit identity `collatz^[k] (c·m+d) = c_k·m + d_k`
  from a step-by-step parity *certificate* `AffValid` — so a new residue family needs
  only that certificate, no bespoke `iterate_succ_apply'` bookkeeping;
* `affOrbit_fst` shows the leading coefficient evolves independently of `d`, equal to
  the pure `leadCoeff` fold;
* `leadCoeff_two_pow` is the **Terras `3^a/2^b` law**: from a power-of-two modulus
  `M = 2^b` whose `b` halvings are spread through `v`, the window ends at exactly
  `3^a` where `a = #odd steps`.  The drop criterion `c < M` is then literally
  `3^a < 2^b`.

`parityVector_attainsBelow` packages all three with `affine_residue_attainsBelow`:
a residue class drops below itself as soon as one exhibits a valid parity-vector
certificate with `c_k < M` and `d_k < r`.  Everything here is axiom-free. -/

/-- The leading-coefficient fold of a parity vector: an odd step triples the leading
coefficient, an even step halves it.  This is the `c`-component of the affine orbit
(`affOrbit_fst`), tracked on its own. -/
def leadCoeff : List Bool → ℕ → ℕ
  | [],          c => c
  | true  :: v,  c => leadCoeff v (3 * c)
  | false :: v,  c => leadCoeff v (c / 2)

/-- **Terras leading-coefficient law (general multiplicative form).**  Folding the
leading coefficient along `v` from a value `3^p · 2^q` carrying enough powers of two
to absorb every halving (`#even steps ≤ q`) yields `3^(p + #odd) · 2^(q - #even)`. -/
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

/-- The Terras law specialised to the residue-determined case `M = 2^b`: a parity
vector whose `b` halvings exactly match the modulus exponent ends with leading
coefficient `3^a`, `a = #odd steps`.  (Take `p = 0`, `q = #even steps` in
`leadCoeff_mul`.) -/
theorem leadCoeff_two_pow (v : List Bool) :
    leadCoeff v (2 ^ v.count false) = 3 ^ v.count true := by
  have := leadCoeff_mul v 0 (v.count false) (le_refl _)
  simpa using this

/-- The drop criterion `c < M` for a power-of-two modulus is exactly the classical
`3^a < 2^b`: enough halvings to overcome the triplings. -/
theorem leadCoeff_two_pow_lt_iff (v : List Bool) :
    leadCoeff v (2 ^ v.count false) < 2 ^ v.count false
      ↔ 3 ^ v.count true < 2 ^ v.count false := by
  rw [leadCoeff_two_pow]

/-- One affine step on the full coefficient pair `(c, d)`, driven by a parity bit. -/
def affStep : Bool → ℕ × ℕ → ℕ × ℕ
  | true,  p => (3 * p.1, 3 * p.2 + 1)
  | false, p => (p.1 / 2, p.2 / 2)

/-- Fold the affine coefficient pair `(c, d)` along a parity vector. -/
def affOrbit : List Bool → ℕ × ℕ → ℕ × ℕ
  | [],     p => p
  | b :: v, p => affOrbit v (affStep b p)

/-- The leading coefficient of the affine orbit is exactly `leadCoeff` — it evolves
independently of the constant `d`. -/
theorem affOrbit_fst (v : List Bool) :
    ∀ c d : ℕ, (affOrbit v (c, d)).1 = leadCoeff v c := by
  induction v with
  | nil => intro c d; rfl
  | cons b v ih =>
    intro c d
    cases b with
    | true => exact ih (3 * c) (3 * d + 1)
    | false => exact ih (c / 2) (d / 2)

/-- A parity vector is *valid* for the affine class `c·m + d` when each recorded
parity actually matches the value's parity along the whole orbit: at an odd step the
leading coefficient is even and the constant is odd (so `c·m+d` is odd for every `m`),
at an even step both are even.  This is the certificate that makes the trajectory
residue-determined — independent of `m`. -/
inductive AffValid : List Bool → ℕ → ℕ → Prop
  | nil  {c d} : AffValid [] c d
  | odd  {v c d} : c % 2 = 0 → d % 2 = 1 → AffValid v (3 * c) (3 * d + 1) →
      AffValid (true :: v) c d
  | even {v c d} : c % 2 = 0 → d % 2 = 0 → AffValid v (c / 2) (d / 2) →
      AffValid (false :: v) c d

/-- **General orbit-realization (the residue-drop engine).**  If the parity vector `v`
is valid for the affine class `c·m + d`, then the `v.length`-step Collatz iterate of
every member of that class is the affine value read off `affOrbit`:
`collatz^[k] (c·m + d) = c_k·m + d_k`.  This replaces the per-residue trajectory chase
with one structural induction on the certificate. -/
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

/-- **Parity-vector residue-drop engine.**  If some residue class `n ≡ r (mod M)`
admits a non-empty valid parity vector `v` whose realized affine iterate `(c_k, d_k)`
has leading coefficient `c_k < M` and constant `d_k < r`, then every member of the
class drops below itself.  This makes a new residue family a pure certificate check:
supply `v` and discharge the (decidable) side conditions. -/
theorem parityVector_attainsBelow {M r : ℕ} (v : List Bool)
    (hk : 0 < v.length) (hval : AffValid v M r)
    (hc : (affOrbit v (M, r)).1 < M) (hd : (affOrbit v (M, r)).2 < r)
    {n : ℕ} (hn : n % M = r) : AttainsBelow n :=
  affine_residue_attainsBelow hk hc hd (fun m => affOrbit_realize hval m) hn

/-- **Terras drop criterion as the textbook inequality `3^a < 2^b`.**  For a
power-of-two modulus `2^b` whose residue-determined window `v` performs exactly its
`b` halvings (`v.count false = b`, with `a := v.count true` triplings), the realized
leading coefficient is *automatically* `3^a` (the Terras law `leadCoeff_two_pow`), so
the drop condition `c_k < M` collapses to the classical Collatz inequality
`3^a < 2^b` — "enough halvings to overcome the triplings."  This is the uniform drop
theorem: a residue class drops below itself as soon as one exhibits a valid window
with `a` odd steps, `b` even steps, `3^a < 2^b`, and a constant that lands below `r`.
No `affOrbit.1` computation is needed — the leading coefficient is forced by the
parity counts alone. -/
theorem terras_attainsBelow {b r : ℕ} (v : List Bool) (hk : 0 < v.length)
    (hcount : v.count false = b) (hval : AffValid v (2 ^ b) r)
    (hlt : 3 ^ v.count true < 2 ^ b)
    (hd : (affOrbit v (2 ^ b, r)).2 < r)
    {n : ℕ} (hn : n % 2 ^ b = r) : AttainsBelow n := by
  refine parityVector_attainsBelow v hk hval ?_ hd hn
  rw [affOrbit_fst, ← hcount, leadCoeff_two_pow, hcount]
  exact hlt

/-- **Sharpness of the Terras criterion.**  For a power-of-two modulus `2^b` whose
window performs exactly its `b` halvings (`v.count false = b`), the engine's
leading-coefficient drop check `c_k < M` is *equivalent* to `3^a < 2^b` — not merely
implied by it.  The realized leading coefficient is *forced* to `3^a` (`leadCoeff_two_pow`),
so `3^a < 2^b` is the **exact** reach of the residue-determined method: a window with
`3^a ≥ 2^b` (too many triplings for its halvings) can never satisfy the coefficient drop
condition, whatever the residue `r`.  This is the necessity companion to
`terras_attainsBelow`, and it pins down why the residue-determined density floor
plateaus — enlarging the dyadic modulus `2^b` only ever certifies residues whose
determined window already carries strictly more halvings than `(log₂ 3)·(triplings)`,
so no purely residue-determined window certifies a class once `3^a ≥ 2^b`. -/
theorem terras_drop_iff {b r : ℕ} (v : List Bool) (hcount : v.count false = b) :
    (affOrbit v (2 ^ b, r)).1 < 2 ^ b ↔ 3 ^ v.count true < 2 ^ b := by
  rw [affOrbit_fst, ← hcount]; exact leadCoeff_two_pow_lt_iff v

/-- Concrete witness of the sharp boundary: the *realizable alternating* window
`[odd, even, odd, even, odd, even]` (three triplings, three halvings) lands at leading
coefficient `3^3 = 27`, which is **not** below its modulus `2^3 = 8`.  Three triplings
need at least `⌈3·log₂ 3⌉ = 5` halvings to drop; three halvings are not enough, so this
window — however its residue is chosen — cannot certify a drop.  (Contrast the gallery
families, where the halvings always outnumber the triplings: e.g. `3 (mod 16)` uses
`3^2 = 9 < 16 = 2^4`.) -/
example : ¬ (leadCoeff [true, false, true, false, true, false] (2 ^ 3) < 2 ^ 3) := by
  decide

/-- **The Collatz 3/2 heuristic as a purely combinatorial drop criterion.**  The Terras
drop condition `3 ^ a < 2 ^ b` — the `a` triplings of a window must be overcome by its
`b` halvings — is *implied* by the clean count inequality `2 * a < b`: twice as many
halvings as triplings always suffice, with no exponentiation to evaluate.  The proof is
the heuristic made exact, using only `3 ≤ 4 = 2²`:
`3 ^ a ≤ 4 ^ a = 2 ^ (2 * a) < 2 ^ b`.  (The constant `2` is not sharp — the true
threshold is `log₂ 3 ≈ 1.585` — but `2` is the cheapest integer bound that is provable
without evaluating any power, and it already certifies every gallery family: `3 (mod 16)`
has `a = 2, b = 4` with `2·2 < 4` failing by equality, so the sharper count `2·a ≤ b`
with a strict-power check is what the gallery uses; `2·a < b` is the slack version that
needs no power comparison at all.) -/
theorem pow_three_lt_two_pow_of_two_mul_lt {a b : ℕ} (h : 2 * a < b) :
    3 ^ a < 2 ^ b :=
  calc 3 ^ a ≤ 4 ^ a := Nat.pow_le_pow_left (by norm_num) a
    _ = 2 ^ (2 * a) := by rw [pow_mul]; norm_num
    _ < 2 ^ b := pow_lt_pow_right₀ (by norm_num) h

/-- **Count-only residue-drop corollary of the Terras engine.**  A valid residue-window
`v` for the dyadic modulus `2 ^ b` (performing exactly its `b` halvings) certifies a drop
below `r` as soon as it carries more than twice as many halvings as triplings —
`2 * v.count true < b` — with the additive constant landing below `r`.  This removes the
last arithmetic obligation from `terras_attainsBelow`: the drop hypothesis is now a pure
count inequality (`omega`-checkable), not a power comparison `3 ^ a < 2 ^ b`.  Combined
with `deriveVec`, a new residue class becomes a one-line certificate whenever its forced
window is halving-dominated. -/
theorem terras_attainsBelow_of_count {b r : ℕ} (v : List Bool) (hk : 0 < v.length)
    (hcount : v.count false = b) (hval : AffValid v (2 ^ b) r)
    (hcnt : 2 * v.count true < b)
    (hd : (affOrbit v (2 ^ b, r)).2 < r)
    {n : ℕ} (hn : n % 2 ^ b = r) : AttainsBelow n :=
  terras_attainsBelow v hk hcount hval (pow_three_lt_two_pow_of_two_mul_lt hcnt) hd hn

/-! ### Decidable certificates: the engine as a one-shot `by decide`

`AffValid` is a `Prop`-valued inductive, so supplying a certificate still means writing
a nested `AffValid.odd …/AffValid.even …` term by hand (one constructor per step).  The
validity condition is, however, a finite computation on the residue data alone, so it
reflects into a `Bool`.  `affValidB` is that decision procedure and `affValidB_sound`
transports a `true` result back to the `Prop`.  Bundling it with the two drop
inequalities and non-emptiness gives `dropCert`, a single `Bool` whose truth — checked by
`decide` — certifies that a whole residue class drops below itself.  Adding a new
residue family is then literally one `by decide`, with no trajectory chase and no
hand-built certificate term. -/

/-- Computable Boolean validity checker mirroring `AffValid`: an odd bit needs the
leading coefficient even and the constant odd (then recurse on the tripled pair); an
even bit needs both even (then recurse on the halved pair). -/
def affValidB : List Bool → ℕ → ℕ → Bool
  | [],          _, _ => true
  | true  :: v,  c, d => (c % 2 == 0) && (d % 2 == 1) && affValidB v (3 * c) (3 * d + 1)
  | false :: v,  c, d => (c % 2 == 0) && (d % 2 == 0) && affValidB v (c / 2) (d / 2)

/-- The Boolean checker is sound for the `Prop`-valued certificate: a `true` evaluation
of `affValidB` produces an `AffValid` derivation.  This is what lets `decide` discharge a
parity certificate. -/
theorem affValidB_sound : ∀ {v : List Bool} {c d : ℕ},
    affValidB v c d = true → AffValid v c d := by
  intro v
  induction v with
  | nil => intro c d _; exact AffValid.nil
  | cons b v ih =>
    intro c d h
    cases b with
    | true =>
      simp only [affValidB, Bool.and_eq_true, beq_iff_eq] at h
      exact AffValid.odd h.1.1 h.1.2 (ih h.2)
    | false =>
      simp only [affValidB, Bool.and_eq_true, beq_iff_eq] at h
      exact AffValid.even h.1.1 h.1.2 (ih h.2)

/-- A single Boolean drop-certificate for the residue class `r (mod M)` along the parity
vector `v`: non-empty, valid for `(M, r)`, and the realized affine iterate `(c_k, d_k)`
satisfies the drop conditions `c_k < M` and `d_k < r`.  Each conjunct is a finite
computation, so `dropCert M r v` evaluates by `decide`. -/
def dropCert (M r : ℕ) (v : List Bool) : Bool :=
  decide (0 < v.length) && affValidB v M r &&
    decide ((affOrbit v (M, r)).1 < M) && decide ((affOrbit v (M, r)).2 < r)

/-- **One-shot residue-drop engine.**  A `true` drop-certificate for `(M, r, v)` makes
every `n ≡ r (mod M)` attain a value below itself.  Combined with `decide` this reduces a
new residue family to a single line: `dropCert_attainsBelow v (by decide) h`. -/
theorem dropCert_attainsBelow {M r : ℕ} (v : List Bool)
    (h : dropCert M r v = true) {n : ℕ} (hn : n % M = r) : AttainsBelow n := by
  simp only [dropCert, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hk, hval⟩, hc⟩, hd⟩ := h
  exact parityVector_attainsBelow v hk (affValidB_sound hval) hc hd hn

/-! ### Validation: the engine reproduces the gallery families

The abstract law recovers the concrete leading coefficients of Part II, and the engine
re-derives a residue drop end-to-end from a parity certificate alone. -/

/-- The Terras law reproduces the `n ≡ 3 (mod 16)` leading coefficient `9 = 3^2` from
its parity vector `[odd, even, odd, even, even, even]` (two `3n+1` steps, four
halvings). -/
example : leadCoeff [true, false, true, false, false, false] (2 ^ 4) = 9 := by decide

/-- The Terras law reproduces the `n ≡ 11 (mod 32)` leading coefficient `27 = 3^3`
(three `3n+1` steps, five halvings). -/
example :
    leadCoeff [true, false, true, false, false, true, false, false] (2 ^ 5) = 27 := by
  decide

/-- End-to-end engine demonstration: re-derive the `n ≡ 3 (mod 16)` drop using only the
parity certificate `[odd, even, odd, even, even, even]` and a single `by decide` — no
manual trajectory chase and no hand-built `AffValid` term.  The whole drop-certificate
(validity, `9 < 16`, `2 < 3`, non-emptiness) collapses to one decidable check. -/
example {n : ℕ} (h : n % 16 = 3) : AttainsBelow n :=
  dropCert_attainsBelow [true, false, true, false, false, false] (by decide) h

/-- Worked instance of the uniform Terras criterion `terras_attainsBelow`: `n ≡ 3
(mod 16)` drops because its six-step window has `a = 2` triplings and `b = 4`
halvings with `3^2 = 9 < 16 = 2^4`.  The only genuine arithmetic content is that
single inequality `3^a < 2^b`; the validity, halving count `b`, and constant drop are
kernel computations.  This is the textbook "enough halvings beat the triplings"
made into a one-line drop certificate. -/
example {n : ℕ} (h : n % 16 = 3) : AttainsBelow n :=
  terras_attainsBelow (b := 4) [true, false, true, false, false, false]
    (by decide) (by decide) (affValidB_sound (by decide))
    (by decide) (by decide)
    (show n % 2 ^ 4 = 3 by rw [show (2 : ℕ) ^ 4 = 16 from by norm_num]; exact h)

/-- The one-shot certificate scales to longer windows with no extra proof effort: the
`n ≡ 11 (mod 32)` drop (eight steps, parity vector `[odd,even,odd,even,even,odd,even,even]`,
final affine coefficient `27 = 3^3 < 32`) is the *same* single `by decide`. -/
example {n : ℕ} (h : n % 32 = 11) : AttainsBelow n :=
  dropCert_attainsBelow
    [true, false, true, false, false, true, false, false] (by decide) h

/-! ### Deriving the parity vector: the engine from `(M, r)` alone

The decidable certificate above still requires the caller to *supply* the parity
vector `v` by hand (e.g. `[true, false, true, false, false, false]` for `mod 16`).
Hand-computing that vector is exactly the error-prone step that produced the broken
mod-128 commit (#30735, a wrong trajectory that referenced theorems never written).

`deriveVector b (M, r)` removes the hand step entirely: it simulates `b` affine
steps starting from `(M, r)`, reading each parity bit off the constant component
`d` (the value `M·m + r` has the same parity as `r` precisely while the leading
coefficient stays even — the residue-determined window).  The headline fact
`deriveVector_of_affValid` shows the derivation is *canonical*: it recovers **the**
valid parity vector of any length whenever one exists, so it is a complete
replacement for the hand-supplied vector — not a heuristic.  A residue family is then
certified from `(M, r, b)` plus a single `by decide`, with no parity vector ever
written or computed by the author. -/

/-- Derive the parity vector of a residue class by simulating `b` affine steps from
the coefficient pair `p = (c, d)`, reading each bit off the constant's parity
(`d % 2 = 1` ⇒ odd step).  Structural recursion on the step budget `b`, so it always
terminates; the budget plays the role the modulus exponent does for `M = 2^b`. -/
def deriveVector : ℕ → ℕ × ℕ → List Bool
  | 0,     _ => []
  | b + 1, p => decide (p.2 % 2 = 1) :: deriveVector b (affStep (decide (p.2 % 2 = 1)) p)

/-- The derived vector has exactly the requested length. -/
theorem deriveVector_length : ∀ (b : ℕ) (p : ℕ × ℕ), (deriveVector b p).length = b := by
  intro b
  induction b with
  | zero => intro p; rfl
  | succ b ih => intro p; simp [deriveVector, ih]

/-- **Canonicity of the derivation.**  Every valid parity vector is exactly the one
the simulator derives: `deriveVector` reads bits off the constant `d`, and validity
forces the chosen bit (odd step ⇒ `d` odd, even step ⇒ `d` even).  So the derivation
is not a heuristic — it recovers *the* valid vector of any length whenever one
exists, making `deriveVector b (M, r)` a complete stand-in for a hand-written
certificate. -/
theorem deriveVector_of_affValid : ∀ {v : List Bool} {c d : ℕ},
    AffValid v c d → deriveVector v.length (c, d) = v := by
  intro v c d hv
  induction hv with
  | nil => rfl
  | @odd v c d _ hd _ ih =>
    have hb : decide (d % 2 = 1) = true := by simp [hd]
    show deriveVector (v.length + 1) (c, d) = true :: v
    simp only [deriveVector, hb, affStep]
    rw [ih]
  | @even v c d _ hd _ ih =>
    have hb : decide (d % 2 = 1) = false := by simp [hd]
    show deriveVector (v.length + 1) (c, d) = false :: v
    simp only [deriveVector, hb, affStep]
    rw [ih]

/-- **One-shot residue-drop engine with derived vector.**  The caller supplies only the
modulus `M`, residue `r`, and step budget `b`; the parity vector is derived and the whole
drop-certificate (validity, the two drop bounds, non-emptiness) is discharged by `decide`.
A new residue family becomes `deriveDropCert_attainsBelow (b := …) (by decide) h` — no
parity vector written or computed by hand. -/
theorem deriveDropCert_attainsBelow {M r b : ℕ}
    (h : dropCert M r (deriveVector b (M, r)) = true) {n : ℕ} (hn : n % M = r) :
    AttainsBelow n :=
  dropCert_attainsBelow (deriveVector b (M, r)) h hn

/-! ### Validation: every gallery family re-derived from `(M, r, b)` only

Each drop below is now certified by the modulus, residue, and a step budget — the
parity vectors `[true, false, …]` of Part II are gone.  `decide` evaluates
`deriveVector`, checks validity, and verifies `c_k < M`, `d_k < r` in one shot. -/

/-- `n ≡ 3 (mod 16)`: derived 6-step window, no hand-written vector. -/
example {n : ℕ} (h : n % 16 = 3) : AttainsBelow n :=
  deriveDropCert_attainsBelow (b := 6) (by decide) h

/-- `n ≡ 11 (mod 32)`: derived 8-step window. -/
example {n : ℕ} (h : n % 32 = 11) : AttainsBelow n :=
  deriveDropCert_attainsBelow (b := 8) (by decide) h

/-- `n ≡ 23 (mod 32)`: derived 8-step window. -/
example {n : ℕ} (h : n % 32 = 23) : AttainsBelow n :=
  deriveDropCert_attainsBelow (b := 8) (by decide) h

/-- `n ≡ 7 (mod 128)`: derived 11-step window (`3^4 = 81 < 128`). -/
example {n : ℕ} (h : n % 128 = 7) : AttainsBelow n :=
  deriveDropCert_attainsBelow (b := 11) (by decide) h

/-- `n ≡ 15 (mod 128)`: derived 11-step window. -/
example {n : ℕ} (h : n % 128 = 15) : AttainsBelow n :=
  deriveDropCert_attainsBelow (b := 11) (by decide) h

/-- `n ≡ 59 (mod 128)`: derived 11-step window. -/
example {n : ℕ} (h : n % 128 = 59) : AttainsBelow n :=
  deriveDropCert_attainsBelow (b := 11) (by decide) h

/-- The canonicity theorem in action: the derived `mod 16` vector is *literally* the
hand-written one of Part II — `deriveVector` is a drop-in replacement, not an
approximation. -/
example : deriveVector 6 (16, 3) = [true, false, true, false, false, false] := by decide

/-! ## Part VI: A general residue-class density floor

The four explicit density bounds of Part II.5 (`attainsBelow_density_lower`,
`_16`, `_32`, `_128`) all instantiate **one** counting pattern: pick a finite set
of residues modulo `M`, check each is a drop-below class, and read off a lower
density of `|residues| / M`.  Each of those four theorems re-derives the same
pairwise-disjointness/injective-image bookkeeping by hand (the `_128` case alone
runs to roughly two hundred lines of `Disjoint` witnesses).

`attainsBelow_density_of_residues` proves that pattern once, for an **arbitrary**
modulus `M` and an arbitrary certified residue set `R`.  The disjointness across
classes is folded into a single injectivity statement: the map `(r, m) ↦ M·m + r`
is injective on `R ×ˢ [1, N-1]` because `r < M` is exactly the remainder of
`M·m + r` modulo `M`.  Every later density improvement — including any level the
decidable engine `dropCert` certifies — is then a one-line corollary: supply `R`
and a proof that each member drops, with the residue count discharged by `decide`.
No new disjoint-union argument is ever needed again.  Axiom-free. -/

open Classical in
/-- **General residue-class density floor.**  Let `R` be a finite set of residues
modulo `M` (`1 ≤ M`), each of which is a *drop-below class*: every member
`M·m + r` with `m ≥ 1` attains a value below itself.  Then at least `|R|·(N-1)` of
the integers in `[1, M·N]` attain a value below themselves.  Distinct residues
yield disjoint classes (the residue `r < M` is the remainder of `M·m + r`), and
each contributes the `N-1` in-range members `M·1+r, …, M·(N-1)+r`; so the witness
set has exactly `|R|·(N-1)` elements.  Dividing by `M·N` and letting `N → ∞` gives
lower natural density `≥ |R|/M`.  This single lemma subsumes the per-level
disjoint-union bookkeeping of `attainsBelow_density_lower{,_16,_32,_128}`. -/
theorem attainsBelow_density_of_residues {M : ℕ} (hM : 1 ≤ M) (R : Finset ℕ)
    (hR : ∀ r ∈ R, r < M)
    (hdrop : ∀ r ∈ R, ∀ m : ℕ, 1 ≤ m → AttainsBelow (M * m + r))
    (N : ℕ) :
    R.card * (N - 1) ≤
      ((Finset.Icc 1 (M * N)).filter (fun n => AttainsBelow n)).card := by
  classical
  -- Witness set: all `M·m + r` for `r ∈ R` and `m ∈ [1, N-1]`, as one injective image.
  set S : Finset ℕ :=
    (R ×ˢ Finset.Icc 1 (N - 1)).image (fun p => M * p.2 + p.1) with hS
  -- The parametrisation `(r, m) ↦ M·m + r` is injective: `r` is the remainder mod `M`.
  have hinj : Set.InjOn (fun p : ℕ × ℕ => M * p.2 + p.1)
      ↑(R ×ˢ Finset.Icc 1 (N - 1)) := by
    intro p hp q hq hpq
    rw [Finset.mem_coe, Finset.mem_product] at hp hq
    have hp1 : p.1 < M := hR p.1 hp.1
    have hq1 : q.1 < M := hR q.1 hq.1
    have hpq2 : M * p.2 + p.1 = M * q.2 + q.1 := hpq
    have e1 : (M * p.2 + p.1) % M = p.1 := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp1]
    have e2 : (M * q.2 + q.1) % M = q.1 := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hq1]
    have hr_eq : p.1 = q.1 := by rw [← e1, hpq2, e2]
    have hm_eq : p.2 = q.2 := by
      have hMm : M * p.2 = M * q.2 := by omega
      exact Nat.eq_of_mul_eq_mul_left hM hMm
    exact Prod.ext_iff.mpr ⟨hr_eq, hm_eq⟩
  have hScard : S.card = R.card * (N - 1) := by
    rw [hS, Finset.card_image_of_injOn hinj, Finset.card_product, Nat.card_Icc,
        Nat.add_sub_cancel]
  -- Every witness is an in-range drop-below start.
  have hsub : S ⊆ (Finset.Icc 1 (M * N)).filter (fun n => AttainsBelow n) := by
    intro x hx
    rw [hS, Finset.mem_image] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    rw [Finset.mem_product, Finset.mem_Icc] at hp
    obtain ⟨hpR, hm1, hm2⟩ := hp
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, hdrop p.1 hpR p.2 hm1⟩
    · have hge : M * 1 ≤ M * p.2 := Nat.mul_le_mul (le_refl M) hm1
      omega
    · have hmle : M * p.2 ≤ M * (N - 1) := Nat.mul_le_mul (le_refl M) hm2
      have hr : p.1 < M := hR p.1 hpR
      have hNN : M * (N - 1) + M = M * N := by
        rw [← Nat.mul_succ]; congr 1; omega
      omega
  calc R.card * (N - 1) = S.card := hScard.symm
    _ ≤ ((Finset.Icc 1 (M * N)).filter (fun n => AttainsBelow n)).card :=
        Finset.card_le_card hsub

open Classical in
/-- **The `13/16` density floor, re-derived from the general lemma.**  Instantiate
`attainsBelow_density_of_residues` at `M = 16` with the thirteen residues that drop
within their residue-determined window — the eight evens, the four `≡ 1 (mod 4)`
(`1, 5, 9, 13`), and the one `≡ 3 (mod 16)` (`3`).  The residue count `13` is a
single kernel `decide`; every drop hypothesis is one of the Part II residue lemmas
selected by an `omega`-checked congruence.  No bespoke disjoint-union bookkeeping —
the same call at `M = 128` with the predicate
`r%2=0 ∨ r%4=1 ∨ r%16=3 ∨ r%32∈{11,23} ∨ r%128∈{7,15,59}` recovers the `115/128`
floor of `attainsBelow_density_lower_128`. -/
theorem attainsBelow_density_lower_16_general (N : ℕ) :
    13 * (N - 1) ≤
      ((Finset.Icc 1 (16 * N)).filter (fun n => AttainsBelow n)).card := by
  have hcard :
      ((Finset.range 16).filter
        (fun r => r % 2 = 0 ∨ r % 4 = 1 ∨ r % 16 = 3)).card = 13 := by decide
  have key := attainsBelow_density_of_residues (M := 16) (by norm_num)
    ((Finset.range 16).filter (fun r => r % 2 = 0 ∨ r % 4 = 1 ∨ r % 16 = 3))
    (by intro r hr; rw [Finset.mem_filter, Finset.mem_range] at hr; exact hr.1)
    (by
      intro r hr m hm
      rw [Finset.mem_filter, Finset.mem_range] at hr
      obtain ⟨_, hgood⟩ := hr
      rcases hgood with h | h | h
      · exact even_attainsBelow (by omega) (by omega)
      · exact mod_four_one_attainsBelow (by omega) (by omega)
      · exact mod_sixteen_three_attainsBelow (by omega))
    N
  rwa [hcard] at key

/-! ## Part VII: Fully auto-derived certificates — supply only the modulus and residue

The decidable certificate `dropCert` of Part V still asks the caller for the parity
vector `v`; only the *validity check* is automatic.  But for a power-of-two modulus
`M = 2^b` the parity vector is itself residue-determined and so can be **computed**
from `(b, r)` alone: starting the affine pair at `(2^b, r)`, the leading coefficient
`c` stays even until exactly `b` halvings have happened, and while `c` is even the
parity of `c·m + d` is just `d mod 2` — independent of `m`.  So each step's parity is
forced, and `deriveVec` reads it straight off the running constant.

`deriveVec` terminates by a fuel argument: two odd steps can never be consecutive (an
odd step sends `d ↦ 3d+1`, which is even), and each even step strips one factor of two
from `c`, so the residue-determined window closes after at most `2b` steps once `c`
becomes odd.  Crucially `affValidB (deriveVec fuel c d) c d = true` holds
**unconditionally** — the recursion branches on exactly the validity conditions — so no
divisibility hypothesis is needed and soundness never depends on the fuel being large
enough (an exhausted or non-dropping window simply fails the decidable drop check, it
never produces a false `AttainsBelow`).

This closes the last gap to a turnkey engine: a new residue family `r (mod 2^b)` is now
literally `autoDropCert_attainsBelow (b := …) (r := …) (by decide) h` — the caller
supplies neither a trajectory chase nor a hand-built parity vector, only the modulus
exponent and residue.  Axiom-free (`decide`, not `native_decide`). -/

/-- Auto-derive the residue-determined parity vector of the affine class `c·m + d`,
reading each forced parity off the constant `d` (valid while the leading coefficient
`c` stays even).  Stops when `c` becomes odd — at which point the window is closed and
the leading coefficient `c` is final — or when the `fuel` is exhausted.  For a
power-of-two start `c = 2^b` the closure always happens within `2b` steps. -/
def deriveVec : ℕ → ℕ → ℕ → List Bool
  | 0,         _, _ => []
  | fuel + 1,  c, d =>
      if c % 2 = 1 then []
      else if d % 2 = 1 then true  :: deriveVec fuel (3 * c) (3 * d + 1)
      else false :: deriveVec fuel (c / 2) (d / 2)

/-- The auto-derived parity vector is always a valid `AffValid` certificate for its
own starting pair, **with no hypothesis on `c, d`**: `deriveVec` branches on exactly the
parity conditions `affValidB` checks, so every recorded bit is sound by construction. -/
theorem affValidB_deriveVec :
    ∀ (fuel c d : ℕ), affValidB (deriveVec fuel c d) c d = true := by
  intro fuel
  induction fuel with
  | zero => intro c d; rfl
  | succ fuel ih =>
    intro c d
    rw [deriveVec]
    split_ifs with hc hd
    · rfl
    · have hce : c % 2 = 0 := by omega
      simp only [affValidB, Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨hce, hd⟩, ih (3 * c) (3 * d + 1)⟩
    · have hce : c % 2 = 0 := by omega
      have hde : d % 2 = 0 := by omega
      simp only [affValidB, Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨hce, hde⟩, ih (c / 2) (d / 2)⟩

/-- A single decidable certificate for the residue class `r (mod 2^b)` that derives its
own parity vector: non-empty derived window whose realized affine iterate drops
(`c_k < 2^b`, `d_k < r`).  Each conjunct is a finite computation, so this evaluates by
`decide`.  Unlike `dropCert`, the caller supplies **no** parity vector. -/
def autoDropCert (b r : ℕ) : Bool :=
  decide (0 < (deriveVec (2 * b + 1) (2 ^ b) r).length) &&
    decide ((affOrbit (deriveVec (2 * b + 1) (2 ^ b) r) (2 ^ b, r)).1 < 2 ^ b) &&
    decide ((affOrbit (deriveVec (2 * b + 1) (2 ^ b) r) (2 ^ b, r)).2 < r)

/-- **Fully auto-derived residue-drop engine.**  A `true` `autoDropCert b r` makes every
`n ≡ r (mod 2^b)` attain a value below itself — the parity vector is derived internally
from `(b, r)`, so a new residue family is one line:
`autoDropCert_attainsBelow (b := …) (r := …) (by decide) h`. -/
theorem autoDropCert_attainsBelow {b r : ℕ} (h : autoDropCert b r = true)
    {n : ℕ} (hn : n % 2 ^ b = r) : AttainsBelow n := by
  simp only [autoDropCert, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hk, hc⟩, hd⟩ := h
  exact parityVector_attainsBelow _ hk
    (affValidB_sound (affValidB_deriveVec _ _ _)) hc hd hn

open Classical in
/-- **Mechanized density floor — zero per-residue proof.**  For any exponent `b`, the
number of residues `r (mod 2^b)` that the auto engine certifies (a single decidable
filter, no hand-supplied parity vectors) times `(N-1)` lower-bounds the count of
drop-below starts in `[1, 2^b · N]`.  This is the promised union of the two halves of
the file: the general density lemma `attainsBelow_density_of_residues` fed by the
turnkey certificate `autoDropCert`, so **any** new level `b` is discharged with no new
proof — the `goodResidues` count is a `decide`, and every drop hypothesis is
`autoDropCert_attainsBelow`.  (Axiom-free: `decide`, not `native_decide`.) -/
theorem attainsBelow_density_of_autoDropCert (b N : ℕ) :
    ((Finset.range (2 ^ b)).filter (fun r => autoDropCert b r = true)).card * (N - 1) ≤
      ((Finset.Icc 1 (2 ^ b * N)).filter (fun n => AttainsBelow n)).card := by
  refine attainsBelow_density_of_residues (M := 2 ^ b) (Nat.one_le_pow b 2 (by norm_num))
    ((Finset.range (2 ^ b)).filter (fun r => autoDropCert b r = true))
    (fun r hr => (Finset.mem_range.1 (Finset.mem_filter.1 hr).1)) ?_ N
  intro r hr m _
  obtain ⟨_, hcert⟩ := Finset.mem_filter.1 hr
  have hrlt : r < 2 ^ b := Finset.mem_range.1 (Finset.mem_filter.1 hr).1
  have hmod : (2 ^ b * m + r) % 2 ^ b = r := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrlt]
  exact autoDropCert_attainsBelow hcert hmod

/-! ### Validation: the auto-derived engine reproduces the gallery families

Each call below supplies only the modulus exponent `b` and the residue `r`; the parity
vector that the Part II/V lemmas wrote out by hand is now computed by `deriveVec` and
certified by a single `by decide`. -/

/-- `n ≡ 3 (mod 16 = 2^4)` drops below itself — derived end-to-end from `(b, r) = (4, 3)`,
no parity vector supplied. -/
example {n : ℕ} (h : n % 16 = 3) : AttainsBelow n :=
  autoDropCert_attainsBelow (b := 4) (r := 3) (by decide)
    (by rw [show (2 : ℕ) ^ 4 = 16 by norm_num]; exact h)

/-- `n ≡ 11 (mod 32 = 2^5)` drops below itself — derived from `(b, r) = (5, 11)`. -/
example {n : ℕ} (h : n % 32 = 11) : AttainsBelow n :=
  autoDropCert_attainsBelow (b := 5) (r := 11) (by decide)
    (by rw [show (2 : ℕ) ^ 5 = 32 by norm_num]; exact h)

/-- `n ≡ 7 (mod 128 = 2^7)` drops below itself — derived from `(b, r) = (7, 7)`, an
eleven-step residue-determined window, the *same* one `by decide`. -/
example {n : ℕ} (h : n % 128 = 7) : AttainsBelow n :=
  autoDropCert_attainsBelow (b := 7) (r := 7) (by decide)
    (by rw [show (2 : ℕ) ^ 7 = 128 by norm_num]; exact h)

/-! ### Part VII bridge to the orbit minimum (Part III)

The per-residue `…_colMin_lt` corollaries of Part III (`mod_sixteen_three_colMin_lt`,
`mod_thirtytwo_eleven_colMin_lt`, `mod_onetwentyeight_seven_colMin_lt`, …) each compose a
*hand-written* `AttainsBelow` witness with `attainsBelow_colMin_lt`.  With the turnkey
engine in place that composition is itself uniform: **any** residue class the auto
certificate accepts has orbit minimum strictly below its start, with no per-residue proof.
This is the last hand-written layer of Part III replaced by a single general lemma. -/

/-- **Auto engine → orbit minimum.**  A residue class `r (mod 2^b)` accepted by the
turnkey certificate `autoDropCert` has orbit minimum strictly below every start:
`colMin n < n` for all `n ≡ r (mod 2^b)`.  Composes `autoDropCert_attainsBelow` (Part VII)
with `attainsBelow_colMin_lt` (Part III), so a new level `b` yields the Part III drop with
one line and no trajectory chase. -/
theorem autoDropCert_colMin_lt {b r : ℕ} (h : autoDropCert b r = true)
    {n : ℕ} (hn : n % 2 ^ b = r) : colMin n < n :=
  attainsBelow_colMin_lt (autoDropCert_attainsBelow h hn)

/-! ## Part VIII: Parity forcing — the certificate *is* the orbit's parity sequence

`affOrbit_realize` (Part V) proves only the **endpoint** of a certified window: after
`v.length` steps the iterate of `c·m + d` is the realized affine value.  It says nothing
about the *interior* parities — a priori a parity vector could disagree with the real
Collatz orbit at some intermediate step yet still land on the correct endpoint.  The
lemmas below close that gap (the standing "forcing direction" open thread): for a valid
certificate `AffValid v c d`, the genuine Collatz orbit of **every** class member
`c·m + d` exhibits exactly the recorded parity bit `v[i]` at each step `i < v.length`.

So the Terras parity vector is not a mere bookkeeping fiction that happens to realize the
drop — it is a faithful transcript of the orbit's own parity sequence, and that sequence
is *residue-determined*: identical for every `m`.  This is the converse companion to the
realization theorem, tying the certificate to the actual dynamics. -/

/-- **Parity forcing.**  Along the window certified by `AffValid v c d`, the real Collatz
orbit of every class member `c·m + d` has parity exactly the recorded bit `v[i]` at each
step `i < v.length`: `collatz^[i] (c·m + d) % 2 = (v[i]).toNat`.  The certificate's
asserted parities are the orbit's actual parities, uniformly in `m`.  (`affOrbit_realize`
gives the endpoint; this gives every interior step, so the two together say the certified
window is a completely faithful description of the residue class's dynamics.) -/
theorem affValid_orbit_parity : ∀ {v : List Bool} {c d : ℕ}, AffValid v c d →
    ∀ (m i : ℕ) (hi : i < v.length),
      collatz^[i] (c * m + d) % 2 = (v[i]'hi).toNat := by
  intro v c d hv
  induction hv with
  | nil => intro m i hi; simp only [List.length_nil] at hi; omega
  | @odd v c d hc hd _ ih =>
    intro m i hi
    obtain ⟨c', rfl⟩ : ∃ c', c = 2 * c' := ⟨c / 2, by omega⟩
    have hcm : 2 * c' * m = 2 * (c' * m) := by ring
    cases i with
    | zero =>
      simp only [Function.iterate_zero, id_eq, List.getElem_cons_zero, Bool.toNat_true]
      omega
    | succ j =>
      have hodd : (2 * c' * m + d) % 2 = 1 := by omega
      have hstep : collatz (2 * c' * m + d) = (3 * (2 * c')) * m + (3 * d + 1) := by
        rw [collatz_odd hodd]; ring
      have hj : j < v.length := by simp only [List.length_cons] at hi; omega
      rw [Function.iterate_succ_apply, hstep]
      simpa [List.getElem_cons_succ] using ih m j hj
  | @even v c d hc hd _ ih =>
    intro m i hi
    obtain ⟨c', rfl⟩ : ∃ c', c = 2 * c' := ⟨c / 2, by omega⟩
    obtain ⟨d', rfl⟩ : ∃ d', d = 2 * d' := ⟨d / 2, by omega⟩
    have hcm : 2 * c' * m = 2 * (c' * m) := by ring
    cases i with
    | zero =>
      simp only [Function.iterate_zero, id_eq, List.getElem_cons_zero, Bool.toNat_false]
      omega
    | succ j =>
      have he : (2 * c' * m + 2 * d') % 2 = 0 := by omega
      have hstep : collatz (2 * c' * m + 2 * d') = c' * m + d' := by
        rw [collatz_even he]; omega
      have hj : j < v.length := by simp only [List.length_cons] at hi; omega
      rw [Function.iterate_succ_apply, hstep]
      have key := ih m j hj
      rw [show (2 * c') / 2 = c' from by omega, show (2 * d') / 2 = d' from by omega] at key
      simpa [List.getElem_cons_succ] using key

/-- **Residue-determined parity.**  Since the forced parities depend only on the affine
class `(c, d)` and not on the member, the Collatz orbit's parity at every certified step
is the same for all `m`: the window's parity sequence is genuinely residue-determined,
which is the structural content that makes the whole Terras approach work. -/
theorem affValid_parity_indep {v : List Bool} {c d : ℕ} (hv : AffValid v c d)
    (m m' i : ℕ) (hi : i < v.length) :
    collatz^[i] (c * m + d) % 2 = collatz^[i] (c * m' + d) % 2 := by
  rw [affValid_orbit_parity hv m i hi, affValid_orbit_parity hv m' i hi]

/-- **The auto-derived vector is a faithful orbit transcript.**  For a power-of-two
modulus `2^b`, the internally computed parity vector `deriveVec (2b+1) (2^b) r` is exactly
the real Collatz parity sequence of every `n ≡ r (mod 2^b)` over its window — no drop
hypothesis needed.  This closes the loop between the residue-determined Terras vector and
the actual orbit (the standing "prove the ACTUAL parity sequence equals `v`" thread): the
turnkey engine's derived certificate does not merely *land* the class below itself, it
predicts each orbit parity along the way. -/
theorem deriveVec_orbit_parity {b r : ℕ} {n : ℕ} (hn : n % 2 ^ b = r) (i : ℕ)
    (hi : i < (deriveVec (2 * b + 1) (2 ^ b) r).length) :
    collatz^[i] n % 2 = ((deriveVec (2 * b + 1) (2 ^ b) r)[i]'hi).toNat := by
  have hval : AffValid (deriveVec (2 * b + 1) (2 ^ b) r) (2 ^ b) r :=
    affValidB_sound (affValidB_deriveVec _ _ _)
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 ^ b * m + r :=
    ⟨n / 2 ^ b, by have := Nat.div_add_mod n (2 ^ b); omega⟩
  exact affValid_orbit_parity hval m i hi

/-! ## Part IX: Interior affine realization — the certified window is affine at *every* step

`affOrbit_realize` (Part V) computes only the **endpoint** value of a certified window:
after `v.length` steps the iterate of `c·m + d` is `affOrbit v (c, d)`.  Part VIII then
recovers the interior *parities* (`affValid_orbit_parity`), but not the interior *values*.
The lemma below closes that last gap: for a valid certificate, the Collatz iterate at
**every** prefix length `i ≤ v.length` is the affine value read off the truncated fold
`affOrbit (v.take i) (c, d)` — the orbit stays affine, with residue-determined
coefficients, through the whole window, not merely at its end.

This is the value-level companion to `affValid_orbit_parity` and the common
generalization of both it and `affOrbit_realize`: taking `i = v.length` (where
`v.take v.length = v`) recovers the endpoint identity, and reducing mod 2 recovers the
parity transcript.  Everything remains axiom-free. -/

/-- **Interior affine realization.**  If `v` is a valid parity certificate for the affine
class `c·m + d`, then for every prefix length `i ≤ v.length` the `i`-step Collatz iterate
of every class member is the affine value of the truncated fold:
`collatz^[i] (c·m + d) = (affOrbit (v.take i) (c, d)).1 · m + (affOrbit (v.take i) (c, d)).2`.
The orbit is affine at every certified step, not only at the endpoint. -/
theorem affOrbit_realize_interior : ∀ {v : List Bool} {c d : ℕ}, AffValid v c d →
    ∀ (m i : ℕ), i ≤ v.length →
      collatz^[i] (c * m + d)
        = (affOrbit (v.take i) (c, d)).1 * m + (affOrbit (v.take i) (c, d)).2 := by
  intro v c d hv
  induction hv with
  | nil =>
    intro m i hi
    simp only [List.length_nil, Nat.le_zero] at hi
    subst hi
    rfl
  | @odd v c d hc hd _ ih =>
    intro m i hi
    obtain ⟨c', rfl⟩ : ∃ c', c = 2 * c' := ⟨c / 2, by omega⟩
    cases i with
    | zero => rfl
    | succ j =>
      have hj : j ≤ v.length := by simp only [List.length_cons] at hi; omega
      have hcm : 2 * c' * m = 2 * (c' * m) := by ring
      have hodd : (2 * c' * m + d) % 2 = 1 := by omega
      have hstep : collatz (2 * c' * m + d) = (3 * (2 * c')) * m + (3 * d + 1) := by
        rw [collatz_odd hodd]; ring
      rw [Function.iterate_succ_apply, hstep]
      -- goal RHS `affOrbit ((true::v).take (j+1)) (2c',d)` is defeq to
      -- `affOrbit (v.take j) (3*(2c'), 3d+1)`, exactly the ih target
      exact ih m j hj
  | @even v c d hc hd _ ih =>
    intro m i hi
    obtain ⟨c', rfl⟩ : ∃ c', c = 2 * c' := ⟨c / 2, by omega⟩
    obtain ⟨d', rfl⟩ : ∃ d', d = 2 * d' := ⟨d / 2, by omega⟩
    cases i with
    | zero => rfl
    | succ j =>
      have hj : j ≤ v.length := by simp only [List.length_cons] at hi; omega
      have hcm : 2 * c' * m = 2 * (c' * m) := by ring
      have he : (2 * c' * m + 2 * d') % 2 = 0 := by omega
      have hstep : collatz (2 * c' * m + 2 * d') = c' * m + d' := by
        rw [collatz_even he]; omega
      rw [Function.iterate_succ_apply, hstep]
      -- restate the (defeq) goal so the halved coefficients are exposed for `e1`/`e2`
      show collatz^[j] (c' * m + d')
          = (affOrbit (v.take j) ((2 * c') / 2, (2 * d') / 2)).1 * m
            + (affOrbit (v.take j) ((2 * c') / 2, (2 * d') / 2)).2
      have e1 : (2 * c') / 2 = c' := by omega
      have e2 : (2 * d') / 2 = d' := by omega
      rw [e1, e2]
      have key := ih m j hj
      rw [e1, e2] at key
      exact key

/-- **Endpoint from the interior.**  Specialising `affOrbit_realize_interior` to the full
prefix `i = v.length` (where `v.take v.length = v`) recovers the endpoint realization
`affOrbit_realize`: the interior statement is a genuine generalization, not a parallel
result. -/
theorem affOrbit_realize_of_interior {v : List Bool} {c d : ℕ} (hv : AffValid v c d)
    (m : ℕ) :
    collatz^[v.length] (c * m + d)
      = (affOrbit v (c, d)).1 * m + (affOrbit v (c, d)).2 := by
  have h := affOrbit_realize_interior hv m v.length (le_refl _)
  rwa [List.take_length] at h

/-! ## Part X: Certificate composition — chaining and slicing certified windows

Every prior part treats a certificate `AffValid v c d` as a single monolithic window.
But windows should *compose*: running the class `c·m + d` through window `v` lands it in
the class `c'·m + d'` with `(c', d') = affOrbit v (c, d)`, and if a second certificate
`w` is valid there, the two windows join into one valid certificate `v ++ w` for the
original class.  The lemmas below establish this monoid-like structure on certified
windows and its slicing converse:

* `affOrbit_append` / `leadCoeff_append` — the affine fold and its leading coefficient
  are *functorial* under concatenation: folding `v ++ w` is folding `w` after `v`.
* `affValid_append` — validity is preserved by concatenation, provided the second
  window is valid **at the affine class the first one produces**.  This is the
  composition law: a long certified window is a chain of short ones.
* `affValid_take` — validity is inherited by every prefix (the slicing converse),
  the certificate-level companion of Part IX's interior realization.
* `affOrbit_realize_append` — the payoff: the concatenated window realizes the composed
  affine map over the summed step count, so drop certificates literally chain.

Everything is axiom-free and structural, matching the rest of the engine. -/

/-- **Affine fold is functorial under concatenation.**  Folding a coefficient pair along
`v ++ w` is the same as folding along `v` and then along `w` from the result — the affine
maps of the two windows compose. -/
theorem affOrbit_append (v w : List Bool) (p : ℕ × ℕ) :
    affOrbit (v ++ w) p = affOrbit w (affOrbit v p) := by
  induction v generalizing p with
  | nil => rfl
  | cons b v ih =>
    show affOrbit (v ++ w) (affStep b p) = affOrbit w (affOrbit v (affStep b p))
    exact ih (affStep b p)

/-- **Leading coefficient is multiplicative under concatenation.**  The Terras leading
coefficient of a joined window is the second window's coefficient evolution applied to the
first's — the value-level shadow of `affOrbit_append` on the first component. -/
theorem leadCoeff_append (v w : List Bool) (c : ℕ) :
    leadCoeff (v ++ w) c = leadCoeff w (leadCoeff v c) := by
  induction v generalizing c with
  | nil => rfl
  | cons b v ih => cases b <;> exact ih _

/-- **Composition law for certificates.**  If `v` is a valid parity certificate for the
affine class `c·m + d`, and `w` is a valid certificate for the class produced by running
`v` — namely `(affOrbit v (c, d)).1 · m + (affOrbit v (c, d)).2` — then the concatenated
window `v ++ w` is a valid certificate for the original class.  Certified windows compose:
a long window is a chain of short ones glued at their affine hand-off points. -/
theorem affValid_append : ∀ {v : List Bool} {c d : ℕ}, AffValid v c d →
    ∀ {w : List Bool},
      AffValid w (affOrbit v (c, d)).1 (affOrbit v (c, d)).2 →
      AffValid (v ++ w) c d := by
  intro v c d hv
  induction hv with
  | nil => intro w hw; simpa using hw
  | @odd v c d hc hd _ ih => intro w hw; exact AffValid.odd hc hd (ih hw)
  | @even v c d hc hd _ ih => intro w hw; exact AffValid.even hc hd (ih hw)

/-- **Prefixes of a valid certificate are valid.**  Truncating a certified window `v` to
any prefix length `i` yields a certificate `v.take i` valid for the *same* starting class
`c·m + d`.  This is the certificate-level converse of `affValid_append` (slicing rather
than gluing) and the structural companion of `affOrbit_realize_interior`: not only is the
interior value affine, the interior window is itself a bona fide certificate. -/
theorem affValid_take : ∀ {v : List Bool} {c d : ℕ}, AffValid v c d →
    ∀ i : ℕ, AffValid (v.take i) c d := by
  intro v c d hv
  induction hv with
  | nil => intro i; rw [List.take_nil]; exact AffValid.nil
  | @odd v c d hc hd _ ih =>
    intro i
    cases i with
    | zero => exact AffValid.nil
    | succ j => exact AffValid.odd hc hd (ih j)
  | @even v c d hc hd _ ih =>
    intro i
    cases i with
    | zero => exact AffValid.nil
    | succ j => exact AffValid.even hc hd (ih j)

/-- **Chained realization — the composition payoff.**  Two certified windows `v` then `w`
(with `w` valid at the class `v` produces) realize the *composed* affine map over the
summed step count `v.length + w.length`: the Collatz iterate of every member of the
original class is the coefficient pair obtained by folding `v` and then `w`.  This is the
value-level statement that residue-drop certificates literally concatenate — the endpoint
realization `affOrbit_realize` applied to the glued window `affValid_append hv hw`. -/
theorem affOrbit_realize_append {v w : List Bool} {c d : ℕ} (hv : AffValid v c d)
    (hw : AffValid w (affOrbit v (c, d)).1 (affOrbit v (c, d)).2) (m : ℕ) :
    collatz^[v.length + w.length] (c * m + d)
      = (affOrbit w (affOrbit v (c, d))).1 * m + (affOrbit w (affOrbit v (c, d))).2 := by
  have h := affOrbit_realize (affValid_append hv hw) m
  rw [List.length_append, affOrbit_append] at h
  exact h

end CollatzStructuredOQ02OQ03
