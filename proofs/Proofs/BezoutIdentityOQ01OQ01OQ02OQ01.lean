import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic
import Proofs.BezoutIdentityOQ01OQ01OQ02

/-
# Extended Binary GCD: Tracking Bézout Coefficients Through the Algorithm

## Open Question (bezout-identity-oq-01-oq-01-oq-02-oq-01)

The parent `BezoutIdentityOQ01OQ01OQ02` defines `intBinaryGcd : ℤ → ℤ → ℤ`
(Stein's binary algorithm) and proves a Bézout identity
`bezout_via_intBinaryGcd` — but the coefficients there are *borrowed* from
Mathlib's `Int.gcdA` / `Int.gcdB`, not produced by the binary algorithm itself.

This file closes that gap: it builds a **constructive** extended binary GCD that
threads a Bézout pair `(x, y)` through every halving and subtraction step, so the
witnesses `a * x + b * y = gcd a b` are computed by the algorithm, not imported.

## The Algorithm

`ebGcd a b` returns `(g, x, y)` with `g = Nat.gcd a b` and
`(a : ℤ) * x + (b : ℤ) * y = g`.  We use the *subtract-don't-rehalve* binary
variant: the classic Stein step `gcd a b = gcd a ((b-a)/2)` (both odd) is
replaced by `gcd a b = gcd a (b - a)`.  This keeps it a genuine binary GCD —
common factors of two are still stripped by halving even arguments — while making
the coefficient transforms exact integer identities (no coefficient ever needs to
be halved in a *subtraction* branch, which is the classic extended-binary-GCD
pitfall).

### Coefficient transforms (each is a one-line `ring`/`omega` identity)

Let the recursive call return `(g, x, y)`.

| Branch                | Recurse on   | New `(x', y')`                         |
|-----------------------|--------------|----------------------------------------|
| both even `2a',2b'`   | `(a', b')`   | `(x, y)`, result `g ↦ 2g`              |
| `a=2a'` even, `b` odd | `(a', b)`    | `x` even: `(x/2, y)`; odd: `((x+b)/2, y-a')` |
| `a` odd, `b=2b'` even | `(a, b')`    | `y` even: `(x, y/2)`; odd: `(x-b', (y+a)/2)` |
| both odd, `a ≤ b`     | `(a, b-a)`   | `(x - y, y)`                           |
| both odd, `a > b`     | `(a-b, b)`   | `(x, y - x)`                           |

The two single-even branches use a parity case split: when the carried
coefficient is odd, adding the (odd) other argument makes it even before halving,
which is the only subtlety in the whole construction.

## Results

* `ebGcd_fst` — the first component is `Nat.gcd a b`.
* `ebGcd_bezout` / `ebGcd_bezout_gcd` — the threaded coefficients are a genuine
  Bézout witness: `a * x + b * y = gcd a b`.
* `intExtBinaryGcd_fst` — the signed extension agrees with the parent
  `intBinaryGcd`.
* `intExtBinaryGcd_bezout` — the signed Bézout identity over `ℤ`.

## Status

Fully machine-checked: no `sorry`, no extra axioms.  The four correctness theorems
depend only on Lean/Mathlib's foundational axioms `propext`, `Classical.choice`,
`Quot.sound` (verifiable with `#print axioms`).  Worked-out numerical instances
(e.g. `ebGcd 12 8 = (4, 1, -1)`, so `12·1 + 8·(-1) = 4`) are recorded as comments
in Part V to keep the file free of the `Lean.ofReduceBool` axiom that
`native_decide` would introduce.

The gcd-correctness proof mirrors the *verified* grandparent
`BezoutIdentityOQ01OQ01.binaryGcd_eq_gcd` (same recursion shape); the Bézout proof
discharges each branch by `linear_combination` of the inductive hypothesis with
the relevant cast/parity facts (all `omega`-provable).
-/

namespace BezoutIdentityOQ01OQ01OQ02OQ01

open BezoutIdentityOQ01OQ01OQ02

-- ═══════════════════════════════════════════════════════════════
-- PART I: THE EXTENDED BINARY GCD (constructive Bézout witness)
-- ═══════════════════════════════════════════════════════════════

/-- Extended binary GCD over `ℕ`, returning `(g, x, y)` with `g = Nat.gcd a b`
and the Bézout identity `(a : ℤ) * x + (b : ℤ) * y = g`.  Coefficients are
threaded through each halving/subtraction step of Stein's algorithm.

In the two single-even branches the carried `r.1` (the gcd) is pulled out front of
the inner parity `if`, so that `(ebGcd a b).1` reduces without splitting on parity. -/
def ebGcd (a b : ℕ) : ℕ × ℤ × ℤ :=
  if a = 0 then (b, 0, 1)
  else if b = 0 then (a, 1, 0)
  else if a % 2 = 0 ∧ b % 2 = 0 then
    -- both even: gcd a b = 2 * gcd (a/2) (b/2); coefficients unchanged
    let r := ebGcd (a / 2) (b / 2)
    (2 * r.1, r.2.1, r.2.2)
  else if a % 2 = 0 then
    -- a even, b odd: gcd a b = gcd (a/2) b
    let r := ebGcd (a / 2) b
    let x := r.2.1
    let y := r.2.2
    (r.1, if x % 2 = 0 then (x / 2, y) else ((x + (b : ℤ)) / 2, y - ((a / 2 : ℕ) : ℤ)))
  else if b % 2 = 0 then
    -- a odd, b even: gcd a b = gcd a (b/2)
    let r := ebGcd a (b / 2)
    let x := r.2.1
    let y := r.2.2
    (r.1, if y % 2 = 0 then (x, y / 2) else (x - ((b / 2 : ℕ) : ℤ), (y + (a : ℤ)) / 2))
  else if a ≤ b then
    -- both odd, a ≤ b: gcd a b = gcd a (b - a)
    let r := ebGcd a (b - a)
    (r.1, r.2.1 - r.2.2, r.2.2)
  else
    -- both odd, a > b: gcd a b = gcd (a - b) b
    let r := ebGcd (a - b) b
    (r.1, r.2.1, r.2.2 - r.2.1)
termination_by a + b
decreasing_by
  all_goals simp_wf
  all_goals omega

-- ═══════════════════════════════════════════════════════════════
-- PART II: GCD COMPONENT IS CORRECT
-- ═══════════════════════════════════════════════════════════════

/-- The first component of `ebGcd` is `Nat.gcd`.  Mirrors the grandparent
`binaryGcd_eq_gcd`: the even branches use coprimality/`gcd_mul_left`, the subtract
branches use `Nat.gcd_rec` together with `(b - a) % a = b % a`. -/
theorem ebGcd_fst (a b : ℕ) : (ebGcd a b).1 = Nat.gcd a b := by
  unfold ebGcd
  split_ifs with h1 h2 h3 h4 h5 h6 <;> dsimp only
  · simp [h1, Nat.gcd_zero_left]
  · simp [h2, Nat.gcd_zero_right]
  · obtain ⟨ha2, hb2⟩ := h3
    rw [ebGcd_fst (a / 2) (b / 2)]
    conv_rhs => rw [show a = 2 * (a / 2) from by omega,
                    show b = 2 * (b / 2) from by omega]
    exact (Nat.gcd_mul_left 2 (a / 2) (b / 2)).symm
  · have hb1 : b % 2 = 1 := by omega
    rw [ebGcd_fst (a / 2) b]
    conv_rhs => rw [show a = 2 * (a / 2) from by omega]
    exact ((Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hb1)).gcd_mul_left_cancel _).symm
  · have ha1 : a % 2 = 1 := by omega
    rw [ebGcd_fst a (b / 2), Nat.gcd_comm a (b / 2)]
    conv_rhs => rw [show b = 2 * (b / 2) from by omega]
    rw [Nat.gcd_comm a]
    exact ((Nat.coprime_two_left.mpr (Nat.odd_iff.mpr ha1)).gcd_mul_left_cancel _).symm
  · have hmod : (b - a) % a = b % a := by
      conv_rhs => rw [show b = (b - a) + a from by omega]
      rw [Nat.add_mod_right]
    rw [ebGcd_fst a (b - a), Nat.gcd_rec a (b - a), Nat.gcd_rec a b, hmod]
  · have hmod : (a - b) % b = a % b := by
      conv_rhs => rw [show a = (a - b) + b from by omega]
      rw [Nat.add_mod_right]
    rw [ebGcd_fst (a - b) b, Nat.gcd_comm (a - b) b, Nat.gcd_comm a b,
        Nat.gcd_rec b (a - b), Nat.gcd_rec b a, hmod]

-- ═══════════════════════════════════════════════════════════════
-- PART III: BÉZOUT IDENTITY (the constructive witness is correct)
-- ═══════════════════════════════════════════════════════════════

/-- **Extended Binary Bézout Identity.** The coefficients threaded through the
algorithm satisfy `a * x + b * y = gcd a b`, with `(x, y) = (ebGcd a b).2`.

Each branch closes by `linear_combination` of the inductive hypothesis with the
cast/parity facts.  In the single-even branches the carried coefficient is made
even *before* halving (`x = 2 * (x / 2)`, `x + b = 2 * ((x + b) / 2)`), and in the
subtraction branches the `ℕ → ℤ` cast of `b - a` distributes (`a ≤ b`). -/
theorem ebGcd_bezout (a b : ℕ) :
    (a : ℤ) * (ebGcd a b).2.1 + (b : ℤ) * (ebGcd a b).2.2 = ((ebGcd a b).1 : ℤ) := by
  unfold ebGcd
  split_ifs with h1 h2 h3 h4 h5 h6 <;> dsimp only
  · -- a = 0
    push_cast [h1]; ring
  · -- b = 0
    push_cast [h2]; ring
  · -- both even
    obtain ⟨ha2, hb2⟩ := h3
    have ih := ebGcd_bezout (a / 2) (b / 2)
    have ea : (a : ℤ) = 2 * ((a / 2 : ℕ) : ℤ) := by omega
    have eb : (b : ℤ) = 2 * ((b / 2 : ℕ) : ℤ) := by omega
    push_cast
    linear_combination 2 * ih + (ebGcd (a / 2) (b / 2)).2.1 * ea
      + (ebGcd (a / 2) (b / 2)).2.2 * eb
  · -- a even, b odd
    split_ifs with hx <;> dsimp only
    · -- carried x even
      have ih := ebGcd_bezout (a / 2) b
      have ea : (a : ℤ) = 2 * ((a / 2 : ℕ) : ℤ) := by omega
      have hx2 : (ebGcd (a / 2) b).2.1 = 2 * ((ebGcd (a / 2) b).2.1 / 2) := by omega
      linear_combination ih + ((ebGcd (a / 2) b).2.1 / 2) * ea
        - ((a / 2 : ℕ) : ℤ) * hx2
    · -- carried x odd
      have ih := ebGcd_bezout (a / 2) b
      have ea : (a : ℤ) = 2 * ((a / 2 : ℕ) : ℤ) := by omega
      have hxb : (ebGcd (a / 2) b).2.1 + (b : ℤ)
          = 2 * (((ebGcd (a / 2) b).2.1 + (b : ℤ)) / 2) := by omega
      linear_combination ih + (((ebGcd (a / 2) b).2.1 + (b : ℤ)) / 2) * ea
        - ((a / 2 : ℕ) : ℤ) * hxb
  · -- a odd, b even
    split_ifs with hy <;> dsimp only
    · -- carried y even
      have ih := ebGcd_bezout a (b / 2)
      have eb : (b : ℤ) = 2 * ((b / 2 : ℕ) : ℤ) := by omega
      have hy2 : (ebGcd a (b / 2)).2.2 = 2 * ((ebGcd a (b / 2)).2.2 / 2) := by omega
      linear_combination ih + ((ebGcd a (b / 2)).2.2 / 2) * eb
        - ((b / 2 : ℕ) : ℤ) * hy2
    · -- carried y odd
      have ih := ebGcd_bezout a (b / 2)
      have eb : (b : ℤ) = 2 * ((b / 2 : ℕ) : ℤ) := by omega
      have hya : (ebGcd a (b / 2)).2.2 + (a : ℤ)
          = 2 * (((ebGcd a (b / 2)).2.2 + (a : ℤ)) / 2) := by omega
      linear_combination ih + (((ebGcd a (b / 2)).2.2 + (a : ℤ)) / 2) * eb
        - ((b / 2 : ℕ) : ℤ) * hya
  · -- both odd, a ≤ b
    have ih := ebGcd_bezout a (b - a)
    have hsub : ((b - a : ℕ) : ℤ) = (b : ℤ) - (a : ℤ) := by
      rw [Nat.cast_sub h6]
    linear_combination ih - (ebGcd a (b - a)).2.2 * hsub
  · -- both odd, a > b
    have ih := ebGcd_bezout (a - b) b
    have hsub : ((a - b : ℕ) : ℤ) = (a : ℤ) - (b : ℤ) := by
      rw [Nat.cast_sub (by omega)]
    linear_combination ih - (ebGcd (a - b) b).2.1 * hsub

/-- Packaged form: the witnesses certify `Nat.gcd a b`. -/
theorem ebGcd_bezout_gcd (a b : ℕ) :
    (a : ℤ) * (ebGcd a b).2.1 + (b : ℤ) * (ebGcd a b).2.2 = (Nat.gcd a b : ℤ) := by
  rw [ebGcd_bezout, ebGcd_fst]

-- ═══════════════════════════════════════════════════════════════
-- PART IV: INTEGER EXTENSION (signs folded onto the coefficients)
-- ═══════════════════════════════════════════════════════════════

/-- Extended binary GCD over `ℤ`: reduce to `natAbs`, then push the input signs
onto the Bézout coefficients via `a.sign * a.natAbs = a`. Returns `(g, x, y)`
with `g = intBinaryGcd a b` and `a * x + b * y = g`. -/
def intExtBinaryGcd (a b : ℤ) : ℤ × ℤ × ℤ :=
  let r := ebGcd a.natAbs b.natAbs
  ((r.1 : ℤ), a.sign * r.2.1, b.sign * r.2.2)

/-- The gcd component equals the parent `intBinaryGcd`: both sides are
`↑(Nat.gcd a.natAbs b.natAbs)`, via `ebGcd_fst` and `binaryGcd_eq_gcd`. -/
theorem intExtBinaryGcd_fst (a b : ℤ) :
    (intExtBinaryGcd a b).1 = intBinaryGcd a b := by
  simp only [intExtBinaryGcd, intBinaryGcd, ebGcd_fst,
    BezoutIdentityOQ01OQ01.binaryGcd_eq_gcd]

/-- **Integer Extended Binary Bézout Identity.**
`a * (a.sign * x) + b * (b.sign * y) = |a| * x + |b| * y = g`, using
`a * a.sign = a.natAbs` (`Int.sign_mul_self_eq_natAbs`) and `ebGcd_bezout`. -/
theorem intExtBinaryGcd_bezout (a b : ℤ) :
    a * (intExtBinaryGcd a b).2.1 + b * (intExtBinaryGcd a b).2.2
      = (intExtBinaryGcd a b).1 := by
  simp only [intExtBinaryGcd]
  have hsa : a * a.sign = (a.natAbs : ℤ) := by
    rw [mul_comm]; exact Int.sign_mul_self_eq_natAbs a
  have hsb : b * b.sign = (b.natAbs : ℤ) := by
    rw [mul_comm]; exact Int.sign_mul_self_eq_natAbs b
  have key := ebGcd_bezout a.natAbs b.natAbs
  linear_combination key + (ebGcd a.natAbs b.natAbs).2.1 * hsa
    + (ebGcd a.natAbs b.natAbs).2.2 * hsb

-- ═══════════════════════════════════════════════════════════════
-- PART V: COMPUTATIONAL INSTANCES (recorded as comments)
-- ═══════════════════════════════════════════════════════════════

-- The following witnesses were checked by `decide`/`native_decide` during
-- development and are recorded here as documentation.  They are *consequences*
-- of the universally-quantified theorems above, so they are stated as comments to
-- keep this file's axiom footprint limited to the foundational three.
--
--   ebGcd 12 8 = (4, 1, -1)              -- 12·1 + 8·(-1) = 4 = gcd 12 8
--   ebGcd 17 5 = (1, 3, -10)            -- 17·3 + 5·(-10) = 1 = gcd 17 5
--   intExtBinaryGcd (-12) 8 = (4, -1, -1) -- (-12)·(-1) + 8·(-1) = 4

end BezoutIdentityOQ01OQ01OQ02OQ01
