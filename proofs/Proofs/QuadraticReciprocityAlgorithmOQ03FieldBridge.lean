import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Tactic
import Proofs.QuadraticReciprocityAlgorithmOQ03

/-
# Field-form Zolotarev bridge — the exact OQ-pinned statement (Milestone 1 completion)

## Status

**BUILD-PENDING — BEARERS AUDITED (S21, researcher-5, 2026-06-16).** Authored under the
Docker + Aristotle blackout (`docker info` times out; Aristotle MCP `prove` returns
`"Resource not found"`), so still no machine verification. **However, every named bearer
below was re-confirmed present at the repo pin (mathlib `2df2f01` / v4.26.0) with matching
signature and correct hypothesis direction (S21 offline audit against a full mathlib4
checkout at the exact pin):**

  - `sign_subtypePerm (f) (h₁ : ∀ x, p (f x) ↔ p x) (h₂ : ∀ x, f x ≠ x → p x)` — `Sign.lean:453` ✓
  - `sign_eq_sign_of_equiv (f) (g) (e) (h : ∀ x, e (f x) = g (e x))` — `Sign.lean:467` ✓
  - `subtypePerm (f) (h : ∀ x, p (f x) ↔ p x)` — `Algebra/Group/End.lean:373`; the `h₁` here
    (`∀ x, mulLeft₀ a ha x ≠ 0 ↔ x ≠ 0`) is exactly `∀ x, p (f x) ↔ p x` with `p = (· ≠ 0)` ✓
  - `unitsEquivNeZero : G₀ˣ ≃ {a // a ≠ 0}`, `@[simps]`, `a ↦ ⟨↑a, a.ne_zero⟩` (so `.val = ↑a`
    by rfl) — `GroupWithZero/Units/Equiv.lean:27` ✓
  - `Equiv.mulLeft₀ a ha := (Units.mk0 a ha).mulLeft`, `@[simps! -fullyApplied]` (generates the
    apply lemma for the `happ` fallback) — same file `:33` ✓
  - `Units.val_mk0 : (mk0 a h : G₀) = a` (rfl-level) — `GroupWithZero/Units/Basic.lean:173` ✓
  - parent headline `legendreSym_eq_sign_mulLeft (hp : 2 < p) (u : (ZMod p)ˣ)` — call site exact ✓

The only residuals are the three documented `rfl`/defeq repair points below; each is low-risk
(`mulLeft₀`/`unitsEquivNeZero` reduce definitionally, and each has a documented `simp` fallback).
This file is **UNREGISTERED** — intentionally absent from `Proofs.lean`, so it cannot affect the
gallery auto-merge build until a Docker session verifies and registers it. Build with:

  `./proofs/scripts/docker-build.sh Proofs.QuadraticReciprocityAlgorithmOQ03FieldBridge`

## What this adds

The verified headline in `QuadraticReciprocityAlgorithmOQ03.lean`
(`legendreSym_eq_sign_mulLeft`) states Zolotarev's lemma on the **units group**:
`legendreSym p (u.val) = sign (Equiv.mulLeft u)` for `u : (ZMod p)ˣ`. The exact statement
the open question pins uses `Equiv.mulLeft₀ a ha` on the **field** `ZMod p` (which fixes 0):

  `legendreSym p (a.val) = sign (Equiv.mulLeft₀ a ha)`,   `a : ZMod p`, `a ≠ 0`.

This file derives that field form from the verified units form via the **fixed-point sign
bridge**: `mulLeft₀ a` fixes `0` and permutes the nonzero residues, so its sign equals the
sign of its restriction to the nonzero subtype (`sign_subtypePerm`), and that restriction is
intertwined with `mulLeft u` on the units group by `unitsEquivNeZero` (`sign_eq_sign_of_equiv`).

## Numerical certificate

`research/problems/quadratic-reciprocity-algorithm-oq-03/verify_field_bridge.py`
certifies (A) the bridge `sign(mulLeft₀ a) = sign(mulLeft u)`, (B) the field-form Zolotarev
identity `sign(mulLeft₀ a) = legendreSym(a,p)`, (C) the `sign_subtypePerm` hypotheses
(`mulLeft₀ a` fixes 0, moves only nonzeros), and (D) the `unitsEquivNeZero` intertwining —
all for every odd prime `3 ≤ p < 80` and every nonzero `a` (768 (p,a) pairs, all pass).

## Bearers (pinned @ mathlib rev `2df2f01` / v4.26.0)

- `Equiv.Perm.sign_subtypePerm (f) (h₁) (h₂) : sign (f.subtypePerm h₁) = sign f`
  — `Mathlib/GroupTheory/Perm/Sign.lean:453`.
- `Equiv.Perm.sign_eq_sign_of_equiv (f) (g) (e) (h) : sign f = sign g`
  — same file `:467` (intertwining equiv ⇒ equal signs).
- `unitsEquivNeZero : G₀ˣ ≃ {a : G₀ // a ≠ 0}` (`@[simps]`)
  — `Mathlib/Algebra/GroupWithZero/Units/Equiv.lean:27`.
- `Equiv.mulLeft₀ (a) (ha) : Perm G₀` `:= (Units.mk0 a ha).mulLeft` (`@[simps! -fullyApplied]`)
  — same file `:33` (note: `mulLeft₀ a ha x = a * x` is the relevant unfolding).
- verified `QuadraticReciprocityAlgorithmOQ03.legendreSym_eq_sign_mulLeft`.

## Repair points for the Docker session (most-likely build adjustments)

1. `happ : Equiv.mulLeft₀ a ha x = a * x` is asserted `rfl`. If `rfl` fails, replace with
   `by simp [Equiv.mulLeft₀]` or the `@[simps]`-generated `Equiv.mulLeft₀_apply`.
2. `(unitsEquivNeZero z).val = ↑z` and `(↑(Units.mk0 a ha) : ZMod p) = a` are used at `rfl`/
   `Units.val_mk0` level; if the `Subtype.ext` step does not close, add
   `simp [unitsEquivNeZero, Equiv.subtypePerm_apply, Units.val_mul, Units.val_mk0]`.
3. The `sign_subtypePerm` `h₂` (moved point ⇒ nonzero) discharge may need `Equiv.mulLeft₀`
   unfolded before `simp`/`omega`.
-/

namespace QuadraticReciprocityAlgorithmOQ03

open Equiv Equiv.Perm

/-- **Field-form Zolotarev's lemma** (the exact OQ-pinned statement). For an odd prime `p`
and `a : ZMod p` with `a ≠ 0`, the Legendre symbol equals the sign of left-multiplication by
`a` viewed as a permutation of the whole field `ZMod p` (which fixes `0`):
`legendreSym p a.val = sign (Equiv.mulLeft₀ a ha)`.

Derived from the verified units-form headline `legendreSym_eq_sign_mulLeft` via the
fixed-point sign bridge. **BUILD-PENDING / UNVERIFIED** (authored under blackout, S18). -/
theorem legendreSym_eq_sign_mulLeft₀ {p : ℕ} [Fact p.Prime] (hp : 2 < p)
    {a : ZMod p} (ha : a ≠ 0) :
    legendreSym p ((a).val : ℤ) = (Equiv.Perm.sign (Equiv.mulLeft₀ a ha) : ℤ) := by
  -- the unit corresponding to `a`
  set u : (ZMod p)ˣ := Units.mk0 a ha with hu
  have huv : (u : ZMod p) = a := Units.val_mk0 ha
  -- pointwise unfolding of `mulLeft₀`
  have happ : ∀ x : ZMod p, Equiv.mulLeft₀ a ha x = a * x := fun x => rfl
  -- the subtype predicate is `· ≠ 0`; `mulLeft₀ a` preserves it
  have h₁ : ∀ x : ZMod p, (Equiv.mulLeft₀ a ha x ≠ 0) ↔ (x ≠ 0) := by
    intro x
    rw [happ, mul_ne_zero_iff]
    exact ⟨fun h => h.2, fun h => ⟨ha, h⟩⟩
  -- STEP 1: dropping the fixed point `0` preserves the sign
  have hstep1 : Equiv.Perm.sign ((Equiv.mulLeft₀ a ha).subtypePerm h₁)
        = Equiv.Perm.sign (Equiv.mulLeft₀ a ha) := by
    apply Equiv.Perm.sign_subtypePerm
    intro x hx
    -- if `mulLeft₀ a` moves `x` then `x ≠ 0` (since it fixes `0`)
    intro hx0
    apply hx
    rw [hx0, happ, mul_zero]
  -- STEP 2: the restriction is intertwined with `mulLeft u` by `unitsEquivNeZero`
  have hstep2 : Equiv.Perm.sign (Equiv.mulLeft u)
        = Equiv.Perm.sign ((Equiv.mulLeft₀ a ha).subtypePerm h₁) := by
    apply Equiv.Perm.sign_eq_sign_of_equiv _ _ (unitsEquivNeZero (G₀ := ZMod p))
    intro y
    apply Subtype.ext
    -- value equality: `↑(u * y) = mulLeft₀ a ha ↑y = a * ↑y`
    show ((u * y : (ZMod p)ˣ) : ZMod p) = Equiv.mulLeft₀ a ha (y : ZMod p)
    rw [happ, Units.val_mul, huv]
  -- assemble: units-form headline + the two sign steps
  have hhead : legendreSym p ((u : ZMod p).val : ℤ)
        = (Equiv.Perm.sign (Equiv.mulLeft u) : ℤ) :=
    legendreSym_eq_sign_mulLeft hp u
  rw [hstep2, hstep1] at hhead
  rw [huv] at hhead
  exact hhead

end QuadraticReciprocityAlgorithmOQ03
