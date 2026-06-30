import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Tactic
import Proofs.QuadraticReciprocityAlgorithmOQ03

/-
# Field-form Zolotarev bridge — the exact OQ-pinned statement (Milestone 1 completion)

## Status

**VERIFIED (machine-checked, 2026-06-25, researcher-1).** Compiled single-file with the host
toolchain off cached Mathlib oleans (`lake env lean`, Lean v4.26.0 / mathlib `2df2f01`) —
Docker still down, but this file imports only Mathlib + the verified parent and needs no
Docker. `#print axioms` on `legendreSym_eq_sign_mulLeft₀` reports
`[propext, Classical.choice, Quot.sound]` only: **0 sorries, 0 axioms, no
`native_decide`/`sorryAx`.**

The one repair beyond the S18/S21 blind transcription was at the two `subtypePerm` call
sites: higher-order unification could not infer the subtype predicate `p` from the
bidirectional hypothesis `h₁` alone (the elaborator left it a metavariable `?m` and the
whole term silently collapsed to `sorryAx`). Fixed by supplying the predicate explicitly,
`subtypePerm (p := fun x : ZMod p => x ≠ 0) h₁`. The `rfl`/defeq points #1 and #3 below held
as written. Now registered in `Proofs.lean`. Rebuild under Docker with:

  `./proofs/scripts/docker-build.sh Proofs.QuadraticReciprocityAlgorithmOQ03FieldBridge`

Bearers re-confirmed at the pin (S21 offline audit; all now exercised by the compile):

  - `sign_subtypePerm (f) (h₁ : ∀ x, p (f x) ↔ p x) (h₂ : ∀ x, f x ≠ x → p x)` — `Sign.lean:453` ✓
  - `sign_eq_sign_of_equiv (f) (g) (e) (h : ∀ x, e (f x) = g (e x))` — `Sign.lean:467` ✓
  - `subtypePerm (f) (h : ∀ x, p (f x) ↔ p x)` — `Algebra/Group/End.lean:373` (predicate `p`
    must be supplied explicitly — see above) ✓
  - `unitsEquivNeZero : G₀ˣ ≃ {a // a ≠ 0}`, `@[simps]`, `a ↦ ⟨↑a, a.ne_zero⟩` ✓
  - `Equiv.mulLeft₀ a ha := (Units.mk0 a ha).mulLeft` ✓
  - `Units.val_mk0 : (mk0 a h : G₀) = a` (rfl-level) ✓
  - parent headline `legendreSym_eq_sign_mulLeft (hp : 2 < p) (u : (ZMod p)ˣ)` ✓

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

## Build history (resolved at verification)

The actual repair (2026-06-25) was none of the three anticipated `rfl`/defeq points — those
held as written. The single blocker was predicate inference at the two `subtypePerm` call
sites (`p` left as a metavariable ⇒ silent `sorryAx`), fixed by `(p := fun x : ZMod p => x ≠ 0)`.
Anticipated points (all confirmed already correct):
1. `happ : Equiv.mulLeft₀ a ha x = a * x` — `rfl` held.
2. `Subtype.ext` value equality via `Units.val_mk0` — held.
3. `sign_subtypePerm` `h₂` (moved point ⇒ nonzero) discharge — held.
-/

namespace QuadraticReciprocityAlgorithmOQ03

open Equiv Equiv.Perm

/-- **Field-form Zolotarev's lemma** (the exact OQ-pinned statement). For an odd prime `p`
and `a : ZMod p` with `a ≠ 0`, the Legendre symbol equals the sign of left-multiplication by
`a` viewed as a permutation of the whole field `ZMod p` (which fixes `0`):
`legendreSym p a.val = sign (Equiv.mulLeft₀ a ha)`.

Derived from the verified units-form headline `legendreSym_eq_sign_mulLeft` via the
fixed-point sign bridge. **VERIFIED** (`lake env lean`, 2026-06-25; 0 sorry / 0 axiom). -/
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
  have hstep1 : Equiv.Perm.sign ((Equiv.mulLeft₀ a ha).subtypePerm (p := fun x : ZMod p => x ≠ 0) h₁)
        = Equiv.Perm.sign (Equiv.mulLeft₀ a ha) := by
    apply Equiv.Perm.sign_subtypePerm
    intro x hx
    -- if `mulLeft₀ a` moves `x` then `x ≠ 0` (since it fixes `0`)
    intro hx0
    apply hx
    rw [hx0, happ, mul_zero]
  -- STEP 2: the restriction is intertwined with `mulLeft u` by `unitsEquivNeZero`
  have hstep2 : Equiv.Perm.sign (Equiv.mulLeft u)
        = Equiv.Perm.sign ((Equiv.mulLeft₀ a ha).subtypePerm (p := fun x : ZMod p => x ≠ 0) h₁) := by
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
