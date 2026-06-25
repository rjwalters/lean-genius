/-
# Dihedral Reflection Cycle Counts: cyc(reflection) = (n+|Fix|)/2 and k^{cyc} Fixed Colorings
## (burnside-counting-oq-03-oq-02-oq-02)

**Open question** (from `burnside-counting-oq-03-oq-02`): the parent proves the
group-agnostic master formula `#(colorings fixed by g) = k ^ cyc g`, where
`cyc g = Nat.card (orbitRel.Quotient ⟨g⟩ X)` is the number of `⟨g⟩`-cycles on the
positions. The sibling `...-oq-01` specialised this to **rotations** (`cyc = gcd(n,r)`).
This leaf specialises it to **reflections**, recovering the classical dihedral reflection
counts `k^{(n+1)/2}` (odd `n`) and `k^{n/2+1}`, `k^{n/2}` (even `n`) as instances of
`k^{cyc g}`, now for *every* number of colours `k`.

A reflection acts on the `n` positions `ZMod n` by the involution `p ↦ -i - p`, realised as
the permutation `reflPerm i := Equiv.subLeft (-i) : Equiv.Perm (ZMod n)`.  Its cycle count is
computed by reading the parent's `k = 2` coloring count two ways:

* the parent's master formula gives `#(2-colorings fixed by reflPerm i) = 2 ^ cyc (reflPerm i)`;
* the sibling `BurnsideCountingOQ04OQ02OQ02.card_invariant_colorings_involutive` gives the
  same count as `2 ^ ((n + reflFix i)/2)`, because the orbits of an involution are fixed points
  (singletons) and transposed pairs, so there are `(|positions| + |fixed points|)/2` of them.

Injectivity of `2 ^ ·` yields the **cycle count**

  `cyc (reflPerm i) = (n + reflFix i) / 2`                          (`cyc_reflPerm`)

and hence, via the parent's *general-`k`* master formula,

  `#(k-colorings fixed by reflPerm i) = k ^ ((n + reflFix i) / 2)` (`card_fixedColorings_reflPerm`).

Specialising the fixed-point count `reflFix i` by parity (`reflFix_odd` / `reflFix_even`, reused
from the sibling) recovers the textbook dihedral reflection contributions for **all** `k`:

  odd  `n` :  `cyc = (n+1)/2`,  count `k^{(n+1)/2}`              (`cyc_reflPerm_odd`)
  even `n` :  `cyc ∈ {n/2+1, n/2}`,  count `k^{n/2+1}` or `k^{n/2}` (`cyc_reflPerm_even`)

This completes the general-`k` reflection half of the master formula, the dual of the sibling's
rotation half `cyc = gcd(n,r)`.

**Sorry count**: 0. **Axiom count**: 0 (only Lean/Mathlib foundational axioms).
-/

import Mathlib
import Proofs.BurnsideCountingOQ03OQ02
import Proofs.BurnsideCountingOQ04OQ02OQ02

open MulAction Finset

namespace BurnsideCountingOQ03OQ02OQ02

open BurnsideCountingOQ03OQ02 (cyc card_fixedBy_eq_pow_cyc coloring_smul_apply)
open BurnsideCountingOQ04OQ02OQ02 (refl refl_involutive reflFix reflFix_odd reflFix_even
  card_invariant_colorings_involutive)

variable {n : ℕ}

/-! ## Section I: The reflection permutation

The reflection through the axis indexed by `i` sends position `p` to `-i - p`.  This is the
involution `Equiv.subLeft (-i)`, viewed as an element of `Equiv.Perm (ZMod n)` so the parent's
`cyc`/Burnside machinery (stated for an arbitrary group element) applies directly. -/

/-- The reflection permutation of the `n` positions: `p ↦ -i - p`. -/
def reflPerm (i : ZMod n) : Equiv.Perm (ZMod n) := Equiv.subLeft (-i)

@[simp] lemma reflPerm_apply (i : ZMod n) (p : ZMod n) : reflPerm i p = -i - p :=
  Equiv.subLeft_apply _ _

/-- `reflPerm i` agrees with the sibling's position involution `refl i = (-i - ·)`. -/
lemma reflPerm_eq_refl (i : ZMod n) (p : ZMod n) : reflPerm i p = refl i p := by
  rw [reflPerm_apply]; rfl

/-- `reflPerm i` squares to the identity. -/
lemma reflPerm_mul_self (i : ZMod n) : reflPerm i * reflPerm i = 1 := by
  ext p
  simp only [Equiv.Perm.mul_apply, reflPerm_apply, Equiv.Perm.one_apply]
  ring

/-- `reflPerm i` is its own inverse (an involution). -/
@[simp] lemma reflPerm_inv (i : ZMod n) : (reflPerm i)⁻¹ = reflPerm i :=
  inv_eq_of_mul_eq_one_right (reflPerm_mul_self i)

/-- Acting by `(reflPerm i)⁻¹` on a position is the involution `refl i`. -/
lemma reflPerm_inv_smul (i : ZMod n) (p : ZMod n) : (reflPerm i)⁻¹ • p = refl i p := by
  rw [reflPerm_inv, Equiv.Perm.smul_def, reflPerm_eq_refl]

/-! ## Section II: Fixed colorings of `reflPerm i` are the `refl i`-symmetric colorings -/

/-- A `k`-coloring is fixed by `reflPerm i` (under the parent's coloring action) exactly when it
is constant on the `refl i`-orbits, i.e. symmetric about the reflection axis. -/
lemma fixedBy_reflPerm_iff {k : ℕ} (i : ZMod n) (c : ZMod n → Fin k) :
    reflPerm i • c = c ↔ ∀ p, c (refl i p) = c p := by
  constructor
  · intro h p
    have hp := congrFun h p
    rw [coloring_smul_apply, reflPerm_inv_smul] at hp
    exact hp
  · intro h
    funext p
    rw [coloring_smul_apply, reflPerm_inv_smul]
    exact h p

/-! ## Section III: The `k = 2` count, via the involution-orbit count -/

/-- **`k = 2` reflection count.**  The number of `2`-colorings fixed by `reflPerm i` is
`2 ^ ((n + reflFix i)/2)` — the sibling's involution-invariant count for `σ = refl i`. -/
lemma card_fixed_two_colorings [NeZero n] (i : ZMod n) :
    Nat.card (fixedBy (ZMod n → Fin 2) (reflPerm i)) = 2 ^ ((n + reflFix i) / 2) := by
  rw [Nat.card_eq_fintype_card]
  have e : (fixedBy (ZMod n → Fin 2) (reflPerm i))
      ≃ {c : ZMod n → Fin 2 // ∀ p, c (refl i p) = c p} :=
    Equiv.subtypeEquivRight (fun c => by rw [mem_fixedBy]; exact fixedBy_reflPerm_iff i c)
  rw [Fintype.card_congr e, card_invariant_colorings_involutive (refl i) (refl_involutive i),
    ZMod.card]
  rfl

/-! ## Section IV: The cycle count and the general-`k` reflection count -/

/-- **Reflection cycle count.**  The number of `⟨reflPerm i⟩`-orbits on the `n` positions is
`(n + reflFix i)/2`: an involution's orbits are its fixed points (singletons) and its transposed
pairs.  Obtained by injectivity of `2 ^ ·` from the two readings of the `k = 2` count. -/
theorem cyc_reflPerm [NeZero n] (i : ZMod n) :
    cyc (X := ZMod n) (reflPerm i) = (n + reflFix i) / 2 := by
  have h : (2 : ℕ) ^ cyc (X := ZMod n) (reflPerm i) = 2 ^ ((n + reflFix i) / 2) := by
    rw [← card_fixedBy_eq_pow_cyc (X := ZMod n) (k := 2) (reflPerm i), card_fixed_two_colorings]
  exact Nat.pow_right_injective (le_refl 2) h

/-- **General-`k` reflection count.**  The number of `k`-colorings fixed by the reflection
`reflPerm i` is `k ^ ((n + reflFix i)/2) = k ^ cyc (reflPerm i)`. -/
theorem card_fixedColorings_reflPerm [NeZero n] (i : ZMod n) (k : ℕ) :
    Nat.card (fixedBy (ZMod n → Fin k) (reflPerm i)) = k ^ ((n + reflFix i) / 2) := by
  rw [card_fixedBy_eq_pow_cyc (X := ZMod n) (k := k) (reflPerm i), cyc_reflPerm i]

/-! ## Section V: Parity specialisation — the textbook reflection counts -/

/-- **Odd `n`.**  Every reflection has `(n+1)/2` cycles (one fixed point plus `(n-1)/2` pairs). -/
theorem cyc_reflPerm_odd [NeZero n] (hn : Odd n) (i : ZMod n) :
    cyc (X := ZMod n) (reflPerm i) = (n + 1) / 2 := by
  rw [cyc_reflPerm i, reflFix_odd hn i]

/-- **Odd `n`, count.**  Every reflection fixes `k ^ ((n+1)/2)` colorings, for every `k`. -/
theorem card_fixedColorings_reflPerm_odd [NeZero n] (hn : Odd n) (i : ZMod n) (k : ℕ) :
    Nat.card (fixedBy (ZMod n → Fin k) (reflPerm i)) = k ^ ((n + 1) / 2) := by
  rw [card_fixedColorings_reflPerm i k, reflFix_odd hn i]

/-- **Even `n`.**  A reflection has either `n/2 + 1` cycles (axis through two vertices,
`reflFix = 2`) or `n/2` cycles (axis through two edge-midpoints, `reflFix = 0`). -/
theorem cyc_reflPerm_even [NeZero n] (hn : Even n) (i : ZMod n) :
    cyc (X := ZMod n) (reflPerm i) = n / 2 + 1 ∨ cyc (X := ZMod n) (reflPerm i) = n / 2 := by
  rw [cyc_reflPerm i]
  rcases reflFix_even hn i with h | h <;> rw [h] <;> omega

/-- **Even `n`, count.**  A reflection fixes either `k ^ (n/2+1)` or `k ^ (n/2)` colorings. -/
theorem card_fixedColorings_reflPerm_even [NeZero n] (hn : Even n) (i : ZMod n) (k : ℕ) :
    Nat.card (fixedBy (ZMod n → Fin k) (reflPerm i)) = k ^ (n / 2 + 1) ∨
      Nat.card (fixedBy (ZMod n → Fin k) (reflPerm i)) = k ^ (n / 2) := by
  rw [card_fixedColorings_reflPerm i k]
  rcases reflFix_even hn i with h | h
  · right; rw [h, Nat.add_zero]
  · left; rw [h]; congr 1; omega

#check @cyc_reflPerm
#check @card_fixedColorings_reflPerm
#check @cyc_reflPerm_odd
#check @cyc_reflPerm_even

end BurnsideCountingOQ03OQ02OQ02

-- Axiom audit: only the standard foundational axioms — no `Lean.ofReduceBool`
-- (no `native_decide`) and no `sorryAx`.
#print axioms BurnsideCountingOQ03OQ02OQ02.cyc_reflPerm
#print axioms BurnsideCountingOQ03OQ02OQ02.card_fixedColorings_reflPerm
