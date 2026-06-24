import Mathlib

/-
# Burnside Counting OQ-04-OQ-01-OQ-01-OQ-01: a closed form for the rotation fixed-point count

## What this proves

The parent `burnside-counting-oq-04-oq-01-oq-01` (`BurnsideCountingOQ04OQ01OQ01.lean`)
computed the binary *bracelet* counts `b(5) = 8`, `b(6) = 13` by evaluating the Burnside
fixed-point sum `∑_{g ∈ D_n} |Fix(g)|` with kernel `decide` — a *computation*, one length at a
time. Its open question OQ-02 asks to replace that per-`n` computation by a **closed form** for
the individual fixed-point counts, the rotation part being `∑_r 2^{gcd(n,r)}`, and OQ-01 asks
for "a symbolic per-element fixed-point formula".

This file proves the generic rotation term, with no computation and uniformly in `n`:

      `Fintype.card {c : ZMod n → Fin 2 // c rotation-invariant by i} = 2 ^ gcd(n, i.val)`.

A binary colouring of the `n`-cycle fixed by the rotation `x ↦ x + i` is exactly one that is
constant on the orbits of that rotation, and the rotation `x ↦ x + i` has exactly
`gcd(n, i.val)` orbits (the index of the cyclic subgroup `⟨i⟩ ≤ ZMod n`). Hence the number of
fixed colourings is `2` raised to the number of orbits, `2 ^ gcd(n, i.val)`.

## How

* `IsRotInvariant i c` says `c (p + i) = c p` for all `p`.
* `invariant_zsmul` upgrades invariance under `+ i` to invariance under `+ k • i` for every
  integer `k` (a two-sided induction), so an invariant colouring is constant on each coset of
  the additive subgroup `zmultiples i`.
* `rotFixedEquiv` is the resulting bijection
  `{c // IsRotInvariant i c} ≃ (ZMod n ⧸ zmultiples i → Fin 2)`.
* `card_quotient_zmultiples` evaluates `|ZMod n ⧸ ⟨i⟩| = gcd(n, i.val)` via Lagrange
  (`index_mul_card`), `Nat.card_zmultiples`, and `ZMod.addOrderOf_coe` (`addOrderOf i =
  n / gcd(n, i.val)`).
* Combining, `card_rotFixed` reads off `2 ^ gcd(n, i.val)`.

As corollaries we recover the rotation sub-sums of the parent's computed Burnside totals
(`∑_{i : ZMod 5} = 40`, `∑_{i : ZMod 6} = 84`) directly from the formula, plus the two extreme
cases (`i = 0` gives `2^n`; a generator gives the `2` constant colourings).

## Honesty / Scope

Only the **rotation** half of OQ-02 is proved here; the reflection contribution (which depends
on the parity of `n` and of `i`) is left to future work — the parent still settles the full
bracelet counts computationally. Everything below is axiom-free (no `native_decide`); the
finite cross-checks `rotation_sum_five`/`rotation_sum_six` use ordinary kernel `decide` on
closed `ℕ` arithmetic. `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace BurnsideRotationFix

open AddSubgroup

/-- A binary colouring of the `n` vertices of the `n`-cycle. There are `2 ^ n` of them. -/
abbrev Coloring (n : ℕ) : Type := ZMod n → Fin 2

/-- A colouring is fixed by the rotation `x ↦ x + i` exactly when adding `i` does not change
any vertex colour. -/
def IsRotInvariant {n : ℕ} (i : ZMod n) (c : Coloring n) : Prop := ∀ p, c (p + i) = c p

instance {n : ℕ} [NeZero n] (i : ZMod n) : DecidablePred (IsRotInvariant i) := fun _ =>
  Fintype.decidableForallFintype

/-- The colourings fixed by the rotation by `i`. -/
def RotFixed (n : ℕ) (i : ZMod n) : Type := {c : Coloring n // IsRotInvariant i c}

instance {n : ℕ} [NeZero n] (i : ZMod n) : Fintype (RotFixed n i) := by
  unfold RotFixed; infer_instance

/-- Invariance under a single shift by `i` extends to invariance under shifting by any integer
multiple `k • i`. This is exactly the statement that an invariant colouring is constant on each
coset of the cyclic subgroup `⟨i⟩`. -/
theorem invariant_zsmul {n : ℕ} {i : ZMod n} {c : Coloring n} (h : IsRotInvariant i c) :
    ∀ (k : ℤ) (p : ZMod n), c (p + k • i) = c p := by
  -- The "subtract `i`" form of invariance, obtained by substituting `p ↦ p - i`.
  have hsub : ∀ p, c (p - i) = c p := fun p => by
    have h1 := h (p - i); simpa using h1.symm
  intro k
  induction k using Int.induction_on with
  | zero => intro p; simp
  | succ k ih =>
      intro p
      have e : p + (↑k + 1 : ℤ) • i = (p + (↑k : ℤ) • i) + i := by
        rw [add_zsmul, one_zsmul]; abel
      rw [e, h, ih]
  | pred k ih =>
      intro p
      have e : p + (-↑k - 1 : ℤ) • i = (p + (-↑k : ℤ) • i) - i := by
        rw [sub_zsmul, one_zsmul]; abel
      rw [e, hsub, ih]

/-- The fixed colourings of the rotation `x ↦ x + i` are in bijection with functions on the
coset space `ZMod n ⧸ ⟨i⟩`: an invariant colouring factors through the quotient, and every
function on the quotient pulls back to an invariant colouring. -/
def rotFixedEquiv {n : ℕ} (i : ZMod n) :
    RotFixed n i ≃ (ZMod n ⧸ zmultiples i → Fin 2) where
  toFun := fun c => fun q =>
    Quotient.liftOn' q c.1 (by
      intro a b hab
      rw [QuotientAddGroup.leftRel_apply] at hab
      obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hab
      have hb : b = a + k • i := by rw [hk]; abel
      rw [hb, invariant_zsmul c.2 k a])
  invFun := fun d =>
    ⟨fun p => d (QuotientAddGroup.mk p), by
      intro p
      show d (QuotientAddGroup.mk (p + i)) = d (QuotientAddGroup.mk p)
      congr 1
      rw [QuotientAddGroup.eq_iff_sub_mem]
      have e : p + i - p = i := by abel
      rw [e]
      exact mem_zmultiples i⟩
  left_inv := by
    rintro ⟨c, hc⟩; rfl
  right_inv := by
    intro d
    funext q
    induction q using Quotient.inductionOn'
    rfl

/-- The coset space of the cyclic subgroup `⟨i⟩ ≤ ZMod n` has exactly `gcd(n, i.val)` points:
the rotation `x ↦ x + i` has `gcd(n, i.val)` orbits. -/
theorem card_quotient_zmultiples {n : ℕ} [NeZero n] (i : ZMod n) :
    Fintype.card (ZMod n ⧸ zmultiples i) = Nat.gcd n i.val := by
  have hn : n ≠ 0 := NeZero.ne n
  set g : ℕ := Nat.gcd n i.val with hg
  have hgdvd : g ∣ n := Nat.gcd_dvd_left n i.val
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hn)
  -- `Nat.card ⟨i⟩ = addOrderOf i = n / g`.
  have hcardH : Nat.card (zmultiples i) = n / g := by
    rw [Nat.card_zmultiples]
    conv_lhs => rw [← ZMod.natCast_zmod_val i]
    rw [ZMod.addOrderOf_coe _ hn]
  -- Lagrange: `index · |⟨i⟩| = |ZMod n| = n`.
  have hlag := AddSubgroup.index_mul_card (zmultiples i)
  rw [hcardH, Nat.card_zmod] at hlag
  -- `index = Fintype.card (ZMod n ⧸ ⟨i⟩)`.
  have hidx : (zmultiples i).index = Fintype.card (ZMod n ⧸ zmultiples i) := by
    rw [AddSubgroup.index, Nat.card_eq_fintype_card]
  rw [hidx] at hlag
  -- Solve `card · (n / g) = n = g · (n / g)` for `card = g`.
  have hdiv_pos : 0 < n / g := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hgdvd) hgpos
  have hng : g * (n / g) = n := Nat.mul_div_cancel' hgdvd
  apply Nat.eq_of_mul_eq_mul_right hdiv_pos
  rw [hlag, hng]

/-- **Closed form for the rotation fixed-point count.** The binary colourings of the `n`-cycle
fixed by the rotation `x ↦ x + i` number exactly `2 ^ gcd(n, i.val)` — two to the number of
orbits of the rotation. No per-`n` computation. -/
theorem card_rotFixed {n : ℕ} [NeZero n] (i : ZMod n) :
    Fintype.card (RotFixed n i) = 2 ^ Nat.gcd n i.val := by
  rw [Fintype.card_congr (rotFixedEquiv i), Fintype.card_fun, Fintype.card_fin,
    card_quotient_zmultiples i]

/-! ## Corollaries -/

/-- The identity rotation (`i = 0`) fixes every one of the `2 ^ n` colourings. -/
theorem card_rotFixed_zero {n : ℕ} [NeZero n] :
    Fintype.card (RotFixed n 0) = 2 ^ n := by
  rw [card_rotFixed]; simp

/-- A rotation by a "generator" — one whose step is coprime to `n` (`gcd(n, i.val) = 1`) — fixes
exactly the `2` constant colourings. This is the clean prime-length case: for `n` prime, every
nonzero rotation is of this kind. -/
theorem card_rotFixed_of_gcd_eq_one {n : ℕ} [NeZero n] (i : ZMod n)
    (h : Nat.gcd n i.val = 1) : Fintype.card (RotFixed n i) = 2 := by
  rw [card_rotFixed, h, pow_one]

/-- Rotation part of the Burnside sum for `n = 5`: `∑_{i : ZMod 5} |Fix(r i)| = 40`, matching
the rotation contribution to the parent's computed total `fixed_sum_five = 80`. -/
theorem rotation_sum_five :
    (∑ i : ZMod 5, Fintype.card (RotFixed 5 i)) = 40 := by
  simp only [card_rotFixed]
  decide

/-- Rotation part of the Burnside sum for `n = 6`: `∑_{i : ZMod 6} |Fix(r i)| = 84`, matching
the rotation contribution to the parent's computed total `fixed_sum_six = 156`. -/
theorem rotation_sum_six :
    (∑ i : ZMod 6, Fintype.card (RotFixed 6 i)) = 84 := by
  simp only [card_rotFixed]
  decide

end BurnsideRotationFix
