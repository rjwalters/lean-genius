import Mathlib
import Proofs.AutomorphicNumberOQ01
import Proofs.AutomorphicNumberOQ01OQ02

/-!
# Automorphic numbers lift uniquely: the reduction tower of idempotents

## What This Proves

The parent files describe the four `k`-digit automorphic residues
`n ^ 2 ≡ n (mod 10 ^ k)` — equivalently the four idempotents `e * e = e` of
`ZMod (10 ^ k)` — by **counting** them (`AutomorphicNumberOQ01`: there are exactly
four; `…OQ01OQ01`: in general `2 ^ ω(n)`) and by describing their **pairing**
(`…OQ01OQ02`: they are `0, 1` and a complementary pair `a, 1 - a` with distinct last
digits).  What none of them explains is the *tower* structure: **why** the automorphic
numbers grow one digit at a time, each `k`-digit automorphic number extending uniquely
to a `(k+1)`-digit one (`5 → 25 → 625 → 0625 → …`, `6 → 76 → 376 → …`).

This file supplies that missing structural layer.  Write
`red k : ZMod (10 ^ (k+1)) →+* ZMod (10 ^ k)` for the canonical digit-dropping ring
homomorphism (reduction modulo `10 ^ k`).  The results:

* **`map_idem`** — any ring homomorphism sends idempotents to idempotents, so `red k`
  maps the four `(k+1)`-digit automorphic residues into the `k`-digit ones.
* **`ker_red_nilpotent`** — the kernel of `red k` is a **nil** ideal: every `x` with
  `red k x = 0` is a multiple of `10 ^ k`, hence `x ^ 2 = 0`.  (This is where the
  doubly-exponential vanishing `(10 ^ k) ^ 2 = 0` in `ZMod (10 ^ (k+1))` enters.)
* **`red_injOn_idem`** — therefore `red k` is **injective** on idempotents: two
  idempotents with the same reduction differ by a nilpotent, so are equal
  (`idem_eq_of_sub_nilpotent`, from the parent).
* **`red_image_idem`** — since both idempotent sets have exactly four elements
  (`automorphic_idempotent_count`) and `red k` is injective on them, the image is the
  *whole* lower set: `red k` is a **bijection** between the two four-element idempotent
  sets.
* **`unique_digit_extension`** (main theorem) — consequently every `k`-digit automorphic
  residue `ē` has a **unique** `(k+1)`-digit automorphic residue lying above it.  This is
  the precise sense in which `5, 25, 625, …` is a single coherent sequence, and the
  reason the two non-trivial automorphic towers converge to the two non-trivial
  idempotents of the `10`-adic integers `ℤ₁₀ ≅ ℤ₂ × ℤ₅`.

## Status

Fully machine-checked: `0` sorries, `0` axioms.  Builds on the verified parent files
`AutomorphicNumberOQ01` and `AutomorphicNumberOQ01OQ02`.
-/

namespace AutomorphicNumberOQ01OQ03

open Finset

/-! ## The digit-dropping reduction homomorphism -/

/-- The canonical reduction `ZMod (10 ^ (k+1)) →+* ZMod (10 ^ k)` — "drop the leading
digit".  Concretely it sends a residue mod `10 ^ (k+1)` to its class mod `10 ^ k`. -/
def red (k : ℕ) : ZMod (10 ^ (k + 1)) →+* ZMod (10 ^ k) :=
  ZMod.castHom (pow_dvd_pow 10 (Nat.le_succ k)) (ZMod (10 ^ k))

/-- A ring homomorphism sends idempotents to idempotents. -/
theorem map_idem {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {e : R}
    (he : e * e = e) : f e * f e = f e := by
  rw [← map_mul, he]

/-! ## The kernel of `red` is a nil ideal -/

/-- **The kernel of `red k` is nilpotent.**  If `red k x = 0` then `x` is a multiple of
`10 ^ k`, and since `(10 ^ k) ^ 2 = 10 ^ (2k) = 0` in `ZMod (10 ^ (k+1))` (for `k ≥ 1`),
already `x ^ 2 = 0`.  This is the structural fact that makes idempotent lifting unique. -/
theorem ker_red_nilpotent (k : ℕ) (hk : 0 < k) {x : ZMod (10 ^ (k + 1))}
    (hx : red k x = 0) : IsNilpotent x := by
  haveI : NeZero ((10 : ℕ) ^ (k + 1)) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero ((10 : ℕ) ^ k) := ⟨pow_ne_zero _ (by norm_num)⟩
  -- Lift `x` to a natural number `m`.
  obtain ⟨m, rfl⟩ := (ZMod.natCast_rightInverse (n := 10 ^ (k + 1))).surjective x
  -- `red` commutes with `Nat.cast`, so the hypothesis says `10 ^ k ∣ m`.
  rw [map_natCast, ZMod.natCast_eq_zero_iff] at hx
  obtain ⟨t, rfl⟩ := hx
  -- `x ^ 2 = (10 ^ k * t) ^ 2 = 0` because `10 ^ (k+1) ∣ (10 ^ k * t) ^ 2`.
  refine ⟨2, ?_⟩
  rw [show ((((10 : ℕ) ^ k * t : ℕ)) : ZMod (10 ^ (k + 1))) ^ 2
        = (((10 : ℕ) ^ k * t) ^ 2 : ℕ) from by push_cast; ring]
  rw [ZMod.natCast_eq_zero_iff]
  have hle : k + 1 ≤ 2 * k := by omega
  refine dvd_trans (pow_dvd_pow 10 hle) ⟨t ^ 2, ?_⟩
  rw [mul_pow, ← pow_mul, Nat.mul_comm k 2]

/-! ## Reduction is a bijection on idempotents -/

/-- **`red k` is injective on idempotents.**  Two idempotents with the same reduction
differ by a nilpotent (their difference lies in the nil kernel), hence are equal. -/
theorem red_injOn_idem (k : ℕ) (hk : 0 < k) {e f : ZMod (10 ^ (k + 1))}
    (he : e * e = e) (hf : f * f = f) (h : red k e = red k f) : e = f := by
  have hker : red k (e - f) = 0 := by rw [map_sub, h, sub_self]
  exact AutomorphicNumberOQ01OQ02.idem_eq_of_sub_nilpotent he hf
    (ker_red_nilpotent k hk hker)

/-- **`red k` is a bijection on idempotents.**  The image under `red k` of the four
`(k+1)`-digit automorphic residues is *exactly* the four `k`-digit ones.  Injectivity
(`red_injOn_idem`) plus equal cardinality (`automorphic_idempotent_count`, both `4`)
forces the image to fill the whole target set. -/
theorem red_image_idem (k : ℕ) (hk : 0 < k) :
    (univ.filter (fun e : ZMod (10 ^ (k + 1)) => e * e = e)).image (red k)
      = univ.filter (fun e : ZMod (10 ^ k) => e * e = e) := by
  apply Finset.eq_of_subset_of_card_le
  · -- image lands inside the lower idempotent set
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨e, he, rfl⟩ := hy
    rw [mem_filter] at he ⊢
    exact ⟨mem_univ _, map_idem (red k) he.2⟩
  · -- lower set (card 4) is no bigger than the image (card 4, by injectivity)
    have hinj : Set.InjOn (red k)
        (univ.filter (fun e : ZMod (10 ^ (k + 1)) => e * e = e) : Finset _) := by
      intro e he f hf h
      simp only [Finset.coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at he hf
      exact red_injOn_idem k hk he hf h
    rw [Finset.card_image_of_injOn hinj,
        AutomorphicNumberOQ01.automorphic_idempotent_count k hk,
        AutomorphicNumberOQ01.automorphic_idempotent_count (k + 1) (by omega)]

/-! ## Main theorem: unique digit-by-digit extension -/

/-- **Main theorem — unique digit extension.**  Every `k`-digit automorphic residue `ē`
(idempotent of `ZMod (10 ^ k)`) is the reduction of a **unique** `(k+1)`-digit automorphic
residue `e` (idempotent of `ZMod (10 ^ (k+1))`).  Thus the automorphic numbers form a
single coherent tower `5 → 25 → 625 → …`, `6 → 76 → 376 → …`, converging to the two
non-trivial idempotents of the `10`-adic integers. -/
theorem unique_digit_extension (k : ℕ) (hk : 0 < k) {ē : ZMod (10 ^ k)} (hē : ē * ē = ē) :
    ∃! e : ZMod (10 ^ (k + 1)), e * e = e ∧ red k e = ē := by
  -- `ē` lies in the lower idempotent set, hence in the image of the reduction.
  have hmem : ē ∈ univ.filter (fun e : ZMod (10 ^ k) => e * e = e) := by
    rw [mem_filter]; exact ⟨mem_univ _, hē⟩
  rw [← red_image_idem k hk, Finset.mem_image] at hmem
  obtain ⟨e, he, hred⟩ := hmem
  rw [mem_filter] at he
  refine ⟨e, ⟨he.2, hred⟩, ?_⟩
  rintro e' ⟨he', hred'⟩
  exact red_injOn_idem k hk he' he.2 (by rw [hred', hred])

/-! ## Concrete extensions

The reduction really does send each `(k+1)`-digit automorphic number to the `k`-digit one
below it, in line with `unique_digit_extension`: `25 ↦ 5`, `625 ↦ 25`, `76 ↦ 6`,
`376 ↦ 76`.  (Here `ZMod.castHom` is reduction; we verify the underlying values.) -/

/-- `25` (mod `100`) reduces to `5` (mod `10`), and both are idempotent. -/
example : (red 1) (25 : ZMod (10 ^ 2)) = (5 : ZMod (10 ^ 1)) := by decide

/-- `76` (mod `100`) reduces to `6` (mod `10`). -/
example : (red 1) (76 : ZMod (10 ^ 2)) = (6 : ZMod (10 ^ 1)) := by decide

/-- `625` (mod `1000`) reduces to `25` (mod `100`). -/
example : (red 2) (625 : ZMod (10 ^ 3)) = (25 : ZMod (10 ^ 2)) := by decide

end AutomorphicNumberOQ01OQ03
