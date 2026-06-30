import Mathlib
import Proofs.AutomorphicNumberOQ01
import Proofs.AutomorphicNumberOQ01OQ01
import Proofs.AutomorphicNumberOQ01OQ02
import Proofs.AutomorphicNumberOQ01OQ03

/-!
# The automorphic idempotent tower over an arbitrary base

## What This Proves

The parent file `AutomorphicNumberOQ01OQ03` establishes, for the *concrete* base `10`, that
the idempotents of `ZMod (10 ^ k)` — the `k`-digit automorphic residues — form a coherent
**tower**: the digit-dropping reduction `ZMod (10 ^ (k+1)) →+* ZMod (10 ^ k)` is a bijection
between the two four-element idempotent sets, so every `k`-digit automorphic number extends
uniquely to a `(k+1)`-digit one (`5 → 25 → 625 → …`).  Sibling `…OQ01OQ01` proves the count
is `2 ^ ω(n)` for *every* modulus `n`.

This file removes the special role of `10`: it proves the same tower structure over an
**arbitrary base** `m`.  Write `red m k : ZMod (m ^ (k+1)) →+* ZMod (m ^ k)` for the
canonical reduction.  The results, all uniform in `m`:

* **`idem_card`** — for `k ≥ 1` the modulus `m ^ k` has exactly `2 ^ ω(m)` idempotents.
  (The exponent is `ω(m)`, *not* `ω(m ^ k)`: a prime power has the same prime support as its
  base, `Nat.primeFactors_pow`.  This is what makes every level of the tower have the *same*
  number of idempotents, the combinatorial reason a bijection can exist.)
* **`ker_red_nilpotent`** — the kernel of `red m k` is a nil ideal: any `x` with
  `red m k x = 0` is a multiple of `m ^ k`, hence `x ^ 2 = 0` in `ZMod (m ^ (k+1))` because
  `m ^ (k+1) ∣ (m ^ k) ^ 2 = m ^ (2k)` once `k ≥ 1` — independent of `m`.
* **`red_injOn_idem`** — `red m k` is therefore injective on idempotents (two idempotents
  with equal reduction differ by a nilpotent, so coincide: `idem_eq_of_sub_nilpotent`).
* **`red_image_idem`** — injectivity together with the *equal* cardinality `2 ^ ω(m)` at
  both levels forces the image to be the whole lower idempotent set: `red m k` is a
  **bijection** on idempotents.
* **`unique_digit_extension`** (main theorem) — consequently every `k`-digit automorphic
  residue mod `m ^ k` lifts to a **unique** `(k+1)`-digit one mod `m ^ (k+1)`.  Thus for
  *every* base `m ≥ 1` the automorphic residues organize into `2 ^ ω(m)` coherent threads
  converging to the `2 ^ ω(m)` idempotents of the `m`-adic integers
  `ℤ_m ≅ ∏_{p ∣ m} ℤ_p`.

The base-`10` parent is the case `ω(10) = 2`, giving `2 ^ 2 = 4` threads.

## Status

Fully machine-checked: `0` sorries, `0` axioms, no `native_decide`.  Reuses the
ring-generic lemmas `AutomorphicNumberOQ01OQ02.idem_eq_of_sub_nilpotent` and
`AutomorphicNumberOQ01OQ03.map_idem`, and the general count
`AutomorphicNumberOQ01OQ01.idempotent_count`.
-/

namespace AutomorphicNumberOQ01OQ03OQ01

open Finset

/-! ## The digit-dropping reduction homomorphism over base `m` -/

/-- The canonical reduction `ZMod (m ^ (k+1)) →+* ZMod (m ^ k)` — "drop the leading
base-`m` digit".  It sends a residue mod `m ^ (k+1)` to its class mod `m ^ k`. -/
def red (m k : ℕ) : ZMod (m ^ (k + 1)) →+* ZMod (m ^ k) :=
  ZMod.castHom (pow_dvd_pow m (Nat.le_succ k)) (ZMod (m ^ k))

/-! ## Every level of the tower has the same idempotent count `2 ^ ω(m)` -/

/-- **The level count.**  For `k ≥ 1` the ring `ZMod (m ^ k)` has exactly `2 ^ ω(m)`
idempotents.  This is the general count `idempotent_count` specialized to `n = m ^ k`,
together with `ω(m ^ k) = ω(m)` (`Nat.primeFactors_pow`). -/
theorem idem_card {m : ℕ} [NeZero m] (k : ℕ) (hk : 0 < k) :
    (univ.filter (fun e : ZMod (m ^ k) => e * e = e)).card = 2 ^ m.primeFactors.card := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  rw [← Fintype.card_subtype (fun e : ZMod (m ^ k) => e * e = e),
      ← Nat.card_eq_fintype_card,
      AutomorphicNumberOQ01OQ01.idempotent_count _ (pow_pos hm k),
      Nat.primeFactors_pow m hk.ne']

/-! ## The kernel of `red` is a nil ideal -/

/-- **The kernel of `red m k` is nilpotent.**  If `red m k x = 0` then `x` is a multiple of
`m ^ k`, and since `(m ^ k) ^ 2 = m ^ (2k) = 0` in `ZMod (m ^ (k+1))` (for `k ≥ 1`),
already `x ^ 2 = 0`.  This is the structural fact that makes idempotent lifting unique. -/
theorem ker_red_nilpotent {m : ℕ} [NeZero m] (k : ℕ) (hk : 0 < k)
    {x : ZMod (m ^ (k + 1))} (hx : red m k x = 0) : IsNilpotent x := by
  -- Lift `x` to a natural number `c`.
  obtain ⟨c, rfl⟩ := (ZMod.natCast_rightInverse (n := m ^ (k + 1))).surjective x
  -- `red` commutes with `Nat.cast`, so the hypothesis says `m ^ k ∣ c`.
  rw [red, map_natCast, ZMod.natCast_eq_zero_iff] at hx
  obtain ⟨t, rfl⟩ := hx
  -- `x ^ 2 = (m ^ k * t) ^ 2 = 0` because `m ^ (k+1) ∣ (m ^ k * t) ^ 2`.
  refine ⟨2, ?_⟩
  rw [show (((m ^ k * t : ℕ)) : ZMod (m ^ (k + 1))) ^ 2
        = ((m ^ k * t) ^ 2 : ℕ) from by push_cast; ring]
  rw [ZMod.natCast_eq_zero_iff]
  have hle : k + 1 ≤ 2 * k := by omega
  refine dvd_trans (pow_dvd_pow m hle) ⟨t ^ 2, ?_⟩
  rw [mul_pow, ← pow_mul, Nat.mul_comm k 2]

/-! ## Reduction is a bijection on idempotents -/

/-- **`red m k` is injective on idempotents.**  Two idempotents with the same reduction
differ by a nilpotent (their difference lies in the nil kernel), hence are equal. -/
theorem red_injOn_idem {m : ℕ} [NeZero m] (k : ℕ) (hk : 0 < k)
    {e f : ZMod (m ^ (k + 1))} (he : e * e = e) (hf : f * f = f)
    (h : red m k e = red m k f) : e = f := by
  have hker : red m k (e - f) = 0 := by rw [map_sub, h, sub_self]
  exact AutomorphicNumberOQ01OQ02.idem_eq_of_sub_nilpotent he hf
    (ker_red_nilpotent k hk hker)

/-- **`red m k` is a bijection on idempotents.**  The image under `red m k` of the
`(k+1)`-digit automorphic residues is *exactly* the `k`-digit ones.  Injectivity
(`red_injOn_idem`) plus equal cardinality (`idem_card`, both `2 ^ ω(m)`) forces the image to
fill the whole target set. -/
theorem red_image_idem {m : ℕ} [NeZero m] (k : ℕ) (hk : 0 < k) :
    (univ.filter (fun e : ZMod (m ^ (k + 1)) => e * e = e)).image (red m k)
      = univ.filter (fun e : ZMod (m ^ k) => e * e = e) := by
  apply Finset.eq_of_subset_of_card_le
  · -- image lands inside the lower idempotent set
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨e, he, rfl⟩ := hy
    rw [mem_filter] at he ⊢
    exact ⟨mem_univ _, AutomorphicNumberOQ01OQ03.map_idem (red m k) he.2⟩
  · -- lower set (card `2 ^ ω(m)`) is no bigger than the image (same card, by injectivity)
    have hinj : Set.InjOn (red m k)
        (univ.filter (fun e : ZMod (m ^ (k + 1)) => e * e = e) : Finset _) := by
      intro e he f hf h
      simp only [Finset.coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at he hf
      exact red_injOn_idem k hk he hf h
    rw [Finset.card_image_of_injOn hinj,
        idem_card k hk, idem_card (k + 1) (by omega)]

/-! ## Main theorem: unique digit-by-digit extension over base `m` -/

/-- **Main theorem — unique digit extension.**  Every `k`-digit automorphic residue `ē`
(idempotent of `ZMod (m ^ k)`) is the reduction of a **unique** `(k+1)`-digit automorphic
residue `e` (idempotent of `ZMod (m ^ (k+1))`).  Thus, for every base `m ≥ 1`, the
automorphic residues form `2 ^ ω(m)` coherent towers converging to the `2 ^ ω(m)`
idempotents of the `m`-adic integers. -/
theorem unique_digit_extension {m : ℕ} [NeZero m] (k : ℕ) (hk : 0 < k)
    {ē : ZMod (m ^ k)} (hē : ē * ē = ē) :
    ∃! e : ZMod (m ^ (k + 1)), e * e = e ∧ red m k e = ē := by
  -- `ē` lies in the lower idempotent set, hence in the image of the reduction.
  have hmem : ē ∈ univ.filter (fun e : ZMod (m ^ k) => e * e = e) := by
    rw [mem_filter]; exact ⟨mem_univ _, hē⟩
  rw [← red_image_idem k hk, Finset.mem_image] at hmem
  obtain ⟨e, he, hred⟩ := hmem
  rw [mem_filter] at he
  refine ⟨e, ⟨he.2, hred⟩, ?_⟩
  rintro e' ⟨he', hred'⟩
  exact red_injOn_idem k hk he' he.2 (by rw [hred', hred])

/-! ## Concrete bases beyond `10`

The structure is genuinely base-independent.  We read off the number of coherent towers for
several bases directly from `idem_card` (the count is `2 ^ ω(m)`, with `ω` the number of
distinct prime divisors): squarefree or prime-power, only the *prime support* matters. -/

/-- Base `6 = 2·3` has `ω = 2`, so `4` automorphic towers — like base `10`. -/
theorem towers_base_six (k : ℕ) (hk : 0 < k) :
    (univ.filter (fun e : ZMod (6 ^ k) => e * e = e)).card = 4 := by
  rw [idem_card (m := 6) k hk,
      show (6 : ℕ) = 2 * 3 from rfl,
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.Prime.primeFactors (by norm_num : Nat.Prime 2),
      Nat.Prime.primeFactors (by norm_num : Nat.Prime 3)]
  decide

/-- Base `12 = 2²·3` has the same prime support `{2, 3}`, so also `4` towers — the extra
factor of `2` does **not** add a tower. -/
theorem towers_base_twelve (k : ℕ) (hk : 0 < k) :
    (univ.filter (fun e : ZMod (12 ^ k) => e * e = e)).card = 4 := by
  rw [idem_card (m := 12) k hk,
      show (12 : ℕ) = 2 ^ 2 * 3 from rfl,
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_prime_pow (by norm_num) (by norm_num : Nat.Prime 2),
      Nat.Prime.primeFactors (by norm_num : Nat.Prime 3)]
  decide

/-- Base `30 = 2·3·5` has `ω = 3`, so `8` automorphic towers. -/
theorem towers_base_thirty (k : ℕ) (hk : 0 < k) :
    (univ.filter (fun e : ZMod (30 ^ k) => e * e = e)).card = 8 := by
  rw [idem_card (m := 30) k hk,
      show (30 : ℕ) = 2 * (3 * 5) from rfl,
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.Prime.primeFactors (by norm_num : Nat.Prime 2),
      Nat.Prime.primeFactors (by norm_num : Nat.Prime 3),
      Nat.Prime.primeFactors (by norm_num : Nat.Prime 5)]
  decide

/-- A prime base `m = 7` has a *single* nontrivial structure: `ω(7) = 1`, so only
`2 ^ 1 = 2` idempotents (`0` and `1`) at every level — no nontrivial automorphic numbers,
matching the fact that `ZMod (7 ^ k)` is local. -/
theorem towers_base_prime {p : ℕ} [NeZero p] (hp : p.Prime) (k : ℕ) (hk : 0 < k) :
    (univ.filter (fun e : ZMod (p ^ k) => e * e = e)).card = 2 := by
  rw [idem_card (m := p) k hk, hp.primeFactors]
  simp

end AutomorphicNumberOQ01OQ03OQ01
