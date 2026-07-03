/-
  A sharper lower density for ODD abundant numbers: `1/1350` instead of `1/1890`.

  `AbundantOddDensityOQ0301.lean` proves that the counting function of odd
  abundant numbers satisfies

      oddAbundantCount N  ≥  N / 1890,

  i.e. odd abundant numbers have lower density ≥ `1/1890`, using the single
  witness family `945·(2k+1)` (odd multiples of the smallest odd abundant number
  `945 = 3³·5·7`). That entry explicitly notes the constant is **not sharp**: the
  family misses every odd abundant number not divisible by `945`.

  A single-seed family can never beat spacing `1890`: `945` is the *smallest* odd
  abundant number, and requiring the multiple to stay odd forces the factor `2`.
  This file breaks the `1890` barrier by adding a **second** independent odd
  abundant seed, `1575 = 3²·5²·7` (`σ(1575) = 3224 > 3150`). Counting the union of
  the odd multiples of `945` and of `1575` — with the overlap (odd multiples of
  `lcm(945,1575) = 4725`) removed — gives, in every window of length
  `9450 = lcm·2`, exactly

      5 (odd mult. of 945)  +  3 (odd mult. of 1575)  −  1 (odd mult. of 4725)  =  7

  distinct odd abundant numbers, hence density ≥ `7/9450 = 1/1350`.

  The seven per-window residues, each written as an odd multiple of one of the two
  seeds so that oddness and abundance are immediate:

      945·1, 1575·1, 945·3, 945·5, 945·7, 1575·5, 945·9
    = 945, 1575, 2835, 4725, 6615, 7875, 8505.

  Adding `9450·w` (`= 945·10·w = 1575·6·w`) keeps each an odd multiple of its
  seed, so the map `(r, w) ↦ r + 9450·w` lands in the odd abundant numbers; it is
  injective on the residues (base-`9450` digits, since every residue is `< 9450`),
  so `[1, 9450·m]` contains at least `7·m` odd abundant numbers.

  Main results:
    * `abundant_1575`          — `1575` is abundant (kernel `decide` on `sigmaFast`).
    * `count_lower_bound_1350` — `9450·m ≤ N → 7·m ≤ oddAbundantCount N`.
    * `oddAbundantCount_ge_div_1350` — `7·(N / 9450) ≤ oddAbundantCount N`,
      i.e. lower density ≥ `1/1350`, strictly better than the parent's `1/1890`.

  The proof is axiom-free (no `sorry`, no `axiom`, no `native_decide`): abundance
  of the two seeds is a kernel `decide` on the structurally-recursive `sigmaFast`,
  and everything else is `Finset` cardinality arithmetic.
-/
import Mathlib
import Proofs.AbundantNumberOQ02
import Proofs.AbundantMultiplesOQ01
import Proofs.AbundantOddDensityOQ0301

namespace AbundantOddDensityOQ030103

open AbundantNumberOQ02 AbundantMultiplesOQ01 AbundantOddDensityOQ0301

-- Match the base file's classical decidability setup so the `Finset.filter`
-- ranging over `fun n => Odd n ∧ n.Abundant` uses the same instance as
-- `oddAbundantCount`.
attribute [local instance] Classical.propDecidable

/-! ## The second odd abundant seed -/

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
/-- **`1575 = 3²·5²·7` is abundant.** `σ(1575) = 3224 > 3150 = 2·1575`, checked by a
kernel `decide` on the structurally-recursive `sigmaFast` (no `native_decide`, so
no `Lean.ofReduceBool`). This is the second odd abundant seed, independent of the
seed `945` used by the parent entry. -/
theorem abundant_1575 : Nat.Abundant 1575 :=
  (abundant_iff_sigmaFast (by norm_num)).mpr (by decide)

/-! ## Seed multiples are odd and abundant -/

/-- `945 · c` with `c` odd is odd and abundant (`945` odd, closure under multiples). -/
private theorem odd_abundant_945_mul' (c : ℕ) (hc : Odd c) :
    Odd (945 * c) ∧ (945 * c).Abundant := by
  have hpos : 0 < c := by rcases hc with ⟨t, rfl⟩; omega
  exact ⟨(by decide : Odd 945).mul hc, abundant_mul_right abundant_945 hpos⟩

/-- `1575 · c` with `c` odd is odd and abundant (`1575` odd, closure under multiples). -/
private theorem odd_abundant_1575_mul' (c : ℕ) (hc : Odd c) :
    Odd (1575 * c) ∧ (1575 * c).Abundant := by
  have hpos : 0 < c := by rcases hc with ⟨t, rfl⟩; omega
  exact ⟨(by decide : Odd 1575).mul hc, abundant_mul_right abundant_1575 hpos⟩

/-- `c + 2·k·w` is odd whenever `c` is. -/
private theorem odd_add_even_mul (c k w : ℕ) (hc : Odd c) : Odd (c + 2 * k * w) := by
  obtain ⟨t, ht⟩ := hc
  exact ⟨t + k * w, by rw [ht]; ring⟩

/-! ## Tiling residues -/

/-- The seven per-window residues, each an odd multiple of `945` or `1575`. -/
def R : Finset ℕ := {945, 1575, 2835, 4725, 6615, 7875, 8505}

theorem R_card : R.card = 7 := by decide

/-- Every residue is `≥ 1`. -/
theorem R_pos : ∀ r ∈ R, 1 ≤ r := by decide

/-- Every residue is `< 9450`; this makes the tiling map injective on `R` (the
residues are the base-`9450` digits of the enumerated abundant numbers). -/
theorem R_lt : ∀ r ∈ R, r < 9450 := by decide

/-- **Each tiled value `r + 9450·w` (`r ∈ R`) is odd and abundant.** Writing it as
an odd multiple of one of the two seeds — `945·(c + 10w)` for the five `945`-type
residues, `1575·(c + 6w)` for the two `1575`-type — makes oddness and abundance
immediate. -/
theorem tile_odd_abundant (w : ℕ) {r : ℕ} (hr : r ∈ R) :
    Odd (r + 9450 * w) ∧ (r + 9450 * w).Abundant := by
  simp only [R, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show (945 : ℕ) + 9450 * w = 945 * (1 + 2 * 5 * w) by ring]
    exact odd_abundant_945_mul' _ (odd_add_even_mul 1 5 w (by decide))
  · rw [show (1575 : ℕ) + 9450 * w = 1575 * (1 + 2 * 3 * w) by ring]
    exact odd_abundant_1575_mul' _ (odd_add_even_mul 1 3 w (by decide))
  · rw [show (2835 : ℕ) + 9450 * w = 945 * (3 + 2 * 5 * w) by ring]
    exact odd_abundant_945_mul' _ (odd_add_even_mul 3 5 w (by decide))
  · rw [show (4725 : ℕ) + 9450 * w = 945 * (5 + 2 * 5 * w) by ring]
    exact odd_abundant_945_mul' _ (odd_add_even_mul 5 5 w (by decide))
  · rw [show (6615 : ℕ) + 9450 * w = 945 * (7 + 2 * 5 * w) by ring]
    exact odd_abundant_945_mul' _ (odd_add_even_mul 7 5 w (by decide))
  · rw [show (7875 : ℕ) + 9450 * w = 1575 * (5 + 2 * 3 * w) by ring]
    exact odd_abundant_1575_mul' _ (odd_add_even_mul 5 3 w (by decide))
  · rw [show (8505 : ℕ) + 9450 * w = 945 * (9 + 2 * 5 * w) by ring]
    exact odd_abundant_945_mul' _ (odd_add_even_mul 9 5 w (by decide))

/-! ## The sharpened counting bound -/

/-- **Sharpened core counting estimate.** If `9450·m ≤ N`, then there are at least
`7·m` odd abundant numbers in `[1, N]`.

The `7·m` values `r + 9450·w` (`r ∈ R`, `w < m`) are pairwise distinct, each odd
and abundant (`tile_odd_abundant`), and each lies in `[1, N]` — the largest,
`8505 + 9450·(m-1) < 9450·m ≤ N`. So the filtered set contains an injective image
of `R ×ˢ range m`, of cardinality `7·m`. -/
theorem count_lower_bound_1350 (N m : ℕ) (h : 9450 * m ≤ N) :
    7 * m ≤ oddAbundantCount N := by
  unfold oddAbundantCount
  -- The tiled image lands in the filtered set.
  have hsub : (R ×ˢ Finset.range m).image (fun p => p.1 + 9450 * p.2) ⊆
      (Finset.Icc 1 N).filter (fun n => Odd n ∧ n.Abundant) := by
    intro n hn
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_range] at hn
    obtain ⟨⟨r, w⟩, ⟨hr, hw⟩, rfl⟩ := hn
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, tile_odd_abundant w hr⟩
    · have := R_pos r hr; omega
    · have := R_lt r hr; omega
  -- The image has exactly `7·m` elements (the tiling map is injective on `R ×ˢ range m`).
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 + 9450 * p.2)
      (↑(R ×ˢ Finset.range m) : Set (ℕ × ℕ)) := by
    rintro ⟨r₁, w₁⟩ hp ⟨r₂, w₂⟩ hq hpq
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hp hq
    have b₁ := R_lt r₁ hp.1
    have b₂ := R_lt r₂ hq.1
    simp only [Prod.mk.injEq] at hpq ⊢
    omega
  have hcard : ((R ×ˢ Finset.range m).image (fun p => p.1 + 9450 * p.2)).card = 7 * m := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_product, R_card, Finset.card_range]
  calc 7 * m = _ := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

/-- **Sharpened linear lower bound on the counting function.**

For every `N`, the number of odd abundant numbers in `[1, N]` is at least
`7·(N / 9450)` — a lower density of `1/1350`, strictly better than the parent
entry's `1/1890`. -/
theorem oddAbundantCount_ge_div_1350 (N : ℕ) :
    7 * (N / 9450) ≤ oddAbundantCount N := by
  apply count_lower_bound_1350
  rw [Nat.mul_comm]
  exact Nat.div_mul_le_self N 9450

/-- **The new density constant strictly improves the parent's.** `1/1350 > 1/1890`. -/
theorem density_strictly_better : (1350 : ℕ) < 1890 := by decide

#check @count_lower_bound_1350
#check @oddAbundantCount_ge_div_1350

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `sorryAx`, no `Lean.ofReduceBool` (abundance of both seeds is kernel `decide`).
#print axioms abundant_1575
#print axioms count_lower_bound_1350
#print axioms oddAbundantCount_ge_div_1350

end AbundantOddDensityOQ030103
