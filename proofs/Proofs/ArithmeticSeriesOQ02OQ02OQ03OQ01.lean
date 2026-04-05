/-
# Pólya Enumeration Theorem: Necklace Counting via Cyclic Group Actions

Addresses OQ-01 from ArithmeticSeriesOQ02OQ02OQ03: "Can the generating function
approach be extended to prove Pólya's enumeration theorem?"

## Main Results

1. **`cyclic_add_action`** — The cyclic group ZMod n acts on ZMod-indexed colorings
   via rotation, with a clean axiom-free proof using ZMod subtraction.
2. **Fixed-point counts** — |Fix(r)| = k^(gcd(r.val, n)) for ZMod n acting on
   k-colorings. Proved by `decide` for concrete small cases.
3. **`burnside_binary_4`** — There are exactly 6 distinct binary necklaces of
   length 4. Proved using Burnside's lemma from Mathlib.
4. **`polya_formula_CN_2colors`** — The Pólya formula for C_n on 2-colorings:
   n · |Necklaces(n,2)| = Σ_{d|n} φ(d) · 2^(n/d). Verified for n = 2,3,4,6.
5. **`necklace_count_formula`** — Explicit necklace counts for small n by `decide`.

## Mathematical Background

**Pólya's Enumeration Theorem** (1937): For a group G acting on a set X, the number
of distinct colorings (orbits under G) using k colors is the cycle index Z(G) evaluated
at all f_j = k:

  Z(G; k, k, ...) = (1/|G|) Σ_{g ∈ G} k^(number of cycles of g)

For the cyclic group C_n = ZMod n acting on n-bead necklaces, rotation by r has
gcd(r, n) cycles (each of length n/gcd(r,n)), so:

  Z(C_n; k) = (1/n) Σ_{r=0}^{n-1} k^(gcd(r,n))
             = (1/n) Σ_{d|n} φ(d) · k^(n/d)   [grouping by gcd value d = n/gcd(r,n)]

Wait, let d = gcd(r,n). Then the number of r in [0,n) with gcd(r,n) = d equals φ(n/d).
So Z(C_n; k) = (1/n) Σ_{d|n} φ(n/d) · k^d.

Setting m = n/d: Z(C_n; k) = (1/n) Σ_{m|n} φ(m) · k^(n/m).

## Key Clean Insight

Using `ZMod n → Fin k` as colorings (instead of `Fin n → Fin k`) gives a clean,
axiom-free group action: rotation by r sends coloring c to `fun i => c (i - r)`.
The action law `(r + s) +ᵥ c = r +ᵥ (s +ᵥ c)` follows immediately from ZMod algebra.

## References

- G. Pólya (1937): "Kombinatorische Anzahlbestimmungen für Gruppen, Graphen und
  chemische Verbindungen", Acta Mathematica 68, 145–254.
- Burnside's lemma (also: Cauchy-Frobenius lemma): |X/G| = (1/|G|) Σ_{g} |Fix(g)|.
-/

import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.GroupTheory.GroupAction.Quotient
set_option maxHeartbeats 400000

namespace PolyaEnumeration

open Finset MulAction

/-
## Part I: Clean Group Action via ZMod Subtraction

Using ZMod n → Fin k avoids modular arithmetic technicalities.
The rotation action is: (r +ᵥ c) i = c (i - r).
The action law follows from associativity of subtraction in ZMod n.
-/
section CyclicAction

/-- A ZMod-indexed coloring: assigns one of k colors to each of n positions,
    indexed by ZMod n for clean algebraic manipulation. -/
abbrev ZColoring (n k : ℕ) := ZMod n → Fin k

/-- Rotation by r: sends position i to position i − r, equivalently,
    the rotated coloring at position i uses the color from position i − r
    in the original coloring. -/
def rotateZColoring (n k : ℕ) (r : ZMod n) (c : ZColoring n k) : ZColoring n k :=
  fun i => c (i - r)

/-- The cyclic group ZMod n acts on ZColoring n k by rotation.
    **No axioms needed**: the action law is `sub_sub` in ZMod n. -/
instance cyclicAction (n k : ℕ) [NeZero n] : AddAction (ZMod n) (ZColoring n k) where
  vadd r c i := c (i - r)
  zero_vadd c := by
    funext i
    show c (i - 0) = c i
    simp
  add_vadd r s c := by
    funext i
    show c (i - (r + s)) = c ((i - r) - s)
    rw [sub_sub]

/-- A ZColoring is fixed by rotation r iff c is periodic with period r,
    i.e., c (i - r) = c i for all positions i. -/
def IsRotFixed (n k : ℕ) [NeZero n] (r : ZMod n) (c : ZColoring n k) : Prop :=
  r +ᵥ c = c

instance (n k : ℕ) [NeZero n] (r : ZMod n) : DecidablePred (@IsRotFixed n k _ r) :=
  fun c => decidable_of_iff (∀ i, c (i - r) = c i)
    ⟨fun h => funext h, fun h i => congrFun h i⟩

end CyclicAction

/-
## Part II: Fixed-Point Counts for Specific Cyclic Groups

For ZMod 4 acting on ZColoring 4 2 (binary 4-necklaces), we compute
|Fix(r)| for each r ∈ ZMod 4.

- Fix(0): all 16 colorings (identity fixes everything)
- Fix(1): colorings with c(i-1) = c(i) for all i → all same color → 2
- Fix(2): colorings with c(i-2) = c(i) for all i → period divides 2 → 4
- Fix(3): same structure as Fix(1) → 2

Total fixed points = 16 + 2 + 4 + 2 = 24. By Burnside: 24/4 = 6 necklaces.
-/
section FixedPointCounts

/-- Total colorings of ZMod 4 with 2 colors: 2^4 = 16. -/
theorem zcoloring_4_2_card : Fintype.card (ZColoring 4 2) = 16 := by
  simp [ZColoring, ZMod, Fintype.card_fun, Fintype.card_fin]

/-- Fixed by 0 (identity): all colorings, count = 16. -/
theorem fix_0_card : Fintype.card { c : ZColoring 4 2 // IsRotFixed 4 2 0 c } = 16 := by
  have : ∀ c : ZColoring 4 2, IsRotFixed 4 2 0 c := by
    intro c
    simp [IsRotFixed, rotateZColoring]
  have : {c : ZColoring 4 2 // IsRotFixed 4 2 0 c} ≃ ZColoring 4 2 :=
    { toFun := fun ⟨c, _⟩ => c
      invFun := fun c => ⟨c, this c⟩
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr this]
  exact zcoloring_4_2_card

/-- Fixed by 1 (rotation by 90°): 2 colorings (all-0 and all-1). -/
theorem fix_1_card : Fintype.card { c : ZColoring 4 2 // IsRotFixed 4 2 1 c } = 2 := by
  native_decide

/-- Fixed by 2 (rotation by 180°): 4 colorings (period divides 2). -/
theorem fix_2_card : Fintype.card { c : ZColoring 4 2 // IsRotFixed 4 2 2 c } = 4 := by
  native_decide

/-- Fixed by 3 (rotation by 270°): 2 colorings. -/
theorem fix_3_card : Fintype.card { c : ZColoring 4 2 // IsRotFixed 4 2 3 c } = 2 := by
  native_decide

/-- Sum of fixed-point counts = 24. -/
theorem fixed_point_sum_4_2 :
    Fintype.card { c : ZColoring 4 2 // IsRotFixed 4 2 0 c } +
    Fintype.card { c : ZColoring 4 2 // IsRotFixed 4 2 1 c } +
    Fintype.card { c : ZColoring 4 2 // IsRotFixed 4 2 2 c } +
    Fintype.card { c : ZColoring 4 2 // IsRotFixed 4 2 3 c } = 24 := by
  rw [fix_0_card, fix_1_card, fix_2_card, fix_3_card]

end FixedPointCounts

/-
## Part III: Burnside's Lemma — Distinct 4-Necklace Count

By Burnside's lemma: |Necklaces| = (1/|G|) · Σ_{g ∈ G} |Fix(g)|
For ZMod 4 on ZColoring 4 2: |Necklaces| = 24 / 4 = 6.

The orbit quotient `orbitRel.Quotient (ZMod 4) (ZColoring 4 2)` is the set
of distinct necklaces. We show it has exactly 6 elements.
-/
section BurnsideApplication

/-- The cyclic group ZMod n acts on ZColoring n k by multiplicative action,
    derived from the additive cyclicAction. -/
instance cyclicMulAction (n k : ℕ) [NeZero n] : MulAction (Multiplicative (ZMod n)) (ZColoring n k) :=
  Multiplicative.mulAction

/-- Noncomputable Fintype for orbit quotients: follows from finiteness of X. -/
noncomputable instance fintypeOrbitRelQuotient (G X : Type*) [Group G] [Fintype X]
    [MulAction G X] : Fintype (orbitRel.Quotient G X) := by
  classical
  exact Fintype.ofSurjective (Quotient.mk (orbitRel G X))
    (fun q => q.inductionOn fun x => ⟨x, rfl⟩)

/-- There are exactly 6 distinct binary necklaces of length 4.
    Proved via Burnside's lemma: fixed-point sum 24 = 6 × 4. -/
theorem binary_4_necklace_count :
    Fintype.card (orbitRel.Quotient (Multiplicative (ZMod 4)) (ZColoring 4 2)) = 6 := by
  have hb := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (Multiplicative (ZMod 4)) (ZColoring 4 2)
  have h1 : ∑ g : Multiplicative (ZMod 4),
      Fintype.card (MulAction.fixedBy (ZColoring 4 2) g) = 24 := by decide
  have h2 : Fintype.card (Multiplicative (ZMod 4)) = 4 := by decide
  -- Use .trans to avoid rw binder-name mismatch (Burnside uses ∑ a while h1 uses ∑ g)
  have h3 : Fintype.card (orbitRel.Quotient (Multiplicative (ZMod 4)) (ZColoring 4 2)) * 4 = 24 := by
    have key := hb.symm.trans h1
    rw [h2] at key; exact key
  omega

end BurnsideApplication

/-
## Part IV: Pólya Formula Verification

The Pólya formula for C_n on 2-colorings:
  n · |Necklaces(n, 2)| = Σ_{d|n} φ(d) · 2^(n/d)

We verify this for n = 2, 3, 4, 6 by norm_num, using Euler's totient values:
- φ(1) = 1, φ(2) = 1, φ(3) = 2, φ(6) = 2
-/
section PolyaFormula

/-- Euler's totient values for small n (provable by decide). -/
theorem totient_1 : Nat.totient 1 = 1 := by native_decide
theorem totient_2 : Nat.totient 2 = 1 := by native_decide
theorem totient_3 : Nat.totient 3 = 2 := by native_decide
theorem totient_4 : Nat.totient 4 = 2 := by native_decide
theorem totient_6 : Nat.totient 6 = 2 := by native_decide

/-- Pólya formula for C_2 (2 beads, 2 colors):
    2 · 3 = φ(1)·2^2 + φ(2)·2^1 = 1·4 + 1·2 = 6. -/
theorem polya_C2_2colors :
    2 * 3 = Nat.totient 1 * 2^2 + Nat.totient 2 * 2^1 := by
  rw [totient_1, totient_2]; norm_num

/-- Pólya formula for C_3 (3 beads, 2 colors):
    3 · 4 = φ(1)·2^3 + φ(3)·2^1 = 1·8 + 2·2 = 12. -/
theorem polya_C3_2colors :
    3 * 4 = Nat.totient 1 * 2^3 + Nat.totient 3 * 2^1 := by
  rw [totient_1, totient_3]; norm_num

/-- Pólya formula for C_4 (4 beads, 2 colors):
    4 · 6 = φ(1)·2^4 + φ(2)·2^2 + φ(4)·2^1 = 1·16 + 1·4 + 2·2 = 24. -/
theorem polya_C4_2colors :
    4 * 6 = Nat.totient 1 * 2^4 + Nat.totient 2 * 2^2 + Nat.totient 4 * 2^1 := by
  rw [totient_1, totient_2, totient_4]; norm_num

/-- Pólya formula for C_6 (6 beads, 2 colors):
    6 · 14 = φ(1)·2^6 + φ(2)·2^3 + φ(3)·2^2 + φ(6)·2^1
           = 1·64 + 1·8 + 2·4 + 2·2 = 84. -/
theorem polya_C6_2colors :
    6 * 14 = Nat.totient 1 * 2^6 + Nat.totient 2 * 2^3 +
             Nat.totient 3 * 2^2 + Nat.totient 6 * 2^1 := by
  rw [totient_1, totient_2, totient_3, totient_6]; norm_num

/-- The necklace count formula for k colors and n beads
    (Pólya, using the divisor sum over Euler totient). -/
noncomputable def necklaceCount (n k : ℕ) [NeZero n] : ℕ :=
  Fintype.card (orbitRel.Quotient (Multiplicative (ZMod n)) (ZMod n → Fin k))

/-- Helper: apply Burnside to get necklace count from fixed-point sum. -/
private theorem necklace_via_burnside (n k c : ℕ) [NeZero n]
    (hfp : ∑ g : Multiplicative (ZMod n),
        Fintype.card (MulAction.fixedBy (ZMod n → Fin k) g) = c * n)
    (hg : Fintype.card (Multiplicative (ZMod n)) = n) :
    necklaceCount n k = c := by
  unfold necklaceCount
  have hb := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (Multiplicative (ZMod n)) (ZMod n → Fin k)
  -- Use .trans to avoid rw binder-name mismatch (Burnside uses ∑ a while hfp uses ∑ g).
  -- No local haveI: both hb and hfp must use the same Fintype instance.
  have key := hb.symm.trans hfp
  rw [hg] at key
  exact Nat.mul_right_cancel (NeZero.pos n) key

/-- Necklace counts for 2 colors, proved via Burnside's lemma. -/
theorem necklaces_2_2 : necklaceCount 2 2 = 3 :=
  necklace_via_burnside 2 2 3 (by native_decide) (by native_decide)

theorem necklaces_3_2 : necklaceCount 3 2 = 4 :=
  necklace_via_burnside 3 2 4 (by native_decide) (by native_decide)

theorem necklaces_4_2 : necklaceCount 4 2 = 6 := by
  unfold necklaceCount; exact binary_4_necklace_count

theorem necklaces_5_2 : necklaceCount 5 2 = 8 :=
  necklace_via_burnside 5 2 8 (by native_decide) (by native_decide)

theorem necklaces_6_2 : necklaceCount 6 2 = 14 :=
  necklace_via_burnside 6 2 14 (by native_decide) (by native_decide)

end PolyaFormula

/-
## Part V: The Pólya Enumeration Theorem (General Statement)

The general theorem connecting the orbit count to the cycle index.
The full proof requires the cycle structure theorem (Burnside applied to all group
elements), which we state axiomatically here.

The key intermediate result we DO prove:
- The divisibility: n | Σ_{d|n} φ(d) · k^(n/d) (for k ≥ 0)
  This is a consequence of Burnside's lemma (the sum of fixed-point counts
  is a multiple of |G|), but we prove it for specific small n by decide.
-/
section GeneralStatement

/-- The divisibility n | 2^n + 2·... is implied by the Pólya formula. -/
theorem polya_C2_divisibility : 2 ∣ (2^2 + 2^1) := by norm_num
theorem polya_C3_divisibility : 3 ∣ (2^3 + 2 * 2^1) := by norm_num
theorem polya_C4_divisibility : 4 ∣ (2^4 + 2^2 + 2 * 2^1) := by norm_num
theorem polya_C6_divisibility : 6 ∣ (2^6 + 2^3 + 2 * 2^2 + 2 * 2^1) := by norm_num

/-- The general Pólya enumeration theorem for cyclic groups:
    For any n ≥ 1 and k ≥ 0 colors, the number of k-colorings of an n-bead necklace
    (under cyclic rotation) equals:
    (1/n) Σ_{d|n} φ(d) · k^(n/d)

    Equivalently (without division):
    n · |Necklaces(n, k)| = Σ_{d|n} φ(d) · k^(n/d)

    This follows from Burnside's lemma applied to the ZMod n action,
    using the cycle structure: rotation by r has gcd(r.val, n) cycles
    each of length n/gcd(r.val, n). -/
theorem polya_enumeration_theorem_CN (n k : ℕ) [NeZero n] [NeZero k] :
    n * necklaceCount n k =
      ∑ d ∈ Nat.divisors n, Nat.totient d * k ^ (n / d) := by
  -- The proof connects:
  -- 1. Burnside's lemma: n * |Orbits| = Σ_{r : ZMod n} |Fix(r)|
  -- 2. Cycle structure: |Fix(r)| = k^(gcd(r.val, n))
  -- 3. Grouping: Σ_{r : ZMod n} k^(gcd(r.val, n)) = Σ_{d|n} φ(n/d) · k^d
  --                                                  = Σ_{d|n} φ(d) · k^(n/d)
  -- Full formalization requires Mathlib's Nat.totient sum formula and
  -- the cycle structure theorem for cyclic group actions.
  sorry

end GeneralStatement

/-
## Part VI: Connection to Generating Functions

The generating function approach from ArithmeticSeriesOQ02OQ02OQ03 (parallel Vandermonde
via PowerSeries) can in principle be extended to Pólya enumeration.

For binary necklaces (k = 2), the generating function is:
  P(x) = Σ_{n≥1} |Necklaces(n, 2)| · x^n

The Pólya formula gives a closed form involving the totient-weighted sum.

The connection to the parallel Vandermonde identity (which counts lattice paths via
convolutions) would arise from the fact that the cycle index of C_n in the ring of
formal power series has a product formula related to cyclotomic polynomials.

This deeper connection remains an open question.
-/
section GeneratingFunctionConnection

/-- The first few values of the binary necklace generating function:
    |Necklaces(n, 2)| for n = 1, 2, 3, 4, 5, 6. -/
def necklaceSeq : List ℕ := [2, 3, 4, 6, 8, 14]

/-- The necklace sequence matches the Pólya formula values. -/
theorem necklaceSeq_matches :
    necklaceSeq = [necklaceCount 1 2, necklaceCount 2 2, necklaceCount 3 2,
                   necklaceCount 4 2, necklaceCount 5 2, necklaceCount 6 2] := by
  have h1 : necklaceCount 1 2 = 2 :=
    necklace_via_burnside 1 2 2 (by native_decide) (by native_decide)
  simp only [necklaceSeq, h1, necklaces_2_2, necklaces_3_2, necklaces_4_2,
             necklaces_5_2, necklaces_6_2]

end GeneratingFunctionConnection

#check @cyclicAction
#check @binary_4_necklace_count
#check @polya_C4_2colors
#check @polya_enumeration_theorem_CN

end PolyaEnumeration
