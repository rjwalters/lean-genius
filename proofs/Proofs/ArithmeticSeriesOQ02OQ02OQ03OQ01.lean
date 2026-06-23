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
import Proofs.BurnsideCountingOQ03
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
-- Bridge: (r +ᵥ c) i = c (i - r) by cyclicAction.vadd definition.
-- Used to make the vadd reduction explicit for the elaborator.
private lemma vadd_apply (n k : ℕ) [NeZero n] (r : ZMod n) (c : ZColoring n k) (i : ZMod n) :
    (r +ᵥ c) i = c (i - r) := rfl

-- Helper: |fixedBy (ZMod n → Fin k) (ofAdd r)| = k^gcd(n, r.val).
-- Proof: substitute n = n'+1 so ZMod (n'+1) = Fin (n'+1) definitionally, then
-- apply polya_cyclic_fixed_count. The fixedBy predicate (ofAdd r) • c = c
-- kernel-reduces (via cyclicAction) to ∀ i, c(i-r) = c(i) = IsFixed n k r c.
private lemma fixedBy_card_eq_polya (n k : ℕ) [NeZero n] (r : ZMod n) :
    Fintype.card (MulAction.fixedBy (ZMod n → Fin k) (Multiplicative.ofAdd r)) =
    k ^ Nat.gcd n r.val := by
  -- Unfold n = n'+1 so ZMod (n'+1) = Fin (n'+1) definitionally (by ZMod definition)
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := NeZero.pos n; omega⟩
  -- Step 1a: fixedBy (smul) ≃ {c // IsRotFixed (vadd)}.
  -- cyclicMulAction = Multiplicative.mulAction, so (ofAdd r) • c = r +ᵥ c = IsRotFixed.
  -- Identity equiv: predicates are definitionally equal ((ofAdd r) • c = r +ᵥ c via mulAction.smul).
  have hstep1 : Fintype.card (MulAction.fixedBy (ZMod (n'+1) → Fin k) (Multiplicative.ofAdd r)) =
      Fintype.card {c : ZMod (n'+1) → Fin k // IsRotFixed (n'+1) k r c} :=
    Fintype.card_congr {
      toFun := fun ⟨c, hc⟩ => ⟨c, hc⟩
      invFun := fun ⟨c, hc⟩ => ⟨c, hc⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl
    }
  -- Step 1b: {c // IsRotFixed (r +ᵥ c = c)} ≃ {c // IsFixed (∀ i, c i = c(i-r))}.
  -- IsRotFixed c = (r +ᵥ c = c); cyclicAction.vadd r c i := c (i - r) definitionally.
  -- congrFun hc i : (r +ᵥ c) i = c i reduces to c (i - r) = c i; .symm gives IsFixed.
  -- ZMod (n'+1) = Fin (n'+1) definitionally, but the elaborator can't unify predicates automatically.
  -- Bridge explicitly: toFun converts ZMod-domain c to Fin-domain c' = fun i => c ⟨i.val, i.isLt⟩.
  -- Predicate proof uses vadd_apply + proof irrelevance for the membership proof in ⟨...⟩.
  have hstep2 : Fintype.card {c : ZMod (n'+1) → Fin k // IsRotFixed (n'+1) k r c} =
      Fintype.card {c : Fin (n'+1) → Fin k // BurnsideCountingOQ03.IsFixed (n'+1) k r c} :=
    Fintype.card_congr {
      toFun := fun ⟨c, hc⟩ =>
        ⟨fun (i : Fin (n'+1)) => c ⟨i.val, i.isLt⟩,
         fun i => by
           have hi := (congrFun hc (⟨i.val, i.isLt⟩ : ZMod (n'+1))).symm
           rw [vadd_apply (n'+1) k r c ⟨i.val, i.isLt⟩] at hi
           -- hi : c ⟨i.val, i.isLt⟩ = c (⟨i.val, i.isLt⟩ - r)
           -- goal : c ⟨i.val, i.isLt⟩ = c ⟨(↑i + (n'+1) - ↑r) % (n'+1), _⟩
           -- (⟨i.val, i.isLt⟩ - r : ZMod (n'+1)) has .val = (i.val + (n'+1) - r.val) % (n'+1)
           -- so they're Fin.ext-equal; proof irrelevance handles the membership proof
           exact hi.trans (congrArg c (Fin.ext (by
             -- Goal: (⟨i.val,_⟩ - r : ZMod (n'+1)).val = (i.val + (n'+1) - r.val) % (n'+1)
             change (⟨i.val, i.isLt⟩ - r : ZMod (n'+1)).val = (i.val + (n'+1) - r.val) % (n'+1)
             have hr : r.val < n' + 1 := ZMod.val_lt r
             have hval : (⟨i.val, i.isLt⟩ - r : ZMod (n'+1)).val =
                 ((n' + 1 - r.val) + i.val) % (n' + 1) := Fin.coe_sub ⟨i.val, i.isLt⟩ r
             rw [hval]; congr 1; omega)))⟩
      invFun := fun ⟨c, hc⟩ =>
        ⟨fun (i : ZMod (n'+1)) => c ⟨i.val, ZMod.val_lt i⟩,
         funext (fun (i : ZMod (n'+1)) => by
           rw [vadd_apply (n'+1) k r (fun j => c ⟨j.val, ZMod.val_lt j⟩) i]
           -- goal : c ⟨(i - r).val, _⟩ = c ⟨i.val, _⟩
           -- hc ⟨i.val, _⟩ : c ⟨i.val, _⟩ = c ⟨(i.val + (n'+1) - r.val) % (n'+1), _⟩
           have h := (hc ⟨i.val, ZMod.val_lt i⟩).symm
           -- h : c ⟨(i.val + (n'+1) - r.val) % (n'+1), _⟩ = c ⟨i.val, _⟩
           -- Prove ⟨(i-r).val, _⟩ = ⟨(i.val+(n'+1)-r.val)%(n'+1), _⟩ as Fin (n'+1)
           -- using Fin.val_sub: (i-r).val = ((n'+1-r.val)+i.val)%(n'+1), then omega.
           have heq : (⟨(i - r).val, ZMod.val_lt (i - r)⟩ : Fin (n'+1)) =
               ⟨(i.val + (n'+1) - r.val) % (n'+1), Nat.mod_lt _ (Nat.succ_pos n')⟩ :=
             Fin.ext (by
               -- Normalize to (i - r : ZMod (n'+1)).val = (i.val + (n'+1) - r.val) % (n'+1)
               change (i - r : ZMod (n'+1)).val = (i.val + (n'+1) - r.val) % (n'+1)
               have hr : r.val < n' + 1 := ZMod.val_lt r
               have hval : (i - r : ZMod (n'+1)).val =
                   ((n' + 1 - r.val) + i.val) % (n' + 1) := Fin.coe_sub i r
               rw [hval]; congr 1; omega)
           exact (congrArg c heq).trans h)⟩
      left_inv := fun ⟨c, _⟩ => Subtype.ext (funext fun i => congrArg c (Fin.ext rfl))
      right_inv := fun ⟨c, _⟩ => Subtype.ext (funext fun i => congrArg c (Fin.ext rfl))
    }
  -- Step 2: polya_cyclic_fixed_count gives card({...}) = k^gcd(r.val, n'+1), then gcd_comm.
  rw [hstep1, hstep2, Nat.gcd_comm]
  exact BurnsideCountingOQ03.polya_cyclic_fixed_count (n' + 1) k r

theorem polya_enumeration_theorem_CN (n k : ℕ) [NeZero n] [NeZero k] :
    n * necklaceCount n k =
      ∑ d ∈ Nat.divisors n, Nat.totient d * k ^ (n / d) := by
  have hn : 0 < n := NeZero.pos n
  -- Burnside's lemma: ∑ g, |Fix(g)| = necklaceCount * |G|
  have hburnside := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (Multiplicative (ZMod n)) (ZMod n → Fin k)
  have hGcard : Fintype.card (Multiplicative (ZMod n)) = n := by
    simp [Fintype.card_multiplicative, ZMod.card]
  -- Step 2: n * necklaceCount = ∑ r : ZMod n, k^gcd(n, r.val)
  -- Avoid rw [← hGcard] which has a motive issue (n appears in NeZero n).
  -- Build the sum equivalence directly and chain via linarith.
  have step2 : n * necklaceCount n k = ∑ r : ZMod n, k ^ Nat.gcd n r.val := by
    unfold necklaceCount
    -- ∑ r : ZMod n, k^gcd(n,r.val) = ∑ g : Mult(ZMod n), |Fix g|
    have sum_eq : ∑ r : ZMod n, k ^ Nat.gcd n r.val =
        ∑ g : Multiplicative (ZMod n), Fintype.card (MulAction.fixedBy (ZMod n → Fin k) g) :=
      Fintype.sum_equiv
        (⟨Multiplicative.ofAdd, Multiplicative.toAdd, fun _ => rfl, fun _ => rfl⟩ :
          ZMod n ≃ Multiplicative (ZMod n))
        (fun r => k ^ Nat.gcd n r.val)
        (fun g => Fintype.card (MulAction.fixedBy (ZMod n → Fin k) g))
        (fun r => (fixedBy_card_eq_polya n k r).symm)
    -- Chain: ∑ r, k^gcd = ∑ g, |Fix g| = |orbits| * |G| = |orbits| * n
    have h := sum_eq.trans hburnside
    rw [hGcard] at h
    linarith [mul_comm n (Fintype.card (orbitRel.Quotient (Multiplicative (ZMod n)) (ZMod n → Fin k)))]
  -- Step 3: ∑ r : ZMod n, k^gcd(n, r.val) = ∑ d | n, φ(n/d) · k^d
  -- polya_sum_identity uses Fin n with gcd(r.val, n); need explicit equiv ZMod n ≃ Fin n
  -- (Fintype instances differ even though ZMod n = Fin n definitionally).
  have step3 : ∑ r : ZMod n, k ^ Nat.gcd n r.val =
      ∑ d ∈ Nat.divisors n, Nat.totient (n / d) * k ^ d := by
    have h := BurnsideCountingOQ03.polya_sum_identity n k hn
    -- h : ∑ r : Fin n, k^gcd(r.val, n) = ∑ d | n, φ(n/d) · k^d
    -- Build equiv ZMod n ≃ Fin n: toFun r = ⟨r.val, val_lt r⟩, invFun i = (i.val : ZMod n)
    calc ∑ r : ZMod n, k ^ Nat.gcd n r.val
        = ∑ r : ZMod n, k ^ Nat.gcd r.val n :=
          Finset.sum_congr rfl (fun r _ => congr_arg (k ^ ·) (Nat.gcd_comm n r.val))
      _ = ∑ r : Fin n, k ^ Nat.gcd r.val n := by
          apply Fintype.sum_equiv
            (⟨fun r => ⟨r.val, ZMod.val_lt r⟩, fun i => (i.val : ZMod n),
              fun r => by simp [ZMod.natCast_val],
              fun i => Fin.ext (by simp [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt])⟩ :
              ZMod n ≃ Fin n)
          intro r
          rfl
      _ = ∑ d ∈ Nat.divisors n, Nat.totient (n / d) * k ^ d := h
  -- Step 4: Reindex d ↦ n/d (involution on divisors): ∑ d | n, φ(n/d)·k^d = ∑ d | n, φ(d)·k^(n/d)
  have step4 : ∑ d ∈ Nat.divisors n, Nat.totient (n / d) * k ^ d =
      ∑ d ∈ Nat.divisors n, Nat.totient d * k ^ (n / d) := by
    apply Finset.sum_nbij (fun d => n / d)
    · -- n/d is a divisor of n when d | n
      intro d hd
      simp only [Nat.mem_divisors] at hd ⊢
      exact ⟨Nat.div_dvd_of_dvd hd.1, hd.2⟩
    · -- n/d is injective: n/d₁ = n/d₂ → d₁ = d₂, using n/(n/d) = d
      -- heq comes as (fun d => n/d) d₁ = (fun d => n/d) d₂ (un-beta-reduced); use have to reduce
      intro d₁ hd₁ d₂ hd₂ heq
      simp only [Finset.mem_coe, Nat.mem_divisors] at hd₁ hd₂
      have heq' : n / d₁ = n / d₂ := heq  -- beta-reduce the lambda
      calc d₁ = n / (n / d₁) := (Nat.div_div_self hd₁.1 hd₁.2).symm
        _ = n / (n / d₂) := by rw [heq']
        _ = d₂ := Nat.div_div_self hd₂.1 hd₂.2
    · -- Surjective: goal is d ∈ (fun d => n/d) '' ↑(Nat.divisors n) (set-image form)
      intro d hd
      -- hd : d ∈ ↑(Nat.divisors n) as set membership; convert to Finset membership first
      have hd' := Nat.mem_divisors.mp (Finset.mem_coe.mp hd)
      refine ⟨n / d, ?_, Nat.div_div_self hd'.1 hd'.2⟩
      simp only [Finset.mem_coe, Nat.mem_divisors]
      exact ⟨Nat.div_dvd_of_dvd hd'.1, hd'.2⟩
    · -- Value equality: φ(n/d)·k^d = φ(d)·k^(n/d) since n/(n/d) = d
      intro d hd
      simp only [Nat.mem_divisors] at hd
      simp [Nat.div_div_self hd.1 hd.2]
  exact step2.trans (step3.trans step4)

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
