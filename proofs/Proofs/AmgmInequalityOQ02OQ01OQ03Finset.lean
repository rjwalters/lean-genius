/-
  Newton–Girard k=3, CONCRETE general-Finset form:
      p₃ = e₁³ − 3·e₁·e₂ + 3·e₃
  with the elementary symmetric sums defined directly over a `Finset s` via
  `powersetCard` (the parent's concrete style), NOT the `MvPolynomial` API.

  Open Question (amgm-inequality-oq-02-oq-01-oq-03), concrete Finset target.

  Lineage:
  • Parent   amgm-inequality-oq-02-oq-01             : k=2 split (∑f)² = ∑f² + Σ_{i≠j} fᵢfⱼ.
  • Sibling  amgm-inequality-oq-02-oq-01-oq-02-oq-01 : the recurrence p₃ = e₁p₂ − e₂p₁ + 3e₃,
                                                       and `psum_two_eq` (p₂ = e₁² − 2e₂).
  • Universal amgm-inequality-oq-02-oq-01-oq-03       : `psum_three_closed` over MvPolynomial,
                                                       valid for every CommRing.

  ───────────────────────────────────────────────────────────────────────────
  RESOLUTION — Route B (aeval bridge), fully general over any CommRing.

  A previous iteration assembled the closed form from three concrete-Finset facts
      (L2) cube_partition :  e₁³ = p₃ + 3·Doff + 6·e₃
      (L3) D_collapse     :  Doff = e₁·p₂ − p₃
      (L4)+(k=2)          :  p₂ = e₁² − 2·e₂
  and found that combining them yields only `2·p₃ = 2·(e₁³ − 3e₁e₂ + 3e₃)` (the **char-2
  obstruction**: over a ring with 2-torsion the factor 2 is a zero-divisor, so Route A
  closes only when 2 is cancellable).

  This file removes that restriction.  The key lemmas `e2_bridge`/`e3_bridge`/`p3_bridge`
  identify the concrete `powersetCard`/power-sum definitions over a `Finset s` with the
  evaluation (`MvPolynomial.aeval`) of `MvPolynomial.esymm`/`MvPolynomial.psum` on the
  subtype `{x // x ∈ s}`.  Transporting the proven universal identities `psum_two_eq` and
  `psum_three_closed` across that bridge gives `p2_closed` and `p3_closed` over **any**
  CommRing.  The combinatorial facts L2 (`cube_partition`) and L4 (`two_e2_eq_offPairs`)
  then follow as algebraic corollaries — char 2 included.

  Bridge ingredients (Mathlib):
    • `MvPolynomial.aeval_esymm_eq_multiset_esymm`, `Finset.esymm_map_val`
    • `Finset.univ_eq_attach` (rfl), `Finset.attach_val`, `Multiset.attach_map_val'`
    • `MvPolynomial.aeval_X`, `Finset.sum_coe_sort`, `Finset.powersetCard_one`.

  ───────────────────────────────────────────────────────────────────────────
  STATUS: 0 sorries, 0 axioms.  Everything holds over an arbitrary `CommRing`.
  Every numeric fact (multiplicities 1/3/6, D = e₁p₂ − p₃, 2e₂ = off-diag pairs, and the
  char-2 collapse) is also checked exactly in `verify_newton_girard_k3.py`.

  Tags: algebra, symmetric-functions, newton-girard, power-sums, finset, characteristic-two
-/

import Mathlib
import Proofs.AmgmInequalityOQ02OQ01OQ02OQ01
import Proofs.AmgmInequalityOQ02OQ01OQ03

namespace AMGMInequalityOQ02OQ01OQ03Finset

open Finset BigOperators MvPolynomial

variable {ι R : Type*} [CommRing R] [DecidableEq ι]

/-- e₁ = Σ fᵢ. -/
def e1 (s : Finset ι) (f : ι → R) : R := ∑ i ∈ s, f i
/-- e₂ = Σ over 2-subsets of the product (concrete `powersetCard` form). -/
def e2 (s : Finset ι) (f : ι → R) : R := ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, f i
/-- e₃ = Σ over 3-subsets of the product (concrete `powersetCard` form). -/
def e3 (s : Finset ι) (f : ι → R) : R := ∑ t ∈ s.powersetCard 3, ∏ i ∈ t, f i
/-- p₂ = Σ fᵢ². -/
def p2 (s : Finset ι) (f : ι → R) : R := ∑ i ∈ s, f i ^ 2
/-- p₃ = Σ fᵢ³. -/
def p3 (s : Finset ι) (f : ι → R) : R := ∑ i ∈ s, f i ^ 3
/-- Off-diagonal cube term:  Σᵢ Σ_{j≠i} fᵢ²·fⱼ. -/
def Doff (s : Finset ι) (f : ι → R) : R := ∑ i ∈ s, ∑ j ∈ s.erase i, f i ^ 2 * f j
/-- Ordered distinct-pair sum:  Σᵢ Σ_{j≠i} fᵢ·fⱼ. -/
def OffPairs (s : Finset ι) (f : ι → R) : R := ∑ i ∈ s, ∑ j ∈ s.erase i, f i * f j

-- ============================================================
-- k = 2 split (inlined from the parent; proven over any CommRing)
-- ============================================================

/-- (∑ fᵢ)² = Σ fᵢ² + Σ_{i≠j} fᵢfⱼ.  Mirrors the parent's diagonal/off-diagonal split. -/
theorem sq_split (s : Finset ι) (f : ι → R) :
    e1 s f ^ 2 = p2 s f + OffPairs s f := by
  simp only [e1, p2, OffPairs]
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [sq, ← Finset.add_sum_erase s (fun j => f i * f j) hi]

-- ============================================================
-- L3: the off-diagonal cube collapse (proven over any CommRing)
-- ============================================================

/-- **L3 (Doff collapse).**  Σᵢ Σ_{j≠i} fᵢ²fⱼ = e₁·p₂ − p₃.
    Pull `fᵢ²` out of the inner sum, use `Σ_{j≠i} fⱼ = e₁ − fᵢ`, then `ring`. -/
theorem D_collapse (s : Finset ι) (f : ι → R) :
    Doff s f = e1 s f * p2 s f - p3 s f := by
  simp only [Doff, e1, p2, p3]
  calc ∑ i ∈ s, ∑ j ∈ s.erase i, f i ^ 2 * f j
      = ∑ i ∈ s, (f i ^ 2 * (∑ j ∈ s, f j) - f i ^ 3) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.mul_sum, Finset.sum_erase_eq_sub hi]
        ring
    _ = (∑ i ∈ s, f i ^ 2 * (∑ j ∈ s, f j)) - ∑ i ∈ s, f i ^ 3 := by
        rw [Finset.sum_sub_distrib]
    _ = (∑ i ∈ s, f i) * (∑ i ∈ s, f i ^ 2) - ∑ i ∈ s, f i ^ 3 := by
        rw [← Finset.sum_mul]; ring

-- ============================================================
-- The aeval bridge:  concrete Finset defs  =  aeval of MvPolynomial symmetric functions
-- evaluated on the subtype `{x // x ∈ s}`.  This is what carries the universal Newton
-- identities (char-2 safe) down to the concrete `powersetCard`/power-sum statements.
-- ============================================================

omit [DecidableEq ι] in
/-- `aeval` of the universal `psum` on the subtype `{x // x ∈ s}` is the concrete
    power sum `Σ_{i ∈ s} fᵢⁿ`. -/
theorem aeval_psum_subtype (s : Finset ι) (f : ι → R) (n : ℕ) :
    aeval (fun i : {x // x ∈ s} => f i.1) (MvPolynomial.psum {x // x ∈ s} R n)
      = ∑ i ∈ s, f i ^ n := by
  rw [MvPolynomial.psum, map_sum]
  simp only [map_pow, aeval_X]
  exact Finset.sum_coe_sort s (fun i => f i ^ n)

omit [DecidableEq ι] in
/-- `aeval` of the universal `esymm` on the subtype `{x // x ∈ s}` is the concrete
    `powersetCard`-`n` symmetric sum `Σ_{t ⊆ s, |t| = n} ∏_{i ∈ t} fᵢ`. -/
theorem aeval_esymm_subtype (s : Finset ι) (f : ι → R) (n : ℕ) :
    aeval (fun i : {x // x ∈ s} => f i.1) (MvPolynomial.esymm {x // x ∈ s} R n)
      = ∑ t ∈ s.powersetCard n, ∏ i ∈ t, f i := by
  rw [MvPolynomial.aeval_esymm_eq_multiset_esymm, ← Finset.esymm_map_val f s n]
  congr 1
  -- `univ.val.map (fun i => f i.1) = s.val.map f`; the `univ`→`attach` steps are `rfl`,
  -- so `Multiset.attach_map_val'` (which strips the subtype projection) closes it up to defeq.
  exact Multiset.attach_map_val' s.val f

omit [DecidableEq ι] in
/-- The `powersetCard`-1 symmetric sum is just `e₁`. -/
theorem esymm_one_eq_e1 (s : Finset ι) (f : ι → R) :
    (∑ t ∈ s.powersetCard 1, ∏ i ∈ t, f i) = e1 s f := by
  rw [Finset.powersetCard_one]
  simp [e1, Finset.sum_map, Finset.prod_singleton]

omit [DecidableEq ι] in
/-- Bridge at degree 1:  `aeval (esymm … 1) = e₁`. -/
theorem e1_bridge (s : Finset ι) (f : ι → R) :
    aeval (fun i : {x // x ∈ s} => f i.1) (MvPolynomial.esymm {x // x ∈ s} R 1) = e1 s f :=
  (aeval_esymm_subtype s f 1).trans (esymm_one_eq_e1 s f)

omit [DecidableEq ι] in
/-- Bridge at degree 2:  `aeval (esymm … 2) = e₂`  (definitional). -/
theorem e2_bridge (s : Finset ι) (f : ι → R) :
    aeval (fun i : {x // x ∈ s} => f i.1) (MvPolynomial.esymm {x // x ∈ s} R 2) = e2 s f :=
  aeval_esymm_subtype s f 2

omit [DecidableEq ι] in
/-- Bridge at degree 3:  `aeval (esymm … 3) = e₃`  (definitional). -/
theorem e3_bridge (s : Finset ι) (f : ι → R) :
    aeval (fun i : {x // x ∈ s} => f i.1) (MvPolynomial.esymm {x // x ∈ s} R 3) = e3 s f :=
  aeval_esymm_subtype s f 3

omit [DecidableEq ι] in
/-- Bridge for the second power sum:  `aeval (psum … 2) = p₂`  (definitional). -/
theorem p2_bridge (s : Finset ι) (f : ι → R) :
    aeval (fun i : {x // x ∈ s} => f i.1) (MvPolynomial.psum {x // x ∈ s} R 2) = p2 s f :=
  aeval_psum_subtype s f 2

omit [DecidableEq ι] in
/-- Bridge for the third power sum:  `aeval (psum … 3) = p₃`  (definitional). -/
theorem p3_bridge (s : Finset ι) (f : ι → R) :
    aeval (fun i : {x // x ∈ s} => f i.1) (MvPolynomial.psum {x // x ∈ s} R 3) = p3 s f :=
  aeval_psum_subtype s f 3

-- ============================================================
-- Closed forms over ANY CommRing, via the bridge (no char-2 restriction)
-- ============================================================

omit [DecidableEq ι] in
/-- **p₂ closed form** over any CommRing:  p₂ = e₁² − 2·e₂.
    Transport of the universal `psum_two_eq` across the aeval bridge. -/
theorem p2_closed (s : Finset ι) (f : ι → R) :
    p2 s f = e1 s f ^ 2 - 2 * e2 s f := by
  have H := congrArg (aeval (fun i : {x // x ∈ s} => f i.1))
    (AMGMInequalityOQ02OQ01OQ02OQ01.psum_two_eq {x // x ∈ s} R)
  simpa only [map_sub, map_mul, map_pow, map_ofNat,
    p2_bridge, e1_bridge, e2_bridge] using H

omit [DecidableEq ι] in
/-- **p₃ closed form** over any CommRing:  p₃ = e₁³ − 3·e₁·e₂ + 3·e₃.
    Transport of the universal `psum_three_closed` across the aeval bridge.
    This is the genuinely general concrete-Finset Newton–Girard k=3 identity. -/
theorem p3_closed (s : Finset ι) (f : ι → R) :
    p3 s f = e1 s f ^ 3 - 3 * (e1 s f * e2 s f) + 3 * e3 s f := by
  have H := congrArg (aeval (fun i : {x // x ∈ s} => f i.1))
    (AMGMInequalityOQ02OQ01OQ03.psum_three_closed {x // x ∈ s} R)
  simpa only [map_add, map_sub, map_mul, map_pow, map_ofNat,
    p3_bridge, e1_bridge, e2_bridge, e3_bridge] using H

-- ============================================================
-- The two combinatorial bridges (former `sorry`s), now algebraic corollaries
-- ============================================================

/-- **L4 (powersetCard-2 ↔ ordered pairs).**  2·e₂ = Σᵢ Σ_{j≠i} fᵢfⱼ.
    Now an algebraic corollary of the k=2 split and the (char-2 safe) `p2_closed`. -/
theorem two_e2_eq_offPairs (s : Finset ι) (f : ι → R) :
    2 * e2 s f = OffPairs s f := by
  linear_combination sq_split s f + p2_closed s f

/-- **L2 (cube partition — the crux).**  e₁³ = p₃ + 3·Doff + 6·e₃.
    The reusable ordered-triple coincidence partition (multiplicities 1/3/6), obtained
    as an algebraic corollary of `p3_closed`, `D_collapse` and `p2_closed`.  Holds over
    any CommRing (char 2 included) because no factor of 2 is cancelled. -/
theorem cube_partition (s : Finset ι) (f : ι → R) :
    e1 s f ^ 3 = p3 s f + 3 * Doff s f + 6 * e3 s f := by
  linear_combination 2 * p3_closed s f - 3 * D_collapse s f - 3 * e1 s f * p2_closed s f

-- ============================================================
-- Route-A reduction (still valid; now with everything proven)
-- ============================================================

/-- The Route-A reduction `2·p₃ = 2·(e₁³ − 3e₁e₂ + 3e₃)`, valid over any CommRing.
    (Historically this was as far as the direct ordered-triple partition could go without
    a cancellable 2; it is now subsumed by the general `p3_closed`.) -/
theorem two_mul_p3_closed (s : Finset ι) (f : ι → R) :
    2 * p3 s f = 2 * (e1 s f ^ 3 - 3 * (e1 s f * e2 s f) + 3 * e3 s f) := by
  linear_combination cube_partition s f + 3 * D_collapse s f + 3 * e1 s f * p2_closed s f

omit [DecidableEq ι] in
/-- **Concrete general-Finset Newton–Girard k=3** over an arbitrary `CommRing`:
      p₃ = e₁³ − 3·e₁·e₂ + 3·e₃.
    No characteristic hypothesis is needed — the char-2 obstruction of the direct
    Route-A assembly is bypassed by the `aeval` transport (`p3_closed`). -/
theorem newton_girard_three_finset (s : Finset ι) (f : ι → R) :
    p3 s f = e1 s f ^ 3 - 3 * (e1 s f * e2 s f) + 3 * e3 s f :=
  p3_closed s f

end AMGMInequalityOQ02OQ01OQ03Finset
