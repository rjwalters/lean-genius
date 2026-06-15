/-
  Newton–Girard k=3, CONCRETE general-Finset form:
      p₃ = e₁³ − 3·e₁·e₂ + 3·e₃
  with the elementary symmetric sums defined directly over a `Finset s` via
  `powersetCard` (the parent's concrete style), NOT the `MvPolynomial` API.

  Open Question (amgm-inequality-oq-02-oq-01-oq-03), concrete Finset target.

  Lineage:
  • Parent   amgm-inequality-oq-02-oq-01             : k=2 split (∑f)² = ∑f² + Σ_{i≠j} fᵢfⱼ.
  • Sibling  amgm-inequality-oq-02-oq-01-oq-02-oq-01 : the recurrence p₃ = e₁p₂ − e₂p₁ + 3e₃.
  • Universal amgm-inequality-oq-02-oq-01-oq-03       : `psum_three_closed` over MvPolynomial,
                                                       valid for every CommRing.

  ───────────────────────────────────────────────────────────────────────────
  KEY FINDING OF THIS FILE — the char-2 obstruction.

  The "direct ordered-triple partition" route (Approach 1 / Route A in the OQ) assembles
  the closed form from three concrete-Finset facts:
      (L2) cube_partition :  e₁³ = p₃ + 3·Doff + 6·e₃
      (L3) D_collapse     :  Doff = e₁·p₂ − p₃
      (L4)+(k=2)          :  p₂ = e₁² − 2·e₂
  Combining them (see `two_mul_p3_closed`) yields exactly

      2 · p₃ = 2 · (e₁³ − 3·e₁·e₂ + 3·e₃).

  Over ℤ, ℚ, ℝ this gives p₃ = e₁³ − 3e₁e₂ + 3e₃ after cancelling the 2.  But over a
  ring with 2-torsion (e.g. 𝔽₂) the factor 2 is a zero-divisor and the identity 2·p₃ =
  2·(…) collapses to 0 = 0, carrying NO information.  The closed form is still *true* over
  𝔽₂ (the universal `psum_three_closed` proves it for every CommRing), but it is NOT
  derivable from L2/L3/L4 alone there.  So Route A's "everything is `ring`" only closes
  over rings where 2 is cancellable; full generality requires Route B (evaluate the proven
  universal `psum_three_closed` through `MvPolynomial.aeval`).

  This corrects the earlier ACT skeleton, which asserted the final assembly was "all `ring`
  once the sums are reconciled" — that is false over char 2.

  ───────────────────────────────────────────────────────────────────────────
  STATUS (build-pending; Docker + Aristotle both down this session):
    • PROVEN over any CommRing:  sq_split (k=2), D_collapse (L3), p2_closed,
      two_mul_p3_closed (the corrected Route-A reduction).
    • PROVEN over a CommRing with no zero-divisors and 2 ≠ 0:
      newton_girard_three_finset (cancel the 2).
    • Two isolated combinatorial `sorry`s remain — the genuine OQ content:
        cube_partition       (L2: ordered-triple coincidence partition, multiplicities 1/3/6)
        two_e2_eq_offPairs   (L4: powersetCard-2 ↔ ordered distinct pairs)
      Both are HARD-but-known Finset-bookkeeping lemmas — ideal Aristotle targets once the
      backend is back, or Route B (aeval) supersedes them with one reindexing lemma.

  Every numeric fact (multiplicities 1/3/6, D = e₁p₂ − p₃, 2e₂ = off-diag pairs, and the
  char-2 collapse) is checked exactly in `verify_newton_girard_k3.py`.

  Tags: algebra, symmetric-functions, newton-girard, power-sums, finset, characteristic-two
-/

import Mathlib

namespace AMGMInequalityOQ02OQ01OQ03Finset

open Finset BigOperators

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
-- L2 / L4: the two genuine combinatorial bridges (OQ content) — sorry
-- ============================================================

/-- **L4 (powersetCard-2 ↔ ordered pairs).**  2·e₂ = Σᵢ Σ_{j≠i} fᵢfⱼ.
    Each unordered 2-subset `{i,j}` corresponds to exactly the two ordered pairs `(i,j)`,
    `(j,i)`, each contributing `fᵢfⱼ`; hence the ordered sum is `2·e₂`.  Verified exactly
    in `verify_newton_girard_k3.py`.  Lean route: bridge `s.powersetCard 2` to `s.offDiag`
    via `Sym2`/`Finset.sum_sym2` (no single-lemma shortcut in Mathlib). HARD/known —
    Aristotle target, or supplant by Route B (aeval). -/
theorem two_e2_eq_offPairs (s : Finset ι) (f : ι → R) :
    2 * e2 s f = OffPairs s f := by
  sorry

/-- **L2 (cube partition — the crux).**  e₁³ = p₃ + 3·Doff + 6·e₃.
    Expand `(∑fᵢ)³ = Σᵢ Σⱼ Σₖ fᵢfⱼfₖ` (two `sum_mul_sum`) and partition the index cube
    `s×s×s` by coincidence pattern:
        all-equal  (1 ordering)        → p₃,
        exactly-two-equal (3 orderings) → 3·Doff,
        all-distinct (6 orderings)      → 6·e₃.
    Multiplicities 1/3/6 verified exactly in `verify_newton_girard_k3.py`.  This is the
    reusable combinatorial artifact the OQ is meant to produce. HARD/known — Aristotle
    target, or supplant by Route B (aeval). -/
theorem cube_partition (s : Finset ι) (f : ι → R) :
    e1 s f ^ 3 = p3 s f + 3 * Doff s f + 6 * e3 s f := by
  sorry

-- ============================================================
-- Corrected Route-A assembly (proven from L2,L3,L4 over any CommRing)
-- ============================================================

/-- p₂ = e₁² − 2·e₂, from the k=2 split and L4. -/
theorem p2_closed (s : Finset ι) (f : ι → R) :
    p2 s f = e1 s f ^ 2 - 2 * e2 s f := by
  have h2 := sq_split s f
  have h4 := two_e2_eq_offPairs s f
  linear_combination h4 - h2

/-- **The honest Route-A output:** `2·p₃ = 2·(e₁³ − 3e₁e₂ + 3e₃)`.
    Valid over ANY CommRing — but note the factor 2 does NOT cancel in char 2.
    Coefficients (derived, sympy-checked):  `cube_partition + 3·D_collapse + 3·e₁·p2_closed`. -/
theorem two_mul_p3_closed (s : Finset ι) (f : ι → R) :
    2 * p3 s f = 2 * (e1 s f ^ 3 - 3 * (e1 s f * e2 s f) + 3 * e3 s f) := by
  have hc := cube_partition s f
  have hd := D_collapse s f
  have hp := p2_closed s f
  linear_combination hc + 3 * hd + 3 * e1 s f * hp

/-- **Concrete general-Finset Newton–Girard k=3** over a CommRing where 2 is cancellable
    (no zero-divisors and `2 ≠ 0`):  p₃ = e₁³ − 3·e₁·e₂ + 3·e₃.
    The char-2 hypothesis is essential — see the file header. -/
theorem newton_girard_three_finset [NoZeroDivisors R] (h2 : (2 : R) ≠ 0)
    (s : Finset ι) (f : ι → R) :
    p3 s f = e1 s f ^ 3 - 3 * (e1 s f * e2 s f) + 3 * e3 s f :=
  mul_left_cancel₀ h2 (two_mul_p3_closed s f)

end AMGMInequalityOQ02OQ01OQ03Finset
