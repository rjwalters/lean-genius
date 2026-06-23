/-
  AMGM-inequality OQ-02-OQ-01-OQ-04
  =================================
  Newton–Girard recurrence in the Finset / CommRing setting.

  Mathlib's `Mathlib.RingTheory.MvPolynomial.NewtonIdentities` proves Newton's
  identities for the *universal* symmetric functions `MvPolynomial.esymm` /
  `MvPolynomial.psum` over `Fintype σ` (the "polynomial-root" form).  This file
  states — and aims to prove — the directly usable specialization: for an
  arbitrary finite family `f : ι → R` indexed by a `Finset s` over a commutative
  ring `R`, with the concrete power sums `pₖ = ∑_{i∈s} f i ^ k` and elementary
  symmetric functions `eₖ = ∑_{T ⊆ s, |T|=k} ∏_{i∈T} f i`.

  Newton–Girard (k ≥ 1):

      ∑_{j=0}^{k-1} (-1)^j · e_j · p_{k-j}  +  (-1)^k · k · e_k  =  0.

  Worked sanity check (s = {a,b}, values x,y):
    k=1:  p₁ - e₁ = (x+y) - (x+y) = 0.
    k=2:  e₀p₂ - e₁p₁ + 2e₂ = (x²+y²) - (x+y)² + 2xy = 0.

  Strategy.  Two viable reductions:

  (A) Universal symmetric functions.  Set the index type to the subtype
      `s : Type` (`{i // i ∈ s}`, a `Fintype`).  Apply the algebra map
      `MvPolynomial.aeval (fun i : s => f i.1)` to Mathlib's
      `MvPolynomial.mul_esymm_eq_sum` (the universal Newton identity over
      `MvPolynomial (s) R`).  Since `aeval` is a ring hom it sends `esymm`
      to `esymm s f ·` and `psum` to `psum s f ·`; the universal identity then
      transports to the concrete one.  Needs evaluation lemmas
      `aeval _ (MvPolynomial.esymm ..) = esymm s f ..` and likewise for `psum`.

  (B) Direct induction on `s` (add one element at a time).  Self-contained,
      ~150–250 lines; the update rule `eₖ(s ∪ {a}) = eₖ(s) + a·e_{k-1}(s)` plus a
      generating-function / telescoping argument gives the recurrence with no
      dependency on uncertain Mathlib API names.  Preferred if (A)'s bridging
      lemmas are absent.

  Status: VERIFIED.  Route A executed below: the concrete recurrence is obtained
  by applying `MvPolynomial.aeval (fun i : s => f i.1)` to Mathlib's universal
  Newton identity `MvPolynomial.mul_esymm_eq_sum`.  Machine-checked under Lean
  v4.26.0 (0 sorries, 0 axioms).  Mathlib API used:
    * `MvPolynomial.mul_esymm_eq_sum`              (RingTheory Symmetric NewtonIdentities)
    * `MvPolynomial.aeval_esymm_eq_multiset_esymm` (RingTheory Symmetric Defs)
    * `Finset.esymm_map_val`                       (RingTheory Symmetric Defs)
    * `MvPolynomial.psum`, `MvPolynomial.aeval_X`
    * `Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk`, `Finset.sum_range_succ`
    * `Multiset.attach_map_val'`, `Finset.attach_val`, `Finset.sum_coe_sort`
    * `Odd.neg_one_pow`
-/

import Mathlib

open Finset BigOperators

namespace AmgmNewtonGirard

variable {ι R : Type*} [CommRing R]

/-- Power sum `pₖ = ∑_{i ∈ s} (f i)^k`. -/
def psum (s : Finset ι) (f : ι → R) (k : ℕ) : R := ∑ i ∈ s, f i ^ k

/-- Elementary symmetric polynomial `eₖ = ∑_{T ⊆ s, |T| = k} ∏_{i ∈ T} f i`. -/
def esymm (s : Finset ι) (f : ι → R) (k : ℕ) : R :=
  ∑ T ∈ s.powersetCard k, ∏ i ∈ T, f i

/-- **Power-sum bridge.**  `aeval` of the universal power sum `MvPolynomial.psum`
    over the index subtype `↥s`, evaluated at `i ↦ f i`, is the concrete `psum s f`. -/
theorem psum_bridge (s : Finset ι) (f : ι → R) (n : ℕ) :
    MvPolynomial.aeval (fun i : ↥s => f i.1) (MvPolynomial.psum (↥s) R n) = psum s f n := by
  rw [MvPolynomial.psum, map_sum, psum]
  rw [← Finset.sum_coe_sort s (fun i => f i ^ n)]
  exact Finset.sum_congr rfl (fun i _ => by rw [map_pow, MvPolynomial.aeval_X])

/-- **Elementary-symmetric bridge.**  `aeval` of the universal elementary symmetric
    polynomial `MvPolynomial.esymm` over `↥s`, evaluated at `i ↦ f i`, is the
    concrete `esymm s f`. -/
theorem esymm_bridge (s : Finset ι) (f : ι → R) (n : ℕ) :
    MvPolynomial.aeval (fun i : ↥s => f i.1) (MvPolynomial.esymm (↥s) R n) = esymm s f n := by
  rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
  -- Goal: ((univ : Finset ↥s).val.map (fun i => f i.1)).esymm n = esymm s f n
  have himg : (Finset.univ : Finset ↥s).val.map (fun i : ↥s => f i.1) = s.val.map f := by
    -- `univ = s.attach` (Fintype instance for the coe-sort), then collapse the attach
    -- via `Multiset.attach_map_val'` (`s.attach.map (f ∘ val) = s.map f`).
    have huniv : (Finset.univ : Finset ↥s) = s.attach := rfl
    rw [huniv, Finset.attach_val]
    exact Multiset.attach_map_val' s.val f
  rw [himg]
  -- `Finset.esymm_map_val f s n : (s.val.map f).esymm n = ∑ t ∈ s.powersetCard n, ∏ i ∈ t, f i`
  rw [Finset.esymm_map_val f s n]
  rfl

/-- The filtered universal-Newton sum over `antidiagonal k` reindexes onto `range k`. -/
theorem reindex_filter (s : Finset ι) (f : ι → R) (k : ℕ) :
    ∑ a ∈ (Finset.antidiagonal k).filter (fun a => a.1 < k),
        (-1) ^ a.1 * esymm s f a.1 * psum s f a.2
      = ∑ j ∈ Finset.range k, (-1) ^ j * esymm s f j * psum s f (k - j) := by
  rw [Finset.sum_filter,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
        (fun a => if a.1 < k then (-1) ^ a.1 * esymm s f a.1 * psum s f a.2 else 0) k,
      Finset.sum_range_succ]
  simp only [lt_self_iff_false, if_false, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  rw [if_pos (Finset.mem_range.mp hj)]

/-- **Newton–Girard recurrence** (Finset / CommRing form).

    Note `esymm s f 0 = 1` (empty product over the unique 0-subset `∅`), so the
    `j = 0` summand is `p_k`, and the sign-alternating tail closes with the
    `(-1)^k · k · e_k` correction term. -/
theorem newton_girard (s : Finset ι) (f : ι → R) (k : ℕ) (_hk : 1 ≤ k) :
    (∑ j ∈ Finset.range k, (-1) ^ j * esymm s f j * psum s f (k - j))
      + (-1) ^ k * (k : R) * esymm s f k = 0 := by
  classical
  -- Universal Newton identity over `↥s`, transported by the algebra map `aeval`.
  have key := MvPolynomial.mul_esymm_eq_sum (↥s) R k
  apply_fun (MvPolynomial.aeval (fun i : ↥s => f i.1)) at key
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast, map_sum,
    esymm_bridge, psum_bridge] at key
  rw [reindex_filter s f k] at key
  -- `key : (k : R) * esymm s f k = (-1) ^ (k + 1) * (∑ j ∈ range k, (-1)^j e_j p_{k-j})`
  have hsign : ((-1 : R)) ^ k * ((-1 : R)) ^ (k + 1) = -1 := by
    rw [← pow_add, show k + (k + 1) = 2 * k + 1 by ring]
    exact Odd.neg_one_pow ⟨k, by ring⟩
  rw [mul_assoc ((-1 : R) ^ k) (k : R) (esymm s f k), key, ← mul_assoc, hsign, neg_one_mul]
  ring

end AmgmNewtonGirard
