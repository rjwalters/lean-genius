import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-
# Multisection of an Arbitrary Summable Family as a Reindexing via `Nat.divModEquiv`

## What This Proves

The parent (`GeometricSeriesOQ09OQ01OQ01`) obtained the `q`-fold splitting of the
*geometric* series `∑_m r^m` as a genuine reindexing of the summation along the
bijection

  `ℕ  ≃  ℕ × Fin q,    m ↦ (m / q, m % q),    (n, a) ↦ q·n + a`

(`Nat.divModEquiv`).  This file answers its open question: the same viewpoint
applies to **any** summable family `f : ℕ → M` valued in a complete Hausdorff
uniform abelian group, with *no* algebraic closed form required.  Concretely, fix a
modulus `q ≥ 1`; then for every `HasSum f S`:

* **Reindexing.**  `HasSum (fun (p : ℕ × Fin q) => f (q·p.1 + p.2)) S` — the
  one-dimensional sum, transported verbatim onto `ℕ × Fin q`.
* **Block regrouping.**  `HasSum (fun n => ∑_{a<q} f (q·n + a)) S` — grouping the
  reindexed series by the block index `n` (finite inner sums); this needs no
  hypothesis beyond `HasSum f S` because the fibers `Fin q` are finite.
* **Residue multisection.**  `HasSum (fun a : Fin q => ∑'_n f (q·n + a)) S`, hence
  `∑_{a<q} ∑'_n f (q·n + a) = ∑'_m f m`.  This is the genuine *multisection*: the
  series is split into `q` residue subseries indexed by `a`, each summed over its
  own block index `n`.

## The Characterisation (answering the open question)

The open question asks to *characterise when* the residue regrouping
`∑_{a<q} ∑'_n f (q·n + a) = S` holds.  The answer is clean: **it holds for every
summable `f`, unconditionally** — it is a pure Fubini/`HasSum.prod_fiberwise`
consequence of summability.  The only nontrivial input is that each residue
subseries `n ↦ f (q·n + a)` is itself summable; this is automatic because
`n ↦ q·n + a` is injective, so summability descends along it
(`Summable.comp_injective`).  No absolute convergence beyond plain `Summable`,
no normed/Banach structure is required — only that `M` is a complete Hausdorff
uniform abelian group (completeness so that each residue subseries converges,
Hausdorffness so that infinite sums are unique, and the topological-group
structure so that the regular-space fiberwise-summation lemma applies).

## Why This Is Not Already in Mathlib

Mathlib has `Nat.divModEquiv`, `Equiv.hasSum_iff`, `HasSum.prod_fiberwise`, and
`Summable.comp_injective`, but not their assembly into the residue-indexed
multisection of an arbitrary summable family.  The new content is the
identification of `f ∘ (Nat.divModEquiv q).symm` with `p ↦ f (q·p.1 + p.2)` and
the observation that, once each residue subseries is seen to be summable via the
injectivity of `n ↦ q·n + a`, the full multisection drops out of fiberwise
summation with no further structure.

## Status: 0 sorries, 0 axioms (over any complete Hausdorff uniform abelian group)
-/

namespace GeometricSeriesOQ09OQ01OQ01OQ01

set_option linter.unusedSectionVars false

variable {M : Type*} [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M]
  [CompleteSpace M] [T2Space M] {f : ℕ → M} {S : M}

/-! ## Injectivity of the residue map and summability of residue subseries -/

/-- For `q ≠ 0` the residue map `n ↦ q·n + a` is injective `ℕ → ℕ`. -/
theorem residue_injective {q : ℕ} (hq : q ≠ 0) (a : ℕ) :
    Function.Injective (fun n : ℕ => q * n + a) := by
  intro n m h
  simp only at h
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hq) (Nat.add_right_cancel h)

/-- Each residue subseries `n ↦ f (q·n + a)` is summable whenever `f` is and
`q ≠ 0`.  This is the only place summability is used, and it follows purely from
the injectivity of the residue map (`Summable.comp_injective`). -/
theorem summable_residue (hf : Summable f) {q : ℕ} (hq : q ≠ 0) (a : ℕ) :
    Summable (fun n : ℕ => f (q * n + a)) := by
  simpa [Function.comp_def] using hf.comp_injective (residue_injective hq a)

/-! ## The reindexing theorem -/

/-- **Reindexing.**  Transporting `HasSum f S` along the bijection
`ℕ ≃ ℕ × Fin q`, `m ↦ (m / q, m % q)` yields the two-dimensional series with term
`f (q·n + a)` at `(n, a)`, summing to the same `S`. -/
theorem hasSum_reindex (hf : HasSum f S) (q : ℕ) [NeZero q] :
    HasSum (fun p : ℕ × Fin q => f (q * p.1 + (p.2 : ℕ))) S := by
  have h := (Nat.divModEquiv q).symm.hasSum_iff.mpr hf
  simp only [Function.comp_def, Nat.divModEquiv_symm_apply] at h
  -- `h : HasSum (fun p => f (p.1 * q + ↑p.2)) S`
  have heq : (fun p : ℕ × Fin q => f (p.1 * q + (p.2 : ℕ)))
      = (fun p : ℕ × Fin q => f (q * p.1 + (p.2 : ℕ))) := by
    funext p; rw [Nat.mul_comm]
  rwa [heq] at h

/-- `tsum` form of the reindexing. -/
theorem tsum_reindex (hf : Summable f) (q : ℕ) [NeZero q] :
    ∑' p : ℕ × Fin q, f (q * p.1 + (p.2 : ℕ)) = ∑' m : ℕ, f m := by
  rw [(hasSum_reindex hf.hasSum q).tsum_eq, hf.hasSum.tsum_eq]

/-- The reindexed two-dimensional series is summable. -/
theorem summable_reindex (hf : Summable f) (q : ℕ) [NeZero q] :
    Summable (fun p : ℕ × Fin q => f (q * p.1 + (p.2 : ℕ))) :=
  (hasSum_reindex hf.hasSum q).summable

/-! ## Block regrouping: finite inner sums over the `q` residues -/

/-- **Block regrouping.**  Grouping the reindexed series by the block index
`n : ℕ` (each block the *finite* sum over the `q` residues) recovers `S`.  No
hypothesis beyond `HasSum f S` is needed because the fibers `Fin q` are finite. -/
theorem hasSum_block (hf : HasSum f S) (q : ℕ) [NeZero q] :
    HasSum (fun n : ℕ => ∑ a : Fin q, f (q * n + (a : ℕ))) S :=
  (hasSum_reindex hf q).prod_fiberwise fun _ => hasSum_fintype _

/-! ## Residue multisection: the Fubini consequence of summability -/

/-- **Residue multisection.**  Grouping the reindexed series by the residue
`a : Fin q` (each group the *infinite* subseries over the block index `n`)
recovers `S`.  This is the multisection of an arbitrary `HasSum`, valid for every
summable `f` as a fiberwise-summation (Fubini) consequence. -/
theorem hasSum_multisection (hf : HasSum f S) (q : ℕ) [NeZero q] :
    HasSum (fun a : Fin q => ∑' n : ℕ, f (q * n + (a : ℕ))) S := by
  have h2 : HasSum (fun p : Fin q × ℕ => f (q * p.2 + (p.1 : ℕ))) S := by
    rw [← (Equiv.prodComm ℕ (Fin q)).hasSum_iff]
    simpa [Function.comp_def] using hasSum_reindex hf q
  exact h2.prod_fiberwise fun a =>
    (summable_residue hf.summable (NeZero.ne q) (a : ℕ)).hasSum

/-- **Multisection identity (answering the open question).**  For every summable
`f` the residue regrouping holds unconditionally:
`∑_{a<q} ∑'_n f (q·n + a) = ∑'_m f m`. -/
theorem tsum_multisection (hf : Summable f) (q : ℕ) [NeZero q] :
    ∑ a ∈ Finset.range q, (∑' n : ℕ, f (q * n + a)) = ∑' m : ℕ, f m := by
  have hfin : (∑ a : Fin q, ∑' n : ℕ, f (q * n + (a : ℕ))) = ∑' m : ℕ, f m :=
    (hasSum_fintype (fun a : Fin q => ∑' n : ℕ, f (q * n + (a : ℕ)))).unique
      (hasSum_multisection hf.hasSum q)
  rw [← hfin, Fin.sum_univ_eq_sum_range (fun a => ∑' n : ℕ, f (q * n + a)) q]

/-! ## Specialisations -/

/-- The `q = 2` even/odd splitting of an arbitrary summable family:
`HasSum f S → HasSum (fun a : Fin 2 => ∑'_n f (2·n + a)) S`. -/
theorem hasSum_multisection_two (hf : HasSum f S) :
    HasSum (fun a : Fin 2 => ∑' n : ℕ, f (2 * n + (a : ℕ))) S :=
  hasSum_multisection hf 2

/-- Even/odd decomposition of a summable real (or any-group) family:
`∑'_n f (2n) + ∑'_n f (2n+1) = ∑'_m f m`. -/
theorem tsum_even_add_odd (hf : Summable f) :
    (∑' n : ℕ, f (2 * n)) + (∑' n : ℕ, f (2 * n + 1)) = ∑' m : ℕ, f m := by
  have h := tsum_multisection hf 2
  simpa [Finset.sum_range_succ] using h

/-! ## Concrete check -/

/-- Sanity check: the even/odd multisection of the summable family `n ↦ (1/2)^n`
recombines to its total `∑'_m (1/2)^m = 2`. -/
example :
    (∑' n : ℕ, (1 / 2 : ℝ) ^ (2 * n)) + (∑' n : ℕ, (1 / 2 : ℝ) ^ (2 * n + 1))
      = ∑' m : ℕ, (1 / 2 : ℝ) ^ m :=
  tsum_even_add_odd (summable_geometric_of_lt_one (by norm_num) (by norm_num))

end GeometricSeriesOQ09OQ01OQ01OQ01
