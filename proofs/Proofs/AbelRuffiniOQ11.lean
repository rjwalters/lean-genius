import Mathlib

/-
# Abel–Ruffini, open question oq-11: the radical-solvable side

The Abel–Ruffini story has two faces. The *negative* face — the symmetric group
`Sₙ` is not solvable for `n ≥ 5`, so the general quintic is not solvable by
radicals — is thoroughly formalized elsewhere in this project (base
`AbelRuffini.lean`, `AbelRuffiniOQ07` for the concrete `X⁵ − X − 1 ≅ S₅`). The
*positive* face is comparatively neglected: **why do radicals work for the cases
they do?**

Galois' answer: an equation is solvable by radicals iff its Galois group is a
solvable group, and the equations one can actually *write* with radicals — pure
powers `Xⁿ = a` and finite combinations of them — always have solvable Galois
groups. Mathlib proves the single-equation facts (`gal_X_pow_sub_C_isSolvable`,
`gal_X_pow_sub_one_isSolvable`) and an abstract multiset-product closure
(`gal_prod_isSolvable`), but states neither a directly usable finite-*product*
form nor the side-by-side dichotomy. This entry supplies both:

* `gal_pow_sub_C_isSolvable`   : every pure equation `Xⁿ = a` has solvable Galois
  group — radicals always succeed for a single root extraction;
* `gal_pow_sub_one_isSolvable` : the `n`-th roots of unity `Xⁿ = 1` likewise;
* `gal_finset_prod_pow_sub_C_isSolvable` : **any finite product
  `∏ᵢ (X^{nᵢ} − aᵢ)` of pure radical equations has solvable Galois group** — the
  closure capturing "anything assembled from radicals stays solvable";
* `abel_ruffini_two_faces` : the dichotomy in one statement — pure radical
  equations are always solvable, yet `Sₘ` (`m ≥ 5`) is not.

Everything is `0`-axiom (`propext` / `Classical.choice` / `Quot.sound` only) and
`sorry`-free.
-/

namespace AbelRuffiniOQ11

open Polynomial

variable {F : Type*} [Field F]

/-- **A single pure equation is solvable.** `Xⁿ = a` always has a solvable Galois
group — extracting one radical never destroys solvability. (Mathlib's
`gal_X_pow_sub_C_isSolvable`, re-exposed as the base case of the closure below.) -/
theorem gal_pow_sub_C_isSolvable (n : ℕ) (a : F) :
    IsSolvable (X ^ n - C a : F[X]).Gal :=
  gal_X_pow_sub_C_isSolvable n a

/-- **Roots of unity are solvable.** `Xⁿ = 1` has a solvable (indeed abelian)
Galois group. (Mathlib's `gal_X_pow_sub_one_isSolvable`.) -/
theorem gal_pow_sub_one_isSolvable (n : ℕ) :
    IsSolvable (X ^ n - 1 : F[X]).Gal :=
  gal_X_pow_sub_one_isSolvable n

/-- **The radical-solvable closure.** Any finite product `∏ᵢ (X^{nᵢ} − aᵢ)` of
pure radical equations has a solvable Galois group. This is the constructive
counterpart to the symmetric-group obstruction: every polynomial assembled from
root extractions stays solvable. Proved by induction over the index set, using
`gal_mul_isSolvable` to glue one factor at a time onto a solvable product. -/
theorem gal_finset_prod_pow_sub_C_isSolvable {ι : Type*} (s : Finset ι)
    (n : ι → ℕ) (a : ι → F) :
    IsSolvable (∏ i ∈ s, (X ^ (n i) - C (a i)) : F[X]).Gal := by
  induction s using Finset.cons_induction with
  | empty => simpa using (gal_one_isSolvable (F := F))
  | cons i s hi ih =>
      rw [Finset.prod_cons]
      exact gal_mul_isSolvable (gal_X_pow_sub_C_isSolvable (n i) (a i)) ih

/-- **The two faces of Abel–Ruffini, side by side.** Pure radical equations
`Xⁿ = a` always have solvable Galois groups (radicals succeed), yet the symmetric
group `Sₘ` is not solvable for `m ≥ 5` (the obstruction that makes the general
quintic unsolvable). The whole theory lives in the gap between these two facts. -/
theorem abel_ruffini_two_faces :
    (∀ (n : ℕ) (a : F), IsSolvable (X ^ n - C a : F[X]).Gal) ∧
    (∀ m : ℕ, 5 ≤ m → ¬ IsSolvable (Equiv.Perm (Fin m))) :=
  ⟨fun n a => gal_X_pow_sub_C_isSolvable n a,
   fun m hm => Equiv.Perm.not_solvable (Fin m) (by rw [Cardinal.mk_fin]; exact_mod_cast hm)⟩

end AbelRuffiniOQ11
