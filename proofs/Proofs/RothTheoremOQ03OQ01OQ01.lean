/-
Roth/Szemerédi — OQ-03-OQ-01-OQ-01: Multilinearity of the k-AP counting operator Λ_k

Source: open question of the roth-theorem-k3 gallery (Gowers norms, OQ-03)
Parent: Proofs/RothTheoremOQ03OQ01.lean  (defines Λ_k = kAPCount and the Gowers norm,
        proves the constant/normalization/annihilation identities)

## What this adds

The parent file builds the k-AP counting operator

  Λ_k(f₀,…,f_{k-1}) = E_{x,d ∈ ZMod N} ∏_{i<k} fᵢ(x + i·d)

and proves Λ_k(c,…,c) = cᵏ, Λ_k(1,…,1) = 1, and that a zero slot annihilates the
count. The single most important *structural* fact, however — the one that powers the
generalized von Neumann inequality and every density-increment argument in the
Roth/Szemerédi circle — is that **Λ_k is multilinear**: it is additive and homogeneous
in each of its k arguments separately.

This file imports the parent operator and proves exactly that, 0-axiom:

* `prod_update_factor` — pull the j-th factor out of the k-AP product (the engine);
* `kAPCount_add_slot`   — additivity in slot j: Λ_k(…, a+b, …) = Λ_k(…,a,…) + Λ_k(…,b,…);
* `kAPCount_smul_slot`  — homogeneity in slot j: Λ_k(…, c•a, …) = c · Λ_k(…,a,…);
* `gowersNorm_nonneg`   — the Gowers norm is nonnegative (it is a genuine modulus).

Slots are addressed with `Function.update`, so "the tuple `f` with its j-th entry
replaced by `v`" is `Function.update f j v`. All results are machine-checked with only
the foundational axioms (`propext`/`Classical.choice`/`Quot.sound`), no `native_decide`.
-/
import Proofs.RothTheoremOQ03OQ01

open Finset BigOperators

namespace RothTheoremOQ03OQ01

variable {N : ℕ} [NeZero N]

/-- **The factorization engine.** Replacing slot `j` of the tuple by `v` pulls the
`j`-th factor `v(x + j·d)` clean out of the `k`-AP product, leaving the product of the
untouched factors over the remaining indices. -/
theorem prod_update_factor (k : ℕ) (f : Fin k → ZMod N → ℂ) (j : Fin k)
    (v : ZMod N → ℂ) (x d : ZMod N) :
    (∏ i : Fin k, Function.update f j v i (x + i.val • d))
      = v (x + j.val • d) * ∏ i ∈ univ.erase j, f i (x + i.val • d) := by
  rw [← Finset.mul_prod_erase univ
        (fun i => Function.update f j v i (x + i.val • d)) (mem_univ j)]
  congr 1
  · rw [Function.update_self]
  · refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- **Additivity in a slot.** `Λ_k` is additive in its `j`-th argument:
`Λ_k(…, a + b, …) = Λ_k(…, a, …) + Λ_k(…, b, …)`. -/
theorem kAPCount_add_slot (k : ℕ) (f : Fin k → ZMod N → ℂ) (j : Fin k)
    (a b : ZMod N → ℂ) :
    kAPCount k (Function.update f j (a + b))
      = kAPCount k (Function.update f j a) + kAPCount k (Function.update f j b) := by
  unfold kAPCount
  simp only [prod_update_factor, Pi.add_apply, add_mul]
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← Finset.sum_add_distrib]

/-- **Homogeneity in a slot.** `Λ_k` is homogeneous in its `j`-th argument:
`Λ_k(…, c • a, …) = c · Λ_k(…, a, …)`. -/
theorem kAPCount_smul_slot (k : ℕ) (f : Fin k → ZMod N → ℂ) (j : Fin k)
    (c : ℂ) (a : ZMod N → ℂ) :
    kAPCount k (Function.update f j (c • a)) = c * kAPCount k (Function.update f j a) := by
  unfold kAPCount
  simp only [prod_update_factor, Pi.smul_apply, smul_eq_mul]
  rw [mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  ring

/-- The Gowers `Uˢ` norm is nonnegative — it is defined as a genuine modulus `‖·‖`. -/
theorem gowersNorm_nonneg (N s : ℕ) [NeZero N] (f : ZMod N → ℂ) :
    0 ≤ gowersNorm N s f := by
  unfold gowersNorm
  exact norm_nonneg _

end RothTheoremOQ03OQ01
