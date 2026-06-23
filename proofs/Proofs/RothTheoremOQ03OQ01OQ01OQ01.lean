/-
Roth/Szemerédi — OQ-03-OQ-01-OQ-01-OQ-01: Symmetries of the k-AP counting operator Λ_k

Source: open question of the roth-theorem-k3 gallery (Gowers norms, OQ-03)
Parent: Proofs/RothTheoremOQ03OQ01OQ01.lean (multilinearity of Λ_k)
Grandparent: Proofs/RothTheoremOQ03OQ01.lean (defines Λ_k = kAPCount, foundational identities)

## What this adds

The grandparent builds the k-AP counting operator

  Λ_k(f₀,…,f_{k-1}) = E_{x,d ∈ ZMod N} ∏_{i<k} fᵢ(x + i·d)

and proves the degenerate/normalization identities; the parent proves it is
*multilinear*. Neither records the **geometric symmetries** of the underlying
configuration `{x, x+d, …, x+(k-1)d}` — the symmetries of an arithmetic
progression as a set. These are genuinely new facts, not consequences of
multilinearity: they come from reindexing bijections of the averaging variables
`(x, d)`, not from the algebra of a single slot.

This file proves the two basic symmetries, 0-axiom:

* `kAPCount_translate` — **translation invariance**: shifting every function by a
  common translate `t` leaves the count unchanged,
  `Λ_k(f₀(·+t),…,f_{k-1}(·+t)) = Λ_k(f₀,…,f_{k-1})`. (The AP is shifted as a
  whole by `−t`; reindex `x ↦ x + t`.)

* `kAPCount_reflect` — **reflection symmetry**: reversing the tuple leaves the
  count unchanged, `Λ_k(f₀,…,f_{k-1}) = Λ_k(f_{k-1},…,f₀)`. The progression
  `x, x+d, …, x+(k-1)d` read backwards is the progression with base point
  `x+(k-1)d` and common difference `−d`; reindex `(x,d) ↦ (x+(k-1)d, −d)`, an
  involution of `(ZMod N)²`, together with the index reversal `i ↦ k-1-i`.

Reversal of the tuple is `fun i => f (Fin.rev i)` (`Fin.rev i = k-1-i`). The
helper `prod_rev_reindex` performs the index reversal inside the product; the
involution `reflectShift` performs the variable substitution. All results are
machine-checked with only the foundational axioms
(`propext`/`Classical.choice`/`Quot.sound`), no `native_decide`.
-/
import Proofs.RothTheoremOQ03OQ01OQ01

open Finset BigOperators

namespace RothTheoremOQ03OQ01

variable {N : ℕ} [NeZero N]

-- ============================================================
-- Translation invariance
-- ============================================================

/-- **Translation invariance.** Replacing every function `fᵢ` by its translate
`y ↦ fᵢ(y + t)` does not change the count: the progression is shifted as a whole
by `−t`, which is absorbed by reindexing the base-point average `x ↦ x + t`. -/
theorem kAPCount_translate (k : ℕ) (f : Fin k → ZMod N → ℂ) (t : ZMod N) :
    kAPCount k (fun i y => f i (y + t)) = kAPCount k f := by
  unfold kAPCount
  congr 1
  -- Reindex the base-point average `x ↦ x + t`; the common translate is absorbed.
  refine Fintype.sum_equiv (Equiv.addRight t) _ _ (fun x => ?_)
  refine Finset.sum_congr rfl (fun d _ => ?_)
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp only [Equiv.coe_addRight]
  congr 1
  abel

-- ============================================================
-- Reflection symmetry
-- ============================================================

/-- **Index reversal inside the product.** Reversing which function is paired
with which AP term is the same as reversing the AP terms: the product of
`f (rev i)` over the AP `x + i·d` equals the product of `f i` over the reversed
shifts `x + (rev i)·d`. -/
theorem prod_rev_reindex (k : ℕ) (f : Fin k → ZMod N → ℂ) (x d : ZMod N) :
    (∏ i : Fin k, f (Fin.rev i) (x + i.val • d))
      = ∏ i : Fin k, f i (x + (Fin.rev i).val • d) := by
  have h := Equiv.Perm.prod_comp' (Fin.revPerm) Finset.univ
    (fun a b : Fin k => f a (x + b.val • d)) (by intro a _; exact Finset.mem_univ a)
  simpa [Fin.revPerm_apply, Fin.revPerm_symm] using h

/-- The base-point/difference substitution behind reflection symmetry:
`(x, d) ↦ (x + (k-1)·d, −d)`. It is an involution of `(ZMod N)²` and it sends the
reversed AP shift `x + (k-1-i)·d` to the forward shift of the reflected
progression, `(x + (k-1)d) + i·(−d)`. -/
def reflectShift (k : ℕ) : ZMod N × ZMod N → ZMod N × ZMod N :=
  fun p => (p.1 + (k - 1) • p.2, -p.2)

theorem reflectShift_involutive (k : ℕ) :
    Function.Involutive (reflectShift (N := N) k) := by
  intro p
  refine Prod.ext ?_ ?_
  · show p.1 + (k - 1) • p.2 + (k - 1) • -p.2 = p.1
    rw [smul_neg]; abel
  · show - -p.2 = p.2
    rw [neg_neg]

/-- The pointwise identity driving reflection: the reversed-AP shift equals the
forward shift of the reflected progression. -/
theorem reflect_shift_eq (k : ℕ) (i : Fin k) (x d : ZMod N) :
    x + (Fin.rev i).val • d = (x + (k - 1) • d) + i.val • (-d) := by
  have hle : i.val ≤ k - 1 := by have := i.isLt; omega
  have hrev : (Fin.rev i).val = k - 1 - i.val := by rw [Fin.val_rev]; omega
  have hsum : (k - 1 - i.val) • d + i.val • d = (k - 1) • d := by
    rw [← add_nsmul]; congr 1; omega
  rw [hrev, smul_neg, ← hsum]; abel

/-- **Reflection symmetry.** Reversing the tuple of functions leaves the count
unchanged: `Λ_k(f₀,…,f_{k-1}) = Λ_k(f_{k-1},…,f₀)`. An AP read backwards is the
AP with base point `x+(k-1)d` and common difference `−d`; the involution
`reflectShift` reindexes the average accordingly. -/
theorem kAPCount_reflect (k : ℕ) (f : Fin k → ZMod N → ℂ) :
    kAPCount k (fun i => f (Fin.rev i)) = kAPCount k f := by
  unfold kAPCount
  congr 1
  -- reduce to the double-sum identity, with the index reversal already applied
  have step : (∑ x : ZMod N, ∑ d : ZMod N,
        ∏ i : Fin k, f i (x + (Fin.rev i).val • d))
      = ∑ x : ZMod N, ∑ d : ZMod N, ∏ i : Fin k, f i (x + i.val • d) := by
    rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
    rw [← Equiv.sum_comp (Function.Involutive.toPerm _ (reflectShift_involutive (N := N) k))
          (fun p : ZMod N × ZMod N => ∏ i : Fin k, f i (p.1 + i.val • p.2))]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    refine Finset.prod_congr rfl (fun i _ => ?_)
    congr 1
    simp only [Function.Involutive.coe_toPerm, reflectShift]
    exact reflect_shift_eq k i p.1 p.2
  -- now insert the index reversal on the left
  rw [← step]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  refine Finset.sum_congr rfl (fun d _ => ?_)
  simpa using prod_rev_reindex k f x d

end RothTheoremOQ03OQ01
