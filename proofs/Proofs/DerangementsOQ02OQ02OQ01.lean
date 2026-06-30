/-
  Higher Factorial Moments of Fixed Points of a Random Permutation
  (derangements-oq-02-oq-02-oq-01)

  Open Question (from derangements-oq-02-oq-02): The parent established the *first*
  factorial moment of the fixed-point count X(σ) = |Fix(σ)| of a uniform random
  permutation of an n-element set:

      ∑_{σ : Perm(Fin n)} X(σ) = n!      i.e.   E[X] = 1.

  This file proves the **higher factorial moments**: for every k ≤ n,

      ∑_{σ : Perm(Fin n)} (X(σ))_k = n!      i.e.   E[(X)_k] = 1,

  where (X)_k = X·(X-1)···(X-k+1) = X.descFactorial k is the k-th falling
  factorial. Equivalently, every factorial moment of X equals 1 -- the exact
  finite-n signature of the Poisson(1) limit, whose factorial moments are all 1.

  **Main Result**:
  `sum_descFactorial_fixedPoints_eq_factorial`: For k ≤ n,
      ∑_{σ : Perm(Fin n)} ((Fix σ).card).descFactorial k = n!.

  **Proof Strategy** (Burnside on the action on ordered k-tuples):
  The parent proved the k = 1 case by Burnside's lemma applied to the action of
  Perm(Fin n) on Fin n. The higher moments arise from the *same* lemma applied to
  the action of Perm(Fin n) on the set of injective k-tuples `Fin k ↪ Fin n`
  (σ • f = σ ∘ f):

  1. The number of k-tuples fixed by σ equals (X(σ))_k. An embedding f is fixed by
     σ iff its image lands in Fix(σ); the count of such embeddings is
     |Fix(σ)|.descFactorial k  (Mathlib's `Fintype.card_embedding_eq`).
  2. Burnside: ∑_σ |Fix_emb(σ)| = (#orbits) · |Perm(Fin n)|.
  3. The symmetric group is k-transitive (`Equiv.Perm.isMultiplyPretransitive`), so
     for k ≤ n the embedding set is nonempty with a single orbit: #orbits = 1.
  4. Hence the sum is 1 · n! = n!.

  The factorial-moment-equals-1 phenomenon is thus a direct consequence of the
  k-transitivity of the full symmetric group.

  **Status**: All proved. 0 sorries, 0 `axiom` declarations, no `native_decide` in
  the main result. n theorems + helper equiv/lemma.
-/

import Proofs.DerangementsOQ02OQ02
import Mathlib.GroupTheory.GroupAction.Embedding
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Tactic

open Finset Fintype Nat Equiv.Perm BigOperators MulAction Function

namespace DerangementsOQ02OQ02OQ01

variable {n k : ℕ}

/-!
## Section I: Counting embeddings fixed by a permutation

An embedding `f : Fin k ↪ Fin n` is fixed by `σ` (under the action `σ • f = σ ∘ f`)
exactly when every value `f i` is a fixed point of `σ`. Such embeddings are in
bijection with embeddings of `Fin k` into the subtype of fixed points of `σ`.
-/

/-- Embeddings of `Fin k` into `Fin n` fixed by `σ` correspond bijectively to
    embeddings of `Fin k` into the set of fixed points of `σ`. -/
def fixedEmbEquiv (σ : Equiv.Perm (Fin n)) :
    {f : Fin k ↪ Fin n // σ • f = f} ≃ (Fin k ↪ {x : Fin n // σ x = x}) where
  toFun := fun ⟨f, hf⟩ =>
    ⟨fun i => ⟨f i, by
        have h := DFunLike.congr_fun hf i
        simpa only [Function.Embedding.smul_apply, Equiv.Perm.smul_def] using h⟩,
     fun i j h => f.injective (congrArg Subtype.val h)⟩
  invFun := fun g =>
    ⟨⟨fun i => (g i : Fin n), fun i j h => g.injective (Subtype.ext h)⟩, by
        ext i
        simp only [Function.Embedding.smul_apply, Equiv.Perm.smul_def,
          Function.Embedding.coeFn_mk]
        exact congrArg _ (g i).property⟩
  left_inv := fun ⟨f, hf⟩ => Subtype.ext (Function.Embedding.ext fun i => rfl)
  right_inv := fun g => Function.Embedding.ext fun i => Subtype.ext rfl

/-- **Key count**: the number of embeddings `Fin k ↪ Fin n` fixed by `σ` equals the
    `k`-th falling factorial of `|Fix(σ)|`. -/
lemma card_fixedBy_emb (σ : Equiv.Perm (Fin n)) :
    Fintype.card (MulAction.fixedBy (Fin k ↪ Fin n) σ) =
      ((Finset.univ.filter fun x => σ x = x).card).descFactorial k := by
  -- ↥(fixedBy _ σ) ≃ {f // σ • f = f} ≃ (Fin k ↪ fixed-point subtype)
  rw [Fintype.card_congr
        ((Equiv.subtypeEquivRight fun f => MulAction.mem_fixedBy).trans (fixedEmbEquiv σ)),
      Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_subtype]

/-!
## Section II: Main theorem via Burnside's lemma

The action of `Perm(Fin n)` on `Fin k ↪ Fin n` is transitive for `k ≤ n`
(k-transitivity of the symmetric group), so Burnside's lemma collapses to a single
orbit and the moment sum equals `n!`.
-/

set_option maxHeartbeats 1000000 in
/-- **Higher factorial moments**: For `k ≤ n`,
      ∑_{σ : Perm(Fin n)} (|Fix(σ)|)_k = n!.
    Equivalently, the `k`-th factorial moment of the fixed-point count of a uniform
    random permutation of `Fin n` equals `1`.

    **Proof**: Burnside's lemma applied to the action of `Perm(Fin n)` on the ordered
    `k`-tuples `Fin k ↪ Fin n`. Each summand `(|Fix(σ)|)_k` counts the `k`-tuples
    fixed by `σ` (`card_fixedBy_emb`). Since the symmetric group is `k`-transitive,
    for `k ≤ n` the (nonempty) tuple set forms a single orbit, so the sum is
    `1 · |Perm(Fin n)| = n!`. -/
theorem sum_descFactorial_fixedPoints_eq_factorial (hk : k ≤ n) :
    ∑ σ : Equiv.Perm (Fin n),
      ((Finset.univ.filter fun x => σ x = x).card).descFactorial k = n.factorial := by
  -- Convert each summand into the count of embeddings fixed by σ.
  simp_rw [← card_fixedBy_emb]
  -- The symmetric group is k-transitive: it acts pretransitively on Fin k ↪ Fin n.
  haveI hpre : MulAction.IsPretransitive (Equiv.Perm (Fin n)) (Fin k ↪ Fin n) :=
    Equiv.Perm.isMultiplyPretransitive (Fin n) k
  -- For k ≤ n the embedding set is nonempty.
  haveI hne : Nonempty (Fin k ↪ Fin n) := ⟨(Fin.castLEOrderEmb hk).toEmbedding⟩
  -- Hence the orbit quotient is a singleton.
  haveI huniq : Unique (orbitRel.Quotient (Equiv.Perm (Fin n)) (Fin k ↪ Fin n)) :=
    (MulAction.pretransitive_iff_unique_quotient_of_nonempty
      (G := Equiv.Perm (Fin n)) (α := Fin k ↪ Fin n)).mp inferInstance |>.some
  haveI hfinΩ : Fintype (orbitRel.Quotient (Equiv.Perm (Fin n)) (Fin k ↪ Fin n)) :=
    Unique.fintype
  -- Burnside: ∑_σ |Fix_emb(σ)| = |Ω| · |G|.
  rw [MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
      (α := Equiv.Perm (Fin n)) (β := Fin k ↪ Fin n)]
  rw [Fintype.card_unique, one_mul, Fintype.card_perm, Fintype.card_fin]

/-!
## Section III: Consequences and interpretation
-/

/-- The first factorial moment (`k = 1`) recovers the parent's expected-fixed-points
    result `∑_σ |Fix(σ)| = n!` as a special case. -/
theorem sum_fixedPoints_eq_factorial_via_moment (hn : 1 ≤ n) :
    ∑ σ : Equiv.Perm (Fin n),
      (Finset.univ.filter fun x => σ x = x).card = n.factorial := by
  have h := sum_descFactorial_fixedPoints_eq_factorial (n := n) (k := 1) hn
  simpa only [Nat.descFactorial_one] using h

/-- **Factorial moment equals one**: for `k ≤ n` the moment sum equals
    `|Perm(Fin n)| = n!`. Dividing by the number of permutations `n!` gives the
    normalized `k`-th factorial moment `E[(X)_k] = 1`. -/
theorem moment_sum_eq_card_perm (hk : k ≤ n) :
    ∑ σ : Equiv.Perm (Fin n),
      ((Finset.univ.filter fun x => σ x = x).card).descFactorial k =
      Fintype.card (Equiv.Perm (Fin n)) := by
  rw [sum_descFactorial_fixedPoints_eq_factorial hk, Fintype.card_perm, Fintype.card_fin]

/-- **Second factorial moment** (`k = 2`): `∑_σ |Fix(σ)|·(|Fix(σ)|-1) = n!` for
    `n ≥ 2`. Together with the first moment this yields the variance
    `Var(X) = E[X(X-1)] + E[X] - (E[X])² = 1 + 1 - 1 = 1`, i.e. `Var(X) = 1`. -/
theorem sum_second_factorial_moment (hn : 2 ≤ n) :
    ∑ σ : Equiv.Perm (Fin n),
      ((Finset.univ.filter fun x => σ x = x).card) *
        ((Finset.univ.filter fun x => σ x = x).card - 1) = n.factorial := by
  have h := sum_descFactorial_fixedPoints_eq_factorial (n := n) (k := 2) hn
  -- descFactorial _ 2 = X * (X - 1)
  have hd : ∀ m : ℕ, m.descFactorial 2 = m * (m - 1) := fun m => by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.descFactorial_succ, Nat.descFactorial_one,
      Nat.mul_comm]
  simp_rw [hd] at h
  exact h

/-- For `k > n` every summand vanishes (no permutation has more than `n` fixed
    points), so the higher-`k` moment sum is `0`, sharply distinguishing it from the
    `k ≤ n` regime where the sum is `n!`. -/
theorem sum_descFactorial_fixedPoints_eq_zero (hk : n < k) :
    ∑ σ : Equiv.Perm (Fin n),
      ((Finset.univ.filter fun x => σ x = x).card).descFactorial k = 0 := by
  apply Finset.sum_eq_zero
  intro σ _
  apply Nat.descFactorial_eq_zero_iff_lt.mpr
  calc (Finset.univ.filter fun x => σ x = x).card
      ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp
    _ < k := hk

end DerangementsOQ02OQ02OQ01
