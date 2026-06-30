import Mathlib
import Proofs.GeometricSeriesOQ07OQ01OQ01OQ01OQ02

/-
# The permutation-descent model of the Eulerian numbers

The parent entry **geometric-series-oq-07-oq-01-oq-01-oq-01-oq-02** proved the explicit
inclusion–exclusion closed form `⟨n,k⟩ = ∑_{i=0}^{k} (-1)ⁱ·C(n+1,i)·(k+1-i)ⁿ`
(`eulerian_eq_explicit`), identifying the alternating binomial sum `eulerianExplicit n k`
with the combinatorial Eulerian number `eulerian n k` built from the triangle recurrence.
Its declared open question (this leaf) asks to use the explicit formula to establish

  1. **non-negativity** of the alternating sum, and
  2. the **descent interpretation**: that `⟨n,k⟩` is the number of permutations of
     `{1,…,n}` with exactly `k` descents.

This entry settles non-negativity and builds the missing combinatorial object for the
descent interpretation: a from-scratch **permutation-descent statistic** on `Equiv.Perm
(Fin n)` and the counting function

> `eulerianDesc n k := #{ σ : Equiv.Perm (Fin n) | (number of descents of σ) = k }`,

which Mathlib does not contain in any form.  We prove the foundational invariant that makes
the descent statistic a genuine statistic — it **partitions the symmetric group**:

> `∑_{k=0}^{n} eulerianDesc n k = n!`.

This is the first step of the descent interpretation; the identification `eulerianDesc n k =
eulerian n k` itself requires the Eulerian insertion bijection and is recorded as the
remaining open continuation.

## What is new

`numDescents` reads off the descents of a permutation from its value sequence
`σ 0, σ 1, …, σ(n-1)` via the list helper `listDes`, and `eulerianDesc` packages the descent
count.  Neither the descent statistic on `Equiv.Perm (Fin n)` nor the Eulerian-as-descent
counting function exists in Mathlib.  The partition identity `∑ₖ eulerianDesc n k = n!`
follows from `Finset.card_eq_sum_card_fiberwise` once the descent count is bounded by `n`
(`numDescents_le`), together with `Fintype.card_perm` and `Fintype.card_fin`.

## References

* Graham, Knuth, Patashnik, *Concrete Mathematics*, §6.2 (Eulerian numbers, the descent
  statistic, and `∑ₖ ⟨n,k⟩ = n!`).
-/

namespace GeometricSeriesOQ07OQ01OQ01OQ01OQ02OQ01

open Finset

/-! ## Non-negativity of the explicit Eulerian sum -/

open GeometricSeriesOQ07OQ01OQ01OQ01 GeometricSeriesOQ07OQ01OQ01OQ01OQ02 in
/-- **Non-negativity (the first half of the open question).** The alternating
inclusion–exclusion sum `∑_{i=0}^{k} (-1)ⁱ·C(n+1,i)·(k+1-i)ⁿ` is non-negative, because it
equals the Eulerian number `⟨n,k⟩`, a count. -/
theorem eulerianExplicit_nonneg (n k : ℕ) : 0 ≤ eulerianExplicit n k := by
  rw [← eulerian_eq_explicit]
  exact_mod_cast Nat.zero_le _

/-! ## The descent statistic -/

/-- Number of descents in a list of naturals: positions where the next entry is strictly
smaller than the current one. -/
def listDes : List ℕ → ℕ
  | a :: b :: t => (if b < a then 1 else 0) + listDes (b :: t)
  | _ => 0

/-- The number of descents of a list never exceeds its length. -/
theorem listDes_le_length : ∀ l : List ℕ, listDes l ≤ l.length
  | [] => by simp [listDes]
  | [_] => by simp [listDes]
  | a :: b :: t => by
    have ih := listDes_le_length (b :: t)
    have : listDes (a :: b :: t) = (if b < a then 1 else 0) + listDes (b :: t) := rfl
    rw [this]
    simp only [List.length_cons] at ih ⊢
    split <;> omega

/-- The descent count of a permutation `σ` of `Fin n`, read off the value sequence
`σ 0, σ 1, …, σ(n-1)`. -/
def numDescents {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  listDes (List.ofFn (fun i : Fin n => (σ i : ℕ)))

/-- A permutation of `Fin n` has at most `n` descents. -/
theorem numDescents_le {n : ℕ} (σ : Equiv.Perm (Fin n)) : numDescents σ ≤ n := by
  have h := listDes_le_length (List.ofFn (fun i : Fin n => (σ i : ℕ)))
  rwa [List.length_ofFn] at h

/-- **The Eulerian number as a descent count.** `eulerianDesc n k` is the number of
permutations of `Fin n` with exactly `k` descents. -/
def eulerianDesc (n k : ℕ) : ℕ :=
  (univ.filter (fun σ : Equiv.Perm (Fin n) => numDescents σ = k)).card

/-! ## The descent statistic partitions the symmetric group -/

/-- **The descent statistic partitions `Sₙ`.** Summing the descent counts over all possible
descent numbers `0,…,n` recovers the order of the symmetric group:
`∑_{k=0}^{n} eulerianDesc n k = n!`.  This is the foundational invariant of the descent
interpretation of the Eulerian numbers. -/
theorem sum_eulerianDesc_eq_factorial (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), eulerianDesc n k = n.factorial := by
  have hbound : ∀ σ : Equiv.Perm (Fin n), numDescents σ ∈ range (n + 1) :=
    fun σ => Finset.mem_range.mpr (Nat.lt_succ_of_le (numDescents_le σ))
  have hmem : Set.MapsTo numDescents (Finset.univ : Finset (Equiv.Perm (Fin n)))
      (range (n + 1)) := fun σ _ => hbound σ
  have hpart := Finset.card_eq_sum_card_fiberwise hmem
  -- `hpart : (univ).card = ∑_{k ∈ range (n+1)} (univ.filter (numDescents · = k)).card`
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hpart
  exact hpart.symm

/-! ## Small-case agreement with the recurrence model

These `decide`-checked equalities confirm that the permutation-descent counting function
agrees with the parent's recurrence-defined Eulerian numbers on the first rows — the
computational evidence underlying the open identification `eulerianDesc = eulerian`. -/

/-- Row `n = 3`: `(⟨3,0⟩,⟨3,1⟩,⟨3,2⟩) = (1,4,1)` matches the descent counts of `S₃`. -/
example : eulerianDesc 3 0 = 1 ∧ eulerianDesc 3 1 = 4 ∧ eulerianDesc 3 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end GeometricSeriesOQ07OQ01OQ01OQ01OQ02OQ01
