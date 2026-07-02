import Mathlib
import Proofs.Erdos1012Problem

/-
# Decidability and the Brute-Force Search Space for (n−k)-Cycle Detection (OQ-05)

## The Open Question

`Erdos1012Problem.lean` (Erdős #1012, long cycles in dense graphs) lists as its
fifth open question:

  **OQ-05.** What is the computational complexity of determining whether a given
  graph with `T(n,k) − 1` edges contains an `(n − k)`-cycle?

A full answer — a polynomial-time algorithm, or an NP-hardness reduction — is far
beyond what can be formalized against current Mathlib.  What *can* be pinned down,
honestly and completely, is the **computational core** the question presupposes:
that for a *fixed finite graph* the decision problem is **algorithmically
solvable** (`Decidable`), and that it is solvable by an explicit **finite
brute-force search** whose search space we can count exactly.

## What This File Proves

- `decidableHasCycleOfLength` : for a fixed finite graph, "contains a cycle of
  length ℓ" is `Decidable` — an actual decision procedure exists.
- `decidableIsHamiltonian`, `decidableIsPancyclicUpTo` : the derived predicates
  are decidable too.
- `hasCycleOfLength_iff_exists_mem_univ` : detection is literally a search over
  the finite set of candidate vertex sequences.
- `searchSpace_card` : that candidate set has exactly `|V| ^ ℓ` elements — the
  explicit (exponential) size of the brute-force search.
- `hamiltonianSearchSpace_card` : the Hamiltonian search space has `n ^ n`
  candidates.
- Concrete computations (`triangle_has_3cycle`, `edgeless_no_3cycle`) showing the
  decision procedure genuinely *runs* via `decide`.

## What This File Does NOT Claim

It does **not** give a polynomial-time algorithm, and it does **not** prove any
hardness result.  The `|V| ^ ℓ` bound is exponential; whether the restricted
instances at `T(n,k) − 1` edges admit a faster algorithm, and whether the general
problem is NP-hard, both remain open — that is exactly the content of OQ-05.  This
file delimits the *decidable, finitely-searchable* skeleton on which any future
complexity analysis rests.
-/

namespace Erdos1012OQ05

open Erdos1012

variable {V : Type*} [Fintype V] [DecidableEq V]

/-!
## Part I: The decision problem is decidable

For a fixed finite graph, membership of a cycle of a given length is a
`Fintype`-bounded existential over a decidable predicate, hence decidable.
-/

/-- There is no cycle of length `0` — the base case of `hasCycleOfLength`. -/
theorem not_hasCycleOfLength_zero (G : SimpleGraph V) :
    ¬ hasCycleOfLength G 0 := by
  simp [hasCycleOfLength]

/-- **The core computational fact.** For a fixed finite graph `G`, the predicate
    "`G` contains a cycle of length `ℓ`" is `Decidable`: there is an algorithm
    that, given `G` and `ℓ`, decides it.  This is the decidable skeleton that any
    complexity analysis of OQ-05 sits on top of. -/
instance decidableHasCycleOfLength (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ ℓ, Decidable (hasCycleOfLength G ℓ)
  | 0 => decidable_of_iff False (by simp [hasCycleOfLength])
  | l + 1 => by
      unfold hasCycleOfLength
      infer_instance

/-- Hamiltonicity is decidable for a fixed finite graph. -/
instance decidableIsHamiltonian (G : SimpleGraph V) [DecidableRel G.Adj] :
    Decidable (isHamiltonian G) :=
  decidableHasCycleOfLength G _

/-- Reformulate pancyclicity as a bounded search over cycle lengths `3 … m`. -/
theorem isPancyclicUpTo_iff (G : SimpleGraph V) (m : ℕ) :
    isPancyclicUpTo G m ↔ ∀ l ∈ Finset.Icc 3 m, hasCycleOfLength G l := by
  simp only [isPancyclicUpTo, Finset.mem_Icc, and_imp]

/-- Pancyclicity up to `m` is decidable for a fixed finite graph. -/
instance decidableIsPancyclicUpTo (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) :
    Decidable (isPancyclicUpTo G m) :=
  decidable_of_iff _ (isPancyclicUpTo_iff G m).symm

/-!
## Part II: Detection is a finite brute-force search

`hasCycleOfLength G (l+1)` is exactly the statement that *some* candidate vertex
sequence in the finite type `Fin (l+1) → V` is an injective closed walk.  We make
the "search a finite set" reading explicit and count the search space.
-/

/-- **Detection as finite search.** A cycle of length `l+1` exists iff some
    candidate map `c : Fin (l+1) → V` in the (finite) universe is an injective
    closed walk in `G`.  This is the brute-force decision procedure spelled out. -/
theorem hasCycleOfLength_iff_exists_mem_univ (G : SimpleGraph V) (l : ℕ) :
    hasCycleOfLength G (l + 1) ↔
      ∃ c ∈ (Finset.univ : Finset (Fin (l + 1) → V)),
        Function.Injective c ∧
          ∀ i : Fin (l + 1),
            G.Adj (c i) (c ⟨(i.val + 1) % (l + 1), Nat.mod_lt _ (by omega)⟩) := by
  simp only [Finset.mem_univ, true_and]
  rfl

/-- **The size of the brute-force search space.** The set of candidate cycle maps
    `Fin ℓ → V` has exactly `|V| ^ ℓ` elements.  This is the explicit (exponential)
    cost of the naive decision procedure. -/
theorem searchSpace_card (ℓ : ℕ) :
    Fintype.card (Fin ℓ → V) = Fintype.card V ^ ℓ := by
  simp [Fintype.card_fin]

/-- The Hamiltonian brute-force search space on `n` vertices has `n ^ n`
    candidate vertex sequences. -/
theorem hamiltonianSearchSpace_card :
    Fintype.card (Fin (Fintype.card V) → V) = Fintype.card V ^ Fintype.card V :=
  searchSpace_card _

/-!
## Part III: The decision procedure actually runs

The instance above is computable, so `decide` evaluates concrete cases.  These
witness that the formalized decision problem is not merely classically decidable
but genuinely executable.
-/

/-- The triangle `K₃` contains a `3`-cycle — decided by executing the procedure. -/
theorem triangle_has_3cycle :
    hasCycleOfLength (⊤ : SimpleGraph (Fin 3)) 3 := by decide

/-- The edgeless graph on `3` vertices contains no `3`-cycle. -/
theorem edgeless_no_3cycle :
    ¬ hasCycleOfLength (⊥ : SimpleGraph (Fin 3)) 3 := by decide

/-- The edgeless graph on any finite vertex set is not Hamiltonian
    (whenever there is at least one vertex to visit). -/
theorem edgeless_not_hamiltonian_fin3 :
    ¬ isHamiltonian (⊥ : SimpleGraph (Fin 3)) := by decide

end Erdos1012OQ05
