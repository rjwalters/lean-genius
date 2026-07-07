import Proofs.KroneckersJugendtraum
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

/-
# Kronecker's Jugendtraum (Hilbert's 12th): real quadratic fields are abelian over ℚ

## Context: the open case

Hilbert's 12th problem asks for *explicit generators* of the abelian extensions of a number
field `K`. It is solved for `K = ℚ` (Kronecker–Weber: roots of unity) and for imaginary
quadratic `K` (complex multiplication: `j`-invariants and CM torsion). The first genuinely
open case is the **real quadratic** fields `K = ℚ(√d)`, `d > 0`: no analogue of CM theory is
known, and the conjectural answers live in the Stark conjectures.

It is easy to misread "open for real quadratic fields" as "we do not know the abelian
extensions of `ℚ` that *are* real quadratic fields". That is false, and this file pins down
exactly why. A real quadratic field is itself a degree-`2` extension of `ℚ`; being of prime
degree and (in characteristic `0`) Galois, its Galois group is **cyclic**, hence **abelian**.
So a real quadratic field is an abelian extension *of* `ℚ`, and Kronecker–Weber already gives
it explicit (cyclotomic) generators: `√d` sits inside a cyclotomic field. What Hilbert's 12th
leaves open is the far larger family of abelian extensions built *over* the real quadratic
field `K` — extensions of `K` that are not abelian over `ℚ`.

## Main results

* `galois_prime_degree_isCyclic` / `galois_prime_degree_abelian` — the general engine: a
  Galois extension of **prime degree** `p` has cyclic (hence abelian) Galois group. Proof:
  `|Gal(L/K)| = [L : K] = p` (`IsGalois.card_aut_eq_finrank`), and a finite group of prime
  order is cyclic (`isCyclic_of_prime_card`), and cyclic groups are commutative.
* `quadratic_galois_abelian` — the `p = 2` specialization: every quadratic Galois extension
  is abelian. Covers both real and imaginary quadratic fields uniformly.
* `realQuadratic_galois_isAbelian` — a real quadratic field that is Galois over `ℚ` is an
  `IsAbelianExtension ℚ K` in the sense of the parent file `KroneckersJugendtraum.lean`.
* `imaginaryQuadratic_galois_isAbelian` — the same for imaginary quadratic fields, recording
  that the abelian-over-`ℚ` conclusion is agnostic to the real/imaginary split; what differs
  between the two cases is only the *effective* generator problem (CM vs. Stark).

These are fully machine-checked with no axioms and no `sorry`; the parent file's four deep
milestones (Kronecker–Weber, CM, Artin reciprocity, Stark) remain axiomatized placeholders.
This file adds the small, honest, unconditional fact those placeholders sit on top of.
-/

noncomputable section

namespace KroneckersJugendtraum

/-! ## The prime-degree engine -/

/-- **A Galois extension of prime degree has cyclic Galois group.**

If `[L : K] = p` with `p` prime and `L/K` Galois, then `Gal(L/K)` is a finite group whose
order is the prime `p` (`IsGalois.card_aut_eq_finrank`), and any finite group of prime order
is cyclic. -/
theorem galois_prime_degree_isCyclic {p : ℕ} [Fact p.Prime]
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = p) :
    IsCyclic (L ≃ₐ[K] L) := by
  have hcard : Nat.card (L ≃ₐ[K] L) = p := by
    rw [IsGalois.card_aut_eq_finrank, hdeg]
  exact isCyclic_of_prime_card hcard

/-- **A Galois extension of prime degree is abelian.**

The Galois group is cyclic (`galois_prime_degree_isCyclic`), and cyclic groups are
commutative. -/
theorem galois_prime_degree_abelian {p : ℕ} [Fact p.Prime]
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = p) :
    ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ := by
  haveI := galois_prime_degree_isCyclic K L hdeg
  letI : CommGroup (L ≃ₐ[K] L) := IsCyclic.commGroup
  exact fun σ τ => mul_comm σ τ

/-! ## The quadratic specialization -/

/-- **Every quadratic Galois extension is abelian.**

Instantiates the prime-degree engine at `p = 2`. This covers both real and imaginary
quadratic number fields, and more generally any degree-`2` Galois extension of any field. -/
theorem quadratic_galois_abelian
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 2) :
    ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact galois_prime_degree_abelian K L hdeg

/-- **A real quadratic field, if Galois over `ℚ`, is an abelian extension of `ℚ`.**

Uses the parent file's `IsRealQuadratic` (degree `2`, all embeddings real) and produces an
`IsAbelianExtension ℚ K`. Combined with Kronecker–Weber this says: the real quadratic field
`ℚ(√d)` itself is cyclotomic, so its generator `√d` is explicit. The genuinely *open* part of
Hilbert's 12th is the abelian extensions built over `K`, not `K` itself. -/
theorem realQuadratic_galois_isAbelian
    (K : Type*) [Field K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (h : IsRealQuadratic K) :
    IsAbelianExtension ℚ K :=
  ⟨inferInstance, quadratic_galois_abelian ℚ K h.1⟩

/-- **An imaginary quadratic field, if Galois over `ℚ`, is an abelian extension of `ℚ`.**

The abelian-over-`ℚ` conclusion is identical to the real case: what distinguishes imaginary
quadratic fields is not whether they are abelian over `ℚ` (they are, trivially, being
quadratic) but that Hilbert's 12th is *solved* for the extensions built over them, via
complex multiplication — the case that is still open for real quadratic fields. -/
theorem imaginaryQuadratic_galois_isAbelian
    (K : Type*) [Field K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (h : IsImaginaryQuadratic K) :
    IsAbelianExtension ℚ K :=
  ⟨inferInstance, quadratic_galois_abelian ℚ K h.1⟩

end KroneckersJugendtraum
