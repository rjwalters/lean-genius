import Mathlib.Computability.Reduce
import Mathlib.Computability.Partrec
import Mathlib.Computability.Primrec
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-
# Myhill's Isomorphism Theorem (1955)

## Open Question (OQ-03)
"Myhill's isomorphism theorem (1955): computable injections yield a computable bijection.
Can this be formalized using Lean's Computable typeclasses?"

## Answer
Yes. The Myhill Isomorphism Theorem states that two sets A, B ⊆ ℕ are one-one equivalent
(OneOneEquiv) if and only if there exists a computable bijection (a computable permutation
of ℕ) mapping A to B.

This is the computable version of the Schroder-Bernstein theorem: classical CBS gives ANY
bijection from two injections; Myhill's theorem gives a COMPUTABLE bijection from two
computable injections.

## Formalization Strategy

We formalize in the Primcodable typeclass setting (matching Mathlib's Computability.Reduce).

### Easy direction: Computable bijection → one-one equivalence
Given a computable bijection e : ℕ ≃ ℕ mapping p to q:
- e witnesses p ≤₁ q (computable injection with p n ↔ q (e n))
- e.symm witnesses q ≤₁ p (computable injection with q m ↔ p (e.symm m))

### Hard direction: One-one equivalence → computable bijection
Given computable injections f: p ≤₁ q and g: q ≤₁ p, construct a computable
bijection σ via the "back-and-forth" method:

Orbit classification: For each n, consider the backward chain:
    n ← g⁻¹(n) ← f⁻¹(g⁻¹(n)) ← g⁻¹(f⁻¹(g⁻¹(n))) ← ...

The chain terminates (at a "base" element not in range g or range f) or is infinite.
  - Type A: terminates outside range(g); use σ(n) = f(n)
  - Type B: terminates outside range(f); thread g⁻¹
  - Type C (infinite): use f(n)

Computability: Since f, g are computable injections, their partial inverses are
computable via Partrec.rfind. The orbit type is determined by bounded search.

## Status
- myhill_easy: proved (computable bijection → one-one equivalence)
- one_one_equiv_of_computable_perm: proved
- myhill_self, myhill_symm, myhill_trans: proved (reflexivity/symmetry/transitivity)
- myhill_isomorphism: hard direction has sorry (open: back-and-forth construction)

## References
- Myhill, J. (1955). "Creative sets." Z. Math. Logik Grundlag. Math. 1, 97–108.
- Rogers, H. (1967). Theory of Recursive Functions and Effective Computability.
  MIT Press. Chapter 7, §7.4, Theorem VII.
- Soare, R. (2016). Turing Computability. Springer. Chapter 3.
-/

open Primcodable Function Computable

namespace MyhillIsomorphism

/-!
## Section 1: Setup and Definitions
-/

/-- A predicate p **corresponds under e** to q if forall n, p n ↔ q (e n). -/
def Corresponds (p : ℕ → Prop) (e : ℕ ≃ ℕ) (q : ℕ → Prop) : Prop :=
  ∀ n, p n ↔ q (e n)

/-!
## Section 2: Easy Direction (Computable Bijection → One-One Equivalence)
-/

/-- **Myhill Easy Direction**: A computable permutation e with p n ↔ q (e n)
    implies p and q are one-one equivalent.

    Proof: e witnesses p ≤₁ q; e.symm witnesses q ≤₁ p. -/
theorem myhill_easy {p q : ℕ → Prop}
    (e : ℕ ≃ ℕ) (he : e.Computable) (hpq : Corresponds p e q) :
    OneOneEquiv p q := by
  constructor
  · exact ⟨e, he.1, e.injective, hpq⟩
  · refine ⟨e.symm, he.2, e.symm.injective, fun n => ?_⟩
    have := hpq (e.symm n)
    simp only [Equiv.apply_symm_apply] at this
    exact this.symm

/-- Variant with explicit computability hypotheses. -/
theorem one_one_equiv_of_computable_perm {p q : ℕ → Prop}
    (e : ℕ ≃ ℕ) (hef : Computable (e : ℕ → ℕ)) (heb : Computable (e.symm : ℕ → ℕ))
    (hpq : ∀ n, p n ↔ q (e n)) : OneOneEquiv p q :=
  myhill_easy e ⟨hef, heb⟩ hpq

/-!
## Section 3: Infrastructure for the Hard Direction
-/

/-- Given a computable injection g : ℕ → ℕ, its partial inverse is partial recursive:
    g⁻¹(m) = the unique n with g(n) = m, if it exists.
    Uses Nat.rfind to search for the preimage. -/
def partialInverse (g : ℕ → ℕ) : ℕ →. ℕ :=
  fun m => (Nat.rfind fun n => decide (g n = m))

/-- The partial inverse is partial-recursive when g is computable.
    Proof: (m, n) ↦ decide (g n = m) is Computable₂ since g is computable,
    so Partrec.rfind applies.
    [Detailed proof requires Computable₂ API — see Mathlib.Computability.Partrec] -/
theorem partialInverse_partrec {g : ℕ → ℕ} (hg : Computable g) :
    Partrec (partialInverse g) := by
  sorry

/-- The partial inverse recovers the input under a computable injection. -/
theorem partialInverse_spec {g : ℕ → ℕ} (hg_inj : Injective g)
    {m n : ℕ} (h : n ∈ partialInverse g m) : g n = m := by
  sorry

/-- Elements in range(g) have a partial inverse defined. -/
theorem partialInverse_dom {g : ℕ → ℕ} {m : ℕ} (hm : ∃ k, g k = m) :
    (partialInverse g m).Dom := by
  sorry

/-!
## Section 4: Orbit Structure for the Back-and-Forth

For computable injections f, g, the orbit of n under iterated (g∘f) is computable.
The orbit structure determines which injection to use in the bijection.
-/

/-- Forward orbit: (g∘f)^k (n). This is always computable. -/
def fwdOrbit (f g : ℕ → ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => g (f (fwdOrbit f g n k))

/-- The back-and-forth strategy: an element n is "f-type" if its backward chain
    under alternating g⁻¹, f⁻¹ terminates outside range(g) (i.e., not a g-image).
    These are exactly the elements where σ(n) := f(n) is the right choice.

    For elements where the chain never terminates (infinite orbits), we also use f. -/
def isGFree (g : ℕ → ℕ) (n : ℕ) : Prop := ∀ k, g k ≠ n

/-!
## Section 5: The Myhill Isomorphism Theorem
-/

/-- **Myhill's Isomorphism Theorem (1955)**

    For predicates p, q : ℕ → Prop:
    OneOneEquiv p q ↔ ∃ computable permutation e with ∀ n, p n ↔ q (e n).

    **Proof (← direction)**: Immediate from myhill_easy.

    **Proof (→ direction)**: Given computable injections f, g:
    - f computable injective, ∀ n, p n ↔ q (f n)
    - g computable injective, ∀ n, q n ↔ p (g n)

    Construct σ via the back-and-forth priority argument (Rogers §7.4):
    At stage s = 0, 1, 2, ...:
      Stage 2k: Ensure k ∈ dom(σ_s). If not, set σ_s(k) = f(k).
      Stage 2k+1: Ensure k ∈ range(σ_s). If not, extend σ to map g(k) → k.

    The resulting σ is total, bijective, and computable because:
    (a) Each stage terminates (finite adjustment using injectivity of f and g)
    (b) The domain/range exhaustion covers all of ℕ (every n added by stage 2n+1)
    (c) Membership condition p n ↔ q (σ n) preserved by the back-and-forth
    (d) Computability: σ(n) is determined by the finite stage at which n enters dom

    [OPEN: ~200 lines of Partrec-based formalization for the priority construction] -/
theorem myhill_isomorphism (p q : ℕ → Prop) :
    OneOneEquiv p q ↔
    ∃ e : ℕ ≃ ℕ, e.Computable ∧ ∀ n, p n ↔ q (e n) := by
  constructor
  · intro ⟨⟨f, hfc, hfi, hfpq⟩, ⟨g, hgc, hgi, hgpq⟩⟩
    -- Hard direction: construct computable bijection via back-and-forth
    -- The priority construction at each stage extends the partial bijection
    -- by one element, using f or g depending on the domain/range gap.
    -- Key computability fact: partialInverse_partrec gives computable g⁻¹.
    -- Key bijectivity fact: f, g injective ensures no collisions.
    sorry
  · rintro ⟨e, he, hpq⟩
    exact myhill_easy e he hpq

/-!
## Section 6: Immediate Corollaries
-/

/-- Every predicate is computably isomorphic to itself (identity permutation). -/
theorem myhill_self (p : ℕ → Prop) :
    ∃ e : ℕ ≃ ℕ, e.Computable ∧ ∀ n, p n ↔ p (e n) :=
  ⟨Equiv.refl ℕ, ⟨Computable.id, Computable.id⟩, fun _ => Iff.rfl⟩

/-- The relation "computably isomorphic" is symmetric:
    the inverse permutation is also computable. -/
theorem myhill_symm {p q : ℕ → Prop}
    (e : ℕ ≃ ℕ) (he : e.Computable) (hpq : ∀ n, p n ↔ q (e n)) :
    ∃ e' : ℕ ≃ ℕ, e'.Computable ∧ ∀ n, q n ↔ p (e' n) := by
  refine ⟨e.symm, he.symm, fun n => ?_⟩
  have h := hpq (e.symm n)
  simp only [Equiv.apply_symm_apply] at h
  exact h.symm

/-- The relation "computably isomorphic" is transitive:
    composition of computable permutations is computable. -/
theorem myhill_trans {p q r : ℕ → Prop}
    (e₁ : ℕ ≃ ℕ) (he₁ : e₁.Computable) (hpq : ∀ n, p n ↔ q (e₁ n))
    (e₂ : ℕ ≃ ℕ) (he₂ : e₂.Computable) (hqr : ∀ n, q n ↔ r (e₂ n)) :
    ∃ e : ℕ ≃ ℕ, e.Computable ∧ ∀ n, p n ↔ r (e n) :=
  ⟨e₁.trans e₂, he₁.trans he₂, fun n => (hpq n).trans (hqr (e₁ n))⟩

/-!
## Section 7: Connection to OneOneEquiv Structure
-/

/-- **OneOneEquiv implies computable isomorphism** (hard direction, as instance). -/
theorem exists_computable_perm_of_one_one_equiv {p q : ℕ → Prop}
    (h : OneOneEquiv p q) :
    ∃ e : ℕ ≃ ℕ, e.Computable ∧ ∀ n, p n ↔ q (e n) :=
  (myhill_isomorphism p q).mp h

/-- **Computable isomorphism implies OneOneEquiv** (easy direction). -/
theorem one_one_equiv_of_computable_iso {p q : ℕ → Prop}
    (e : ℕ ≃ ℕ) (he : e.Computable) (h : ∀ n, p n ↔ q (e n)) :
    OneOneEquiv p q :=
  myhill_easy e he h

/-- **The computable isomorphism relation is an equivalence relation** on predicates ℕ → Prop.
    Reflexivity, symmetry, and transitivity all follow from operations on computable permutations. -/
theorem computable_iso_is_equivalence :
    Equivalence (fun p q : ℕ → Prop =>
      ∃ e : ℕ ≃ ℕ, e.Computable ∧ ∀ n, p n ↔ q (e n)) :=
  ⟨fun p => myhill_self p,
   fun ⟨e, he, hpq⟩ => myhill_symm e he hpq,
   fun ⟨e₁, he₁, hpq⟩ ⟨e₂, he₂, hqr⟩ => myhill_trans e₁ he₁ hpq e₂ he₂ hqr⟩

/-!
## Section 8: Key Special Cases
-/

/-- The empty predicate is computably isomorphic only to the empty predicate.
    (Any permutation maps ∅ to ∅.) -/
theorem myhill_empty_unique {p : ℕ → Prop}
    (e : ℕ ≃ ℕ) (he : e.Computable) (h : ∀ n, False ↔ p (e n)) :
    ∀ n, ¬ p n := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, e m = n := e.surjective n
  exact (h m).mpr hn

/-- The universal predicate (always true) is computably isomorphic only to itself. -/
theorem myhill_univ_unique {p : ℕ → Prop}
    (e : ℕ ≃ ℕ) (he : e.Computable) (h : ∀ n, True ↔ p (e n)) :
    ∀ n, p n := by
  intro n
  obtain ⟨m, rfl⟩ : ∃ m, e m = n := e.surjective n
  exact (h m).mp True.intro

end MyhillIsomorphism
