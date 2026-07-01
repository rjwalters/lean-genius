import Mathlib.Computability.Reduce
import Mathlib.Computability.Partrec
import Mathlib.Computability.Halting
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
- partialInverse_{spec,dom,unique}: proved (partial-inverse API for the hard direction)
- fwdOrbit_eq_iterate: proved (forward orbit = iteration of g∘f; forward direction is computable)
- isGFree_iff_not_mem_range: proved — pins down WHY the naive orbit classification is
  not computable: `isGFree` is Π₁ (complement of the c.e. set `range g`), hence undecidable
- partialInverse_dom_iff_mem_range / mem_range_re / not_isGFree_re: proved — the Σ₁/Π₁
  complexity claim made machine-checked: `range g` is `REPred` (c.e.) for computable `g`
  (its the domain of `partialInverse g`), so `isGFree g` is co-c.e. (Π₁)
- decidableIsGFree: proved — the Π₁ obstruction becomes decidable once `range g` is decidable
- totalInverse_{mem,right,left,computable}: proved — a surjective computable injection has a
  total, computable two-sided inverse (partialInverse becomes everywhere-defined)
- computable_bijection_isComputablePerm / oneOneEquiv_of_computable_bijection: proved — the
  fully computable easy case (Myhill when the reductions are already bijections)
- myhill_isomorphism: hard direction has sorry (open: stage-wise back-and-forth construction)

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
  unfold partialInverse
  apply Partrec.rfind
  apply Computable₂.partrec₂
  -- (m, n) ↦ decide (g n = m) is computable: equality of naturals is primitive
  -- recursive, and g is computable.
  have heq0 : Primrec₂ (fun a b : ℕ => decide (a = b)) := Primrec.eq.decide
  have heq : Computable₂ (fun a b : ℕ => decide (a = b)) := heq0.to_comp
  exact heq.comp (hg.comp Computable.snd) Computable.fst

/-- The partial inverse recovers the input under a computable injection.
    (Injectivity is not needed: `rfind` returns a witness `n` with `g n = m`.) -/
theorem partialInverse_spec {g : ℕ → ℕ} (_hg_inj : Injective g)
    {m n : ℕ} (h : n ∈ partialInverse g m) : g n = m := by
  have hspec := Nat.rfind_spec h
  simpa using hspec

/-- Elements in range(g) have a partial inverse defined.
    A witness `g k = m` makes the bounded `rfind` search terminate. -/
theorem partialInverse_dom {g : ℕ → ℕ} {m : ℕ} (hm : ∃ k, g k = m) :
    (partialInverse g m).Dom := by
  obtain ⟨k, hk⟩ := hm
  rw [partialInverse, Nat.rfind_dom']
  exact ⟨k, by simp [hk], fun _ => trivial⟩

/-- The partial inverse is **single-valued** under an injective `g`: any two
    values returned for the same `m` coincide. This is the bijectivity fact the
    back-and-forth construction needs — extending the partial map by a `g`-edge
    can never collide, because preimages under an injection are unique. -/
theorem partialInverse_unique {g : ℕ → ℕ} (hg_inj : Injective g)
    {m n₁ n₂ : ℕ} (h₁ : n₁ ∈ partialInverse g m) (h₂ : n₂ ∈ partialInverse g m) :
    n₁ = n₂ :=
  hg_inj (by rw [partialInverse_spec hg_inj h₁, partialInverse_spec hg_inj h₂])

/-!
## Section 4: Orbit Structure for the Back-and-Forth

For computable injections f, g, the orbit of n under iterated (g∘f) is computable.
The orbit structure determines which injection to use in the bijection.
-/

/-- Forward orbit: (g∘f)^k (n). This is always computable. -/
def fwdOrbit (f g : ℕ → ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => g (f (fwdOrbit f g n k))

/-- The forward orbit is exactly iteration of `g ∘ f`, identifying `fwdOrbit`
    with Mathlib's `Function.iterate` (unlocking its API). Since `fun x => g (f x)`
    is computable whenever `f` and `g` are, the *forward* orbit is unproblematically
    computable — the difficulty in Myhill's construction lies entirely in the
    *backward* direction (see the note on `isGFree` below). -/
theorem fwdOrbit_eq_iterate (f g : ℕ → ℕ) (n k : ℕ) :
    fwdOrbit f g n k = (fun x => g (f x))^[k] n := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [fwdOrbit, ih, Function.iterate_succ_apply']

/-- **The forward orbit is computable**, as a two-argument function of the base
    point `n` and the iteration count `k`: `fwdOrbit f g` is `Computable₂` whenever
    `f` and `g` are computable. This discharges (with an actual machine-checked
    `Computable` certificate) the prose remark on `fwdOrbit_eq_iterate` that the
    *forward* direction of the orbit is unproblematic — the computability difficulty
    in Myhill's construction lies entirely in the *backward* direction, where
    deciding `range g` membership (`isGFree`, below) is `Π₁`.

    The proof identifies `fwdOrbit f g n` with `Nat.rec` on the iteration count and
    applies `Computable.nat_rec`, whose step function `IH ↦ g (f IH)` is computable
    because `f` and `g` are. -/
theorem fwdOrbit_computable {f g : ℕ → ℕ} (hf : Computable f) (hg : Computable g) :
    Computable₂ (fwdOrbit f g) := by
  have key : ∀ (n k : ℕ), fwdOrbit f g n k
      = Nat.rec (motive := fun _ => ℕ) n (fun _ IH => g (f IH)) k := by
    intro n k
    induction k with
    | zero => rfl
    | succ k ih => rw [fwdOrbit, ih]
  have h := Computable.nat_rec (α := ℕ × ℕ) (σ := ℕ)
    (f := fun a => a.2) (g := fun a => a.1)
    (h := fun (_ : ℕ × ℕ) (p : ℕ × ℕ) => g (f p.2))
    Computable.snd Computable.fst
    ((hg.comp (hf.comp (Computable.snd.comp Computable.snd))).to₂)
  exact h.of_eq (fun a => (key a.1 a.2).symm)

/-- The back-and-forth strategy: an element n is "f-type" if its backward chain
    under alternating g⁻¹, f⁻¹ terminates outside range(g) (i.e., not a g-image).
    These are exactly the elements where σ(n) := f(n) is the right choice.

    For elements where the chain never terminates (infinite orbits), we also use f. -/
def isGFree (g : ℕ → ℕ) (n : ℕ) : Prop := ∀ k, g k ≠ n

/-- `isGFree g n` is exactly the statement that `n` is **not** in the range of `g`.

    **Why this matters for computability.** The "orbit classification" sketch above
    (Type A/B/C) asks, for each `n`, whether the backward chain terminates outside
    `range g` — i.e. whether some ancestor is `isGFree`. But `isGFree g n` is a
    `Π₁` (universally quantified) predicate: for a merely *computable* injection `g`,
    `range g` is only computably enumerable (`Σ₁`), so its complement `isGFree g`
    is `Π₁` and in general **undecidable**. Hence the orbit type of `n` is *not*
    computable, and the classical Schröder–Bernstein orbit construction does **not**
    yield a computable bijection.

    This is precisely why Myhill's theorem cannot be obtained by "reading off" the
    classical proof, and must instead use the stage-wise finite back-and-forth
    (priority) construction described on `myhill_isomorphism`, where each stage
    performs only a *bounded* search and never has to decide `range g`. -/
theorem isGFree_iff_not_mem_range (g : ℕ → ℕ) (n : ℕ) :
    isGFree g n ↔ n ∉ Set.range g := by
  simp only [isGFree, Set.mem_range, not_exists, ne_eq]

/-!
## Section 4a: The Σ₁ / Π₁ complexity of `range g` — machine-checked

The docstrings above justify the failure of the naive orbit classification by the
*complexity* of `range g`: for a merely computable injection it is only
computably enumerable (`Σ₁`), so its complement `isGFree g` is `Π₁`. Here we turn
that prose into actual theorems. `REPred` (Mathlib, `Computability/Halting`) is the
predicate "is the domain of a computable partial function", i.e. computably
enumerable. Since `partialInverse g` is partial recursive (Section 3) and its domain
is *exactly* `range g`, `Partrec.dom_re` gives `REPred (· ∈ range g)` directly.
-/

/-- The partial inverse `partialInverse g` is defined at `m` **iff** `m ∈ range g`.
    (No injectivity needed: `rfind` halts exactly when a preimage exists.) This
    identifies `range g` with the domain of a partial recursive function. -/
theorem partialInverse_dom_iff_mem_range (g : ℕ → ℕ) (m : ℕ) :
    (partialInverse g m).Dom ↔ m ∈ Set.range g := by
  rw [Set.mem_range]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Part.dom_iff_mem.mp h
    exact ⟨n, by simpa using Nat.rfind_spec hn⟩
  · exact fun hm => partialInverse_dom hm

/-- **`range g` is computably enumerable (`Σ₁`)** for any computable `g`.

    This is the machine-checked form of the "`range g` is c.e." claim used
    throughout to explain why the classical Schröder–Bernstein orbit classification
    is not computable. `REPred p` means `p` is the halting domain of a computable
    partial function; here that function is `partialInverse g`. -/
theorem mem_range_re {g : ℕ → ℕ} (hg : Computable g) :
    REPred (fun n => n ∈ Set.range g) :=
  (partialInverse_partrec hg).dom_re.of_eq (fun n => partialInverse_dom_iff_mem_range g n)

/-- **The complement of `isGFree g` is computably enumerable.** Equivalently,
    `isGFree g` is co-c.e. (`Π₁`): its negation `· ∈ range g` is `REPred`. Combined
    with `isGFree_iff_not_mem_range`, this pins down the exact complexity of the
    obstruction predicate — it is the complement of a c.e. set, hence in general
    not itself computable, which is precisely why the orbit type of `n` cannot be
    decided by bounded search. -/
theorem not_isGFree_re {g : ℕ → ℕ} (hg : Computable g) :
    REPred (fun n => ¬ isGFree g n) :=
  (mem_range_re hg).of_eq fun n => by rw [isGFree_iff_not_mem_range, not_not]

/-!
## Section 4b: Isolating the Π₁ obstruction — the fully computable case

The insight `isGFree_iff_not_mem_range` shows the *only* obstruction to reading a
computable bijection off the classical Schröder–Bernstein construction is that
`isGFree g` (equivalently `· ∉ Set.range g`) is `Π₁`. Here we make that precise
in two ways:

* `decidableIsGFree` — as soon as `Set.range g` is *decidable*, the obstruction
  disappears and `isGFree g` is a decidable predicate.
* `computable_bijection_isComputablePerm` — the fully computable special case:
  a computable **bijection** of ℕ is automatically a computable permutation, i.e.
  its inverse is computable too. (This is Myhill's theorem in the degenerate case
  where the two one-one reductions are already bijections, so no back-and-forth is
  needed.) The inverse is obtained from the partial-recursive `partialInverse`,
  which becomes total because `g` is surjective.
-/

/-- If `Set.range g` is decidable then the `Π₁` obstruction predicate `isGFree g`
    is itself decidable — the range-decidability hypothesis is exactly what the
    general (merely-computable) case lacks. -/
def decidableIsGFree (g : ℕ → ℕ) [DecidablePred (· ∈ Set.range g)] :
    DecidablePred (isGFree g) :=
  fun n => decidable_of_iff _ (isGFree_iff_not_mem_range g n).symm

/-- Under a surjective `g`, the partial inverse (Section 3) is defined everywhere,
    so it yields a genuine total function `ℕ → ℕ`. -/
def totalInverse (g : ℕ → ℕ) (hg : Surjective g) : ℕ → ℕ :=
  fun m => (partialInverse g m).get (partialInverse_dom (hg m))

/-- The total inverse is always a valid `partialInverse` value. -/
theorem totalInverse_mem {g : ℕ → ℕ} (hg : Surjective g) (m : ℕ) :
    totalInverse g hg m ∈ partialInverse g m :=
  Part.get_mem _

/-- `totalInverse` is a right inverse of `g` (needs only surjectivity). -/
theorem totalInverse_right {g : ℕ → ℕ} (hg : Surjective g) (m : ℕ) :
    g (totalInverse g hg m) = m := by
  have h := Nat.rfind_spec (totalInverse_mem hg m)
  simpa using h

/-- `totalInverse` is a left inverse of `g` (needs injectivity too). -/
theorem totalInverse_left {g : ℕ → ℕ} (hg_inj : Injective g) (hg : Surjective g)
    (n : ℕ) : totalInverse g hg (g n) = n :=
  hg_inj (totalInverse_right hg (g n))

/-- When `g` is a computable injection **and** surjective, its total inverse is
    computable: `partialInverse` is partial recursive and here everywhere defined,
    so it coincides with the total function `totalInverse`. -/
theorem totalInverse_computable {g : ℕ → ℕ} (hgc : Computable g) (hg : Surjective g) :
    Computable (totalInverse g hg) :=
  (partialInverse_partrec hgc).of_eq (fun _ => (Part.some_get _).symm)

/-- **Computable easy-case Schröder–Bernstein / Myhill.** A computable *bijection*
    of ℕ is a computable permutation: both it and its inverse are computable. This
    is the special case where the two one-one reductions are already bijections, so
    the back-and-forth priority construction is unnecessary and the `Π₁` `isGFree`
    obstruction never arises. -/
theorem computable_bijection_isComputablePerm {g : ℕ → ℕ}
    (hgc : Computable g) (hg : Bijective g) :
    (Equiv.ofBijective g hg).Computable := by
  refine ⟨hgc, ?_⟩
  have hsymm : ⇑(Equiv.ofBijective g hg).symm = totalInverse g hg.surjective := by
    funext m
    apply hg.injective
    rw [totalInverse_right hg.surjective]
    exact (Equiv.ofBijective g hg).apply_symm_apply m
  rw [hsymm]
  exact totalInverse_computable hgc hg.surjective

/-- Consequently, a computable bijection `g` with `p n ↔ q (g n)` computably
    witnesses `OneOneEquiv p q` — the fully computable instance of Myhill's
    theorem, discharged without the open back-and-forth construction. -/
theorem oneOneEquiv_of_computable_bijection {p q : ℕ → Prop} {g : ℕ → ℕ}
    (hgc : Computable g) (hg : Bijective g) (hpq : ∀ n, p n ↔ q (g n)) :
    OneOneEquiv p q :=
  myhill_easy (Equiv.ofBijective g hg) (computable_bijection_isComputablePerm hgc hg) hpq

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
