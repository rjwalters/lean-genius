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
- IsMatching / MatchingCorr + matching_step_f / matching_step_g: proved — the finite
  partial-bijection layer and the two atomic, correspondence-preserving back-and-forth
  extension steps (domain step through f, range step through g). matching_functional /
  matching_cofunctional: the matching is a partial bijection (both coordinates determine
  the partner). These are the pieces the stage scheduler assembles; only the scheduler
  (collision-chasing via the alternating f/g chain) remains open.
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
## Section 4c: Finite partial bijections ("matchings") — the atomic back-and-forth steps

The stage-wise construction promised on `myhill_isomorphism` maintains a *finite*
partial injection and extends it one element at a time (Rogers §7.4). We formalize
that finite partial injection as an association `List (ℕ × ℕ)` which is injective in
both coordinates — a **matching** — together with the two atomic extension steps the
back-and-forth performs:

* the even-stage **domain step**, routed through `f` (add `(a, f a)`);
* the odd-stage **range step**, routed through `g` (add `(g c, c)`).

Each step is a *bounded*, correspondence-preserving extension and requires only that
the new endpoints are fresh on their respective sides. Crucially the correspondence
`p ↔ q` is preserved *by construction*: the domain step uses `p a ↔ q (f a)` (the `f`
reduction) and the range step uses `p (g c) ↔ q c` (the `g` reduction), so the map is
never tested against the — possibly non-computable — predicates `p`, `q` directly.

This isolates precisely what remains open in `myhill_isomorphism`: only the
*scheduler* that resolves a **collision** (when the naive target `f a` / preimage of
`c` is already used) by chasing the alternating `f`/`g` chain. The atomic steps
below are the pieces that scheduler assembles.
-/

/-- The domain (list of first coordinates) of a finite partial map. -/
def mDom (L : List (ℕ × ℕ)) : List ℕ := L.map Prod.fst

/-- The range (list of second coordinates) of a finite partial map. -/
def mRan (L : List (ℕ × ℕ)) : List ℕ := L.map Prod.snd

@[simp] theorem mDom_cons (a b : ℕ) (L : List (ℕ × ℕ)) :
    mDom ((a, b) :: L) = a :: mDom L := rfl

@[simp] theorem mRan_cons (a b : ℕ) (L : List (ℕ × ℕ)) :
    mRan ((a, b) :: L) = b :: mRan L := rfl

/-- A **matching**: a finite partial injection `ℕ ⇀ ℕ`, injective in *both*
    coordinates. The two `Nodup` conditions say no domain element and no range
    element is recorded twice — i.e. the association list is a partial bijection. -/
def IsMatching (L : List (ℕ × ℕ)) : Prop :=
  (mDom L).Nodup ∧ (mRan L).Nodup

/-- The empty matching. -/
theorem isMatching_nil : IsMatching ([] : List (ℕ × ℕ)) :=
  ⟨List.nodup_nil, List.nodup_nil⟩

/-- **Atomic extension of a matching.** Prepending a pair whose components are each
    fresh on their own side keeps the list a matching. This is the single structural
    fact both back-and-forth steps rely on. -/
theorem isMatching_cons {L : List (ℕ × ℕ)} (hL : IsMatching L)
    {a b : ℕ} (ha : a ∉ mDom L) (hb : b ∉ mRan L) :
    IsMatching ((a, b) :: L) :=
  ⟨by simpa using List.nodup_cons.mpr ⟨ha, hL.1⟩,
   by simpa using List.nodup_cons.mpr ⟨hb, hL.2⟩⟩

/-- A matching is **functional**: its domain determines the partner. If two recorded
    pairs share a first coordinate they are equal. (Uses only domain-side `Nodup`.) -/
theorem matching_functional {L : List (ℕ × ℕ)} (hL : IsMatching L)
    {a b b' : ℕ} (h : (a, b) ∈ L) (h' : (a, b') ∈ L) : b = b' := by
  have := List.inj_on_of_nodup_map hL.1 h h' rfl
  simpa using congrArg Prod.snd this

/-- A matching is **co-functional**: its range determines the partner. If two recorded
    pairs share a second coordinate they are equal. (Uses only range-side `Nodup`.) -/
theorem matching_cofunctional {L : List (ℕ × ℕ)} (hL : IsMatching L)
    {a a' b : ℕ} (h : (a, b) ∈ L) (h' : (a', b) ∈ L) : a = a' := by
  have := List.inj_on_of_nodup_map hL.2 h h' rfl
  simpa using congrArg Prod.fst this

/-- A matching **respects** the correspondence `p ↔ q` if every recorded pair does. -/
def MatchingCorr (p q : ℕ → Prop) (L : List (ℕ × ℕ)) : Prop :=
  ∀ ab ∈ L, p ab.1 ↔ q ab.2

/-- The empty matching vacuously respects any correspondence. -/
theorem matchingCorr_nil (p q : ℕ → Prop) : MatchingCorr p q [] := by
  intro _ h; simp at h

/-- Correspondence is preserved when the newly added pair itself corresponds. -/
theorem matchingCorr_cons {p q : ℕ → Prop} {L : List (ℕ × ℕ)}
    (hC : MatchingCorr p q L) {a b : ℕ} (hab : p a ↔ q b) :
    MatchingCorr p q ((a, b) :: L) := by
  intro ab hmem
  rcases List.mem_cons.mp hmem with h | h
  · subst h; exact hab
  · exact hC ab h

/-- **Domain step (through `f`).** If `a` is fresh in the domain and its `f`-image is
    fresh in the range, extending the matching by `(a, f a)` keeps it a matching and
    preserves the `p ↔ q` correspondence — because the `f` reduction gives
    `p a ↔ q (f a)`. This is the even-stage move: it guarantees `a ∈ dom`. -/
theorem matching_step_f {p q : ℕ → Prop} {f : ℕ → ℕ} (hfpq : ∀ n, p n ↔ q (f n))
    {L : List (ℕ × ℕ)} (hL : IsMatching L) (hC : MatchingCorr p q L)
    {a : ℕ} (ha : a ∉ mDom L) (hfa : f a ∉ mRan L) :
    IsMatching ((a, f a) :: L) ∧ MatchingCorr p q ((a, f a) :: L) :=
  ⟨isMatching_cons hL ha hfa, matchingCorr_cons hC (hfpq a)⟩

/-- **Range step (through `g`).** If `c` is fresh in the range and its `g`-image is
    fresh in the domain, extending the matching by `(g c, c)` keeps it a matching and
    preserves the correspondence — because the `g` reduction gives `q c ↔ p (g c)`.
    This is the odd-stage move: it guarantees `c ∈ ran`. -/
theorem matching_step_g {p q : ℕ → Prop} {g : ℕ → ℕ} (hgpq : ∀ n, q n ↔ p (g n))
    {L : List (ℕ × ℕ)} (hL : IsMatching L) (hC : MatchingCorr p q L)
    {c : ℕ} (hc : c ∉ mRan L) (hgc : g c ∉ mDom L) :
    IsMatching ((g c, c) :: L) ∧ MatchingCorr p q ((g c, c) :: L) :=
  ⟨isMatching_cons hL hgc hc, matchingCorr_cons hC (hgpq c).symm⟩

/-- Each atomic step **strictly enlarges** the matching: the recorded length grows by
    one, which is the well-founded measure the scheduler decreases towards full
    domain/range coverage (`k` enters by stage `2k + 1`). -/
theorem matching_length_cons (a b : ℕ) (L : List (ℕ × ℕ)) :
    ((a, b) :: L).length = L.length + 1 := by simp

/-!
## Section 4d: Least fresh element — the computable exhaustion primitive

The atomic steps of Section 4c (`matching_step_f`, `matching_step_g`) each extend a
finite matching by one edge, provided the new endpoint is *fresh* (not already in
`mDom L` / `mRan L`). To turn these steps into a construction that covers **all** of
ℕ, the priority scheduler must, at each stage, target the *least* natural number not
yet present on the relevant side (`mDom` at even stages, `mRan` at odd stages).
Because it always attacks the least uncovered element, every `k` is guaranteed to be
handled by stage `2k + 1` — this is exactly the domain/range-exhaustion argument the
scheduler needs (cf. `matching_length_cons`).

This section provides that targeting function as a total, computable
`firstMissing : List ℕ → ℕ` returning the least natural not occurring in a finite
list, together with the two properties the exhaustion proof consumes: `firstMissing`
is genuinely absent (`firstMissing_not_mem`), and it is *minimal* — every smaller
number is already present (`firstMissing_lt_mem`), so `List.range (firstMissing L) ⊆
L` and repeated extension strictly grows the covered prefix. Its computability
(`firstMissing_computable`) is what keeps the permutation built on top of it
computable; the proof mirrors the `partialInverse`/`totalInverse` pattern of
Sections 3–4b (`Nat.rfind` search + everywhere-defined ⟹ total computable).
-/

/-- Partial version: search (via `Nat.rfind`) for the least `n` absent from `L`.
    Absence `n ∉ L` is phrased decidably as `List.idxOf n L = L.length` (a list's
    `idxOf` equals its length exactly when the element is missing). -/
def firstMissingPart (L : List ℕ) : Part ℕ :=
  Nat.rfind fun n => decide (List.idxOf n L = L.length)

/-- A finite list of naturals always omits some natural number (ℕ is infinite). -/
theorem exists_not_mem_list (L : List ℕ) : ∃ n : ℕ, n ∉ L := by
  obtain ⟨n, hn⟩ := Infinite.exists_notMem_finset L.toFinset
  exact ⟨n, fun h => hn (List.mem_toFinset.mpr h)⟩

/-- The search terminates: a missing element exists, so `firstMissingPart` is
    everywhere defined. -/
theorem firstMissingPart_dom (L : List ℕ) : (firstMissingPart L).Dom := by
  obtain ⟨n, hn⟩ := exists_not_mem_list L
  rw [firstMissingPart, Nat.rfind_dom']
  exact ⟨n, by simp [hn], fun _ => trivial⟩

/-- **Least fresh element**: the least natural number not occurring in `L`. -/
def firstMissing (L : List ℕ) : ℕ := (firstMissingPart L).get (firstMissingPart_dom L)

/-- `firstMissing L` is a valid value of the underlying `rfind` search. -/
theorem firstMissing_mem_part (L : List ℕ) : firstMissing L ∈ firstMissingPart L :=
  Part.get_mem _

/-- **Freshness**: `firstMissing L` is genuinely absent from `L`. This is what makes
    it a legal endpoint for `matching_step_f` / `matching_step_g` (with `L := mDom …`
    or `mRan …`). -/
theorem firstMissing_not_mem (L : List ℕ) : firstMissing L ∉ L := by
  have h := Nat.rfind_spec (firstMissing_mem_part L)
  have h2 : List.idxOf (firstMissing L) L = L.length := by simpa using h
  exact List.idxOf_eq_length_iff.mp h2

/-- **Minimality**: every natural number below `firstMissing L` already occurs in
    `L`. Equivalently `List.range (firstMissing L) ⊆ L`. Together with
    `firstMissing_not_mem` this pins down `firstMissing L` as the least element of the
    complement of `L`, so repeatedly extending by it exhausts an ever-larger initial
    segment of ℕ — the termination measure of the priority construction. -/
theorem firstMissing_lt_mem (L : List ℕ) {m : ℕ} (hm : m < firstMissing L) : m ∈ L := by
  have h := Nat.rfind_min (firstMissing_mem_part L) hm
  have h2 : ¬ (List.idxOf m L = L.length) := by simpa using h
  by_contra hmem
  exact h2 (List.idxOf_eq_length_iff.mpr hmem)

/-- **`firstMissing` is computable.** List membership `n ∈ L` is primitive recursive
    (through `List.idxOf` and `List.length`), so the bounded `rfind` search is partial
    recursive; being everywhere defined (`firstMissingPart_dom`) it coincides with the
    total function `firstMissing`. This is the computability guarantee that lets the
    back-and-forth permutation assembled from these fresh-element choices remain
    computable. -/
theorem firstMissing_computable : Computable firstMissing := by
  have hp : Partrec firstMissingPart := by
    unfold firstMissingPart
    apply Partrec.rfind
    apply Computable₂.partrec₂
    have hidx : Computable (fun p : List ℕ × ℕ => List.idxOf p.2 p.1) :=
      Primrec.list_idxOf.to_comp.comp Computable.snd Computable.fst
    have hlen : Computable (fun p : List ℕ × ℕ => p.1.length) :=
      Primrec.list_length.to_comp.comp Computable.fst
    have heq0 : Primrec₂ (fun a b : ℕ => decide (a = b)) := Primrec.eq.decide
    have heq : Computable₂ (fun a b : ℕ => decide (a = b)) := heq0.to_comp
    exact heq.comp hidx hlen
  exact hp.of_eq (fun L => (Part.some_get (firstMissingPart_dom L)).symm)

/-- The `firstMissing`-covered prefix lies inside `L`: every natural below
    `firstMissing L` already occurs. This packages `firstMissing_lt_mem` as an initial
    segment (`Finset.range`) coverage statement, the form the exhaustion argument uses.
    (The `List.range` variant with the canonical name `range_firstMissing_subset` is
    below in Section 4d; this `Finset`-flavoured restatement keeps the distinct name
    `range_firstMissing_subset_finset` to avoid the collision the two independent
    sessions introduced.) -/
theorem range_firstMissing_subset_finset (L : List ℕ) {m : ℕ}
    (hm : m ∈ Finset.range (firstMissing L)) : m ∈ L :=
  firstMissing_lt_mem L (Finset.mem_range.mp hm)

/-- **Exhaustion bound**: `firstMissing L ≤ L.length`. Since `{0, …, firstMissing L − 1}`
    are all present (`firstMissing_lt_mem`), they are `firstMissing L` distinct members of
    `L`, so `firstMissing L ≤ #(L.toFinset) ≤ L.length`. Hence a matching of length `n`
    leaves the least fresh endpoint `≤ n`: repeatedly extending by `firstMissing` covers
    every initial segment of ℕ. This is the quantitative termination measure the priority
    scheduler decreases (cf. `matching_length_cons`) — every `k` enters by a bounded stage. -/
theorem firstMissing_le_length (L : List ℕ) : firstMissing L ≤ L.length := by
  have hsub : Finset.range (firstMissing L) ⊆ L.toFinset := fun m hm =>
    List.mem_toFinset.mpr (firstMissing_lt_mem L (Finset.mem_range.mp hm))
  calc firstMissing L = (Finset.range (firstMissing L)).card := (Finset.card_range _).symm
    _ ≤ L.toFinset.card := Finset.card_le_card hsub
    _ ≤ L.length := List.toFinset_card_le L

/-!
## Section 4e: Domain/range duality via coordinate swap

The back-and-forth construction has two structurally identical halves: the even stage
guarantees domain coverage (through `f`), the odd stage guarantees range coverage
(through `g`). These are formally dual — the odd stage on `(p, q, g)` is the even stage
on the *swapped* problem `(q, p, g)`. Coordinate-swapping a matching `L ↦ L.map Prod.swap`
exchanges its domain and range while preserving the matching and correspondence
structure (with `p, q` swapped). This lets the eventual scheduler define and verify only
one stage move and obtain the other by duality.
-/

/-- Swapping coordinates exchanges the domain and range lists. -/
@[simp] theorem mDom_map_swap (L : List (ℕ × ℕ)) : mDom (L.map Prod.swap) = mRan L := by
  simp [mDom, mRan, List.map_map, Function.comp]

@[simp] theorem mRan_map_swap (L : List (ℕ × ℕ)) : mRan (L.map Prod.swap) = mDom L := by
  simp [mDom, mRan, List.map_map, Function.comp]

/-- A coordinate-swapped matching is again a matching (the two `Nodup` sides trade). -/
theorem isMatching_map_swap {L : List (ℕ × ℕ)} (hL : IsMatching L) :
    IsMatching (L.map Prod.swap) :=
  ⟨by rw [mDom_map_swap]; exact hL.2, by rw [mRan_map_swap]; exact hL.1⟩

/-- Coordinate-swapping a matching that respects `p ↔ q` yields one respecting `q ↔ p`.
    This is the precise sense in which the odd (range) stage is the even (domain) stage of
    the swapped problem. -/
theorem matchingCorr_map_swap {p q : ℕ → Prop} {L : List (ℕ × ℕ)}
    (hC : MatchingCorr p q L) : MatchingCorr q p (L.map Prod.swap) := by
  intro ab hmem
  rw [List.mem_map] at hmem
  obtain ⟨cd, hcd, rfl⟩ := hmem
  exact (hC cd hcd).symm

/-!
## Section 4e: Monotone exhaustion — the least-fresh targeting makes progress

Section 4d produced `firstMissing L`, the least natural absent from `L`, with its two
defining properties (`firstMissing_not_mem`, `firstMissing_lt_mem`). The priority
scheduler of `myhill_isomorphism` uses it as the *target* at each stage, and needs one
more quantitative fact to guarantee **domain/range exhaustion**: that repeatedly
prepending the least-fresh element strictly enlarges the covered initial segment of ℕ,
so every `k` is reached in finitely many stages.

We package that here. First we restate minimality as a genuine initial-segment cover
(`range_firstMissing_subset`: `[0, firstMissing L) ⊆ L`) and prove its converse
characterization (`le_firstMissing_of_range_subset`: covering `[0, n)` forces
`n ≤ firstMissing L`). Together these say `firstMissing L` is *exactly* the length of
the exhausted prefix. The payoff is `firstMissing_lt_cons_self`: prepending the
least-fresh element strictly increases `firstMissing`, i.e. the exhausted prefix grows
by at least one at every stage. This is the strictly-increasing, ℕ-valued progress
measure the back-and-forth construction decreases against (dual to
`matching_length_cons`), pinning down *why* the naive least-fresh targeting terminates
its coverage obligation for each `k` — independently of how collisions are resolved.
-/

/-- **Covered prefix.** Minimality of `firstMissing` (Section 4d), restated as an
    initial-segment cover: every natural below `firstMissing L` occurs in `L`, i.e.
    `[0, firstMissing L) ⊆ L`. -/
theorem range_firstMissing_subset (L : List ℕ) :
    List.range (firstMissing L) ⊆ L := by
  intro m hm
  exact firstMissing_lt_mem L (List.mem_range.mp hm)

/-- **Characterization of `firstMissing` as the exhausted-prefix length.** If `L`
    already covers the whole initial segment `[0, n)`, then `firstMissing L ≥ n`
    (the least gap cannot occur before `n`). Combined with `range_firstMissing_subset`
    this shows `firstMissing L` is precisely the length of the largest gap-free prefix
    `[0, firstMissing L)` of ℕ recorded in `L`. -/
theorem le_firstMissing_of_range_subset {n : ℕ} {L : List ℕ}
    (h : List.range n ⊆ L) : n ≤ firstMissing L := by
  by_contra hlt
  push_neg at hlt
  exact firstMissing_not_mem L (h (List.mem_range.mpr hlt))

/-- Prepending the least-fresh element extends the covered prefix by one: `[0,
    firstMissing L]` is covered by `firstMissing L :: L`. This is the single step the
    progress measure rests on. -/
theorem range_succ_firstMissing_subset_cons_self (L : List ℕ) :
    List.range (firstMissing L + 1) ⊆ firstMissing L :: L := by
  intro m hm
  rcases (Nat.lt_succ_iff.mp (List.mem_range.mp hm)).lt_or_eq with h | h
  · exact List.mem_cons_of_mem _ (firstMissing_lt_mem L h)
  · exact h ▸ List.mem_cons_self

/-- **Strict progress of least-fresh targeting.** Prepending the least missing element
    of `L` strictly increases `firstMissing`. Hence iterating the least-fresh choice
    drives `firstMissing` (the exhausted-prefix length) to infinity: every `k` is
    covered after finitely many stages. This strictly-monotone ℕ-valued measure is the
    exhaustion guarantee the scheduler in `myhill_isomorphism` needs, complementing the
    length measure `matching_length_cons` of the atomic steps. -/
theorem firstMissing_lt_cons_self (L : List ℕ) :
    firstMissing L < firstMissing (firstMissing L :: L) := by
  have h : firstMissing L + 1 ≤ firstMissing (firstMissing L :: L) :=
    le_firstMissing_of_range_subset (range_succ_firstMissing_subset_cons_self L)
  omega

/-!
## Section 4f: Reading the permutation off a matching — the computable evaluator

The scheduler assembles a chain of finite matchings `L₀ ⊆ L₁ ⊆ …`; the permutation
`σ` is then read off by *looking up* the partner of `n` in the matching at the stage
`n` enters the domain (obligation (d) of `myhill_isomorphism`). This section supplies
that evaluator as a **total, computable** function of the matching and the argument,
together with its correctness: on a matching it recovers the recorded partner exactly.

`mLookup L n` reads the entry of `mRan L` at the position of `n` in `mDom L`
(`List.idxOf`). Because `mDom L` and `mRan L` are the two coordinate projections of the
same list, they are index-aligned, so this returns the second coordinate of the pair
whose first coordinate is `n`. Off the domain (`n ∉ mDom L`) the index is out of range
and the placeholder `0` is returned — harmless, since the read-off only queries
`n ∈ mDom`. The two `Nodup` conditions of `IsMatching` are exactly what make the lookup
single-valued (`matching_functional`), so `mLookup` is the computable realization of the
finite partial bijection a matching represents.
-/

/-- **Partner lookup in a matching.** The value the finite partial map `L` associates to
    `n`: the entry of the range list `mRan L` at the index of `n` in the domain list
    `mDom L`. A total function; off the domain it returns the placeholder `0`. -/
def mLookup (L : List (ℕ × ℕ)) (n : ℕ) : ℕ :=
  (mRan L).getD (List.idxOf n (mDom L)) 0

/-- **Correctness of `mLookup`.** On a matching, the lookup recovers the recorded
    partner: if `(n, b) ∈ L` then `mLookup L n = b`. The domain-side `Nodup` (via
    `IsMatching`) guarantees `n` occurs once in `mDom L`, so its index selects exactly
    the aligned range entry `b`. This makes `mLookup` the evaluation of the finite
    partial bijection a matching encodes — the read-off used to define `σ`. -/
theorem mLookup_eq_of_mem :
    ∀ {L : List (ℕ × ℕ)}, IsMatching L → ∀ {n b : ℕ}, (n, b) ∈ L → mLookup L n = b := by
  intro L
  induction L with
  | nil => intro _ n b h; simp at h
  | cons hd tl ih =>
    obtain ⟨a, c⟩ := hd
    intro hL n b h
    have hnodupD : (a :: mDom tl).Nodup := by simpa using hL.1
    have hnodupR : (c :: mRan tl).Nodup := by simpa using hL.2
    have ha_notin : a ∉ mDom tl := (List.nodup_cons.mp hnodupD).1
    have hMtl : IsMatching tl :=
      ⟨(List.nodup_cons.mp hnodupD).2, (List.nodup_cons.mp hnodupR).2⟩
    rw [List.mem_cons] at h
    rcases h with h | h
    · -- the pair is the head: `(n, b) = (a, c)`
      have hn : n = a := congrArg Prod.fst h
      have hb : b = c := congrArg Prod.snd h
      subst hn; subst hb
      simp only [mLookup, mDom_cons, mRan_cons, List.idxOf_cons_self, List.getD_cons_zero]
    · -- the pair is in the tail: recurse, the head index is skipped
      have hn_mem : n ∈ mDom tl := by
        simp only [mDom, List.mem_map]; exact ⟨(n, b), h, rfl⟩
      have hne : a ≠ n := fun heq => ha_notin (heq ▸ hn_mem)
      simp only [mLookup, mDom_cons, mRan_cons, List.idxOf_cons_ne _ hne,
        List.getD_cons_succ]
      exact ih hMtl h

/-- **`mLookup` is computable** (indeed primitive recursive) in both the matching and the
    argument. The domain/range projections `mDom`, `mRan` are list maps of the coordinate
    projections; `List.idxOf` and `List.getD` are primitive recursive (`Primrec.list_idxOf`,
    `Primrec.list_getD`). Combined with `mLookup_eq_of_mem`, this is the computability
    guarantee behind reading a *computable* permutation off the stage-wise matchings:
    once the (computable) sequence of matchings is built, `σ n` is a computable lookup. -/
theorem mLookup_computable : Computable₂ mLookup := by
  have hmDom : Computable (fun L : List (ℕ × ℕ) => mDom L) := by
    have h : Primrec (fun L : List (ℕ × ℕ) => L.map Prod.fst) :=
      Primrec.list_map Primrec.id (Primrec.fst.comp Primrec.snd)
    exact h.to_comp
  have hmRan : Computable (fun L : List (ℕ × ℕ) => mRan L) := by
    have h : Primrec (fun L : List (ℕ × ℕ) => L.map Prod.snd) :=
      Primrec.list_map Primrec.id (Primrec.snd.comp Primrec.snd)
    exact h.to_comp
  have hIdx : Computable (fun p : List (ℕ × ℕ) × ℕ => List.idxOf p.2 (mDom p.1)) :=
    Primrec.list_idxOf.to_comp.comp Computable.snd (hmDom.comp Computable.fst)
  have hRanP : Computable (fun p : List (ℕ × ℕ) × ℕ => mRan p.1) :=
    hmRan.comp Computable.fst
  have hget : Computable (fun p : List (ℕ × ℕ) × ℕ =>
      (mRan p.1).getD (List.idxOf p.2 (mDom p.1)) 0) :=
    (Primrec.list_getD (0 : ℕ)).to_comp.comp hRanP hIdx
  exact hget.of_eq (fun _ => rfl)

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
