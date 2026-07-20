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
  the partner). These are the pieces the stage scheduler assembles.
- myhill_isomorphism: COMPLETE (0-sorry / 0-axiom). Both directions proved; the hard direction
  uses the computable extension-only scheduler `sigmaC` (Section 5·C), whose read-off is
  `Computable` (`sigmaC_computable`), so the resulting permutation is a genuine computable
  bijection. `#print axioms` → `[propext, Classical.choice, Quot.sound]` only.

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
## Section 4·chase: The collision chase is a *bounded* forward-orbit walk

The stage-wise scheduler behind `myhill_isomorphism` places a fresh domain point `a` by
trying its image `f a`. When `f a` is already used (a **collision**), the blocking pair is
the `g`-edge `(g (f a), f a)` (see the `collision_f_source` analysis), so the obstruction
is the *already-placed* element `g (f a)` — and by the recurrence `fwdOrbit f g a (k+1) =
g (f (fwdOrbit f g a k))` this is exactly the next forward-orbit point `fwdOrbit f g a 1`.
Hence "chasing the collision" means walking the forward orbit `a, g(f a), g(f(g(f a))),
…`, which is computable (`fwdOrbit_computable`) and never decides the `Π₁` predicate
`isGFree`.

The one thing the scheduler still needs from this walk is that it **terminates**: the
search for a fresh target is *bounded*, so it is a genuine computable step (not an
unbounded μ-search). That is what this section supplies, with no reference to `isGFree`:

* `fwdOrbit_succ` — the chase-step recurrence, making `g (f x)` the successor target.
* `fwdOrbit_prefix_distinct` — **acyclicity of a fresh-anchored colliding prefix.** If the
  orbit is anchored at a point `a ∉ D` and every later point up to stage `N` lies in the
  occupied set `D`, then the points `fwdOrbit f g a 0, …, N` are pairwise distinct. (If two
  coincided, injectivity of `g ∘ f` would make `a` itself periodic, i.e. `a = fwdOrbit f g
  a d ∈ D` for some `1 ≤ d`, contradicting freshness.)
* `fwdOrbit_chase_length_le` — the resulting **length bound**: a colliding prefix whose
  interior stays inside a finite list `D` has length `≤ D.length`. Instantiated with `D :=
  mDom L` (the current matching's domain), this bounds the collision chase by the size of
  the partial bijection built so far, discharging the "bounded search" obligation.
-/

/-- **Chase-step recurrence.** From orbit point `x = fwdOrbit f g a k`, the next point is
    the collision blocker `g (f x)`: `fwdOrbit f g a (k+1) = g (f (fwdOrbit f g a k))`. In
    particular the element obstructing a fresh domain point `a` (namely `g (f a)`) is the
    first orbit step `fwdOrbit f g a 1`. This is the definitional unfolding of `fwdOrbit`,
    isolated here because it is the exact link between the collision analysis and the
    forward orbit. -/
theorem fwdOrbit_succ (f g : ℕ → ℕ) (n k : ℕ) :
    fwdOrbit f g n (k + 1) = g (f (fwdOrbit f g n k)) := rfl

/-- **Acyclicity of a fresh-anchored colliding orbit prefix.** Let `g ∘ f` be injective
    (guaranteed by `f`, `g` injective). Suppose the forward orbit of `a` has its anchor
    *outside* the occupied set (`¬ D a`) while every later point up to stage `N` is
    *inside* it (`D (fwdOrbit f g a k)` for `1 ≤ k ≤ N`) — exactly the situation of a
    collision chase that keeps hitting already-placed points. Then the prefix
    `fwdOrbit f g a 0, …, fwdOrbit f g a N` is **injective** (no repeats).

    *Why.* A repeat `fwdOrbit a i = fwdOrbit a j` with `i < j` would, via injectivity of
    `(g ∘ f)^[i]`, force `a = fwdOrbit a (j - i)` with `1 ≤ j - i ≤ N`; but that point lies
    in `D`, so `a ∈ D`, contradicting freshness. Thus the orbit cannot re-enter its anchor,
    and a colliding chase visits only fresh orbit points — which is what makes it bounded. -/
theorem fwdOrbit_prefix_distinct {f g : ℕ → ℕ}
    (hf : Function.Injective f) (hg : Function.Injective g)
    {a : ℕ} {D : ℕ → Prop} (h0 : ¬ D a) {N : ℕ}
    (hchase : ∀ k, 1 ≤ k → k ≤ N → D (fwdOrbit f g a k)) :
    ∀ ⦃i⦄, i ≤ N → ∀ ⦃j⦄, j ≤ N → fwdOrbit f g a i = fwdOrbit f g a j → i = j := by
  have hT : Function.Injective (fun x => g (f x)) := fun x y h => hf (hg h)
  have hiter : ∀ k, fwdOrbit f g a k = (fun x => g (f x))^[k] a :=
    fun k => fwdOrbit_eq_iterate f g a k
  intro i hi j hj hij
  rcases le_total i j with hle | hle
  · obtain ⟨d, rfl⟩ := Nat.le.dest hle
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd; simp
    · exfalso
      rw [hiter i, hiter (i + d), Function.iterate_add_apply] at hij
      have hax : a = (fun x => g (f x))^[d] a := (hT.iterate i) hij
      have hdN : d ≤ N := le_trans (Nat.le_add_left d i) hj
      have hDa : D (fwdOrbit f g a d) := hchase d hd hdN
      rw [hiter d, ← hax] at hDa
      exact h0 hDa
  · obtain ⟨d, rfl⟩ := Nat.le.dest hle
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd; simp
    · exfalso
      rw [hiter (j + d), hiter j, Function.iterate_add_apply] at hij
      have hax : (fun x => g (f x))^[d] a = a := (hT.iterate j) hij
      have hdN : d ≤ N := le_trans (Nat.le_add_left d j) hi
      have hDa : D (fwdOrbit f g a d) := hchase d hd hdN
      rw [hiter d, hax] at hDa
      exact h0 hDa

/-- **The collision chase is bounded by the occupied domain.** If the fresh anchor `a`
    lies outside the finite occupied list `D`, and every chase point `fwdOrbit f g a k`
    for `1 ≤ k ≤ N` lies inside `D`, then `N ≤ D.length`. In the scheduler, taking
    `D := mDom L` (the domain of the current finite matching `L`) bounds the number of
    collision-chase steps by `L.length`, so the search for a fresh `f`-target is a genuine
    *bounded* (hence computable) step — the last piece the "each stage terminates" clause
    of `myhill_isomorphism` rests on. -/
theorem fwdOrbit_chase_length_le {f g : ℕ → ℕ}
    (hf : Function.Injective f) (hg : Function.Injective g)
    {a : ℕ} {D : List ℕ} (h0 : a ∉ D) {N : ℕ}
    (hchase : ∀ k, 1 ≤ k → k ≤ N → fwdOrbit f g a k ∈ D) :
    N ≤ D.length := by
  have hdist := fwdOrbit_prefix_distinct hf hg (D := fun n => n ∈ D) h0 hchase
  have hInj : Set.InjOn (fwdOrbit f g a) ↑(Finset.Icc 1 N) := by
    intro i hi j hj hij
    simp only [Finset.coe_Icc, Set.mem_Icc] at hi hj
    exact hdist hi.2 hj.2 hij
  have hmaps : ∀ k ∈ Finset.Icc 1 N, fwdOrbit f g a k ∈ D.toFinset := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    exact List.mem_toFinset.mpr (hchase k hk.1 hk.2)
  have hcard : (Finset.Icc 1 N).card ≤ D.toFinset.card :=
    Finset.card_le_card_of_injOn (fwdOrbit f g a) hmaps hInj
  have hIcc : (Finset.Icc 1 N).card = N := by rw [Nat.card_Icc]; omega
  rw [hIcc] at hcard
  exact le_trans hcard (List.toFinset_card_le D)

/-- **The collision chase preserves the source predicate.** Each chase step sends `x` to
    `g (f x)`, and the reductions give `p (g (f x)) ↔ q (f x) ↔ p x`; so the `p`-value is
    invariant along the whole forward orbit: `p (fwdOrbit f g a k) ↔ p a` for every `k`.

    This is the correspondence half of the collision step. When a fresh domain point `a`
    cannot take its own image `f a` (already used) and the scheduler routes it instead to
    the image `f (fwdOrbit f g a N)` of a later, *escaping* orbit point (`chase_target_corr`
    below), the resulting edge still respects the membership condition — precisely because
    walking the orbit never changes the `p`-value. Note this holds for *arbitrary* (not
    necessarily computable) predicates `p, q`: the invariance is routed structurally through
    the reductions `f, g`, never by testing `p`/`q`. -/
theorem fwdOrbit_corr {p q : ℕ → Prop} {f g : ℕ → ℕ}
    (hfpq : ∀ n, p n ↔ q (f n)) (hgpq : ∀ n, q n ↔ p (g n)) (a : ℕ) :
    ∀ k, p (fwdOrbit f g a k) ↔ p a := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [fwdOrbit_succ]
      -- `p (g (f xₖ)) ↔ q (f xₖ) ↔ p xₖ ↔ p a`
      rw [← hgpq (f (fwdOrbit f g a k)), ← hfpq (fwdOrbit f g a k)]
      exact ih

/-- **Correspondence for the routed collision target.** Combining `fwdOrbit_corr` with the
    `f`-reduction: the membership condition `p a ↔ q (f (fwdOrbit f g a N))` holds for every
    orbit stage `N`. So routing the fresh domain point `a` to the range value
    `f (fwdOrbit f g a N)` — the escape target the chase produces once `f` of an orbit point
    lands outside the occupied range — records a pair `(a, f (fwdOrbit f g a N))` that
    satisfies `MatchingCorr`. Together with `fwdOrbit_chase_length_le` (the chase is bounded,
    hence computable) this discharges both obligations of the even-stage collision move:
    *bounded termination* and *correspondence preservation*. -/
theorem chase_target_corr {p q : ℕ → Prop} {f g : ℕ → ℕ}
    (hfpq : ∀ n, p n ↔ q (f n)) (hgpq : ∀ n, q n ↔ p (g n)) (a N : ℕ) :
    p a ↔ q (f (fwdOrbit f g a N)) :=
  (fwdOrbit_corr hfpq hgpq a N).symm.trans (hfpq (fwdOrbit f g a N))

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
## Section 4f-bis: Read-off coherence — the limit function is well-defined and injective

`mLookup_eq_of_mem` reads the recorded partner off a matching. To assemble the
stage-wise matchings into a single permutation `σ : ℕ ≃ ℕ` the assembly step needs three
further facts about that read-off, all consequences of the matching `Nodup` conditions:

* the read-off **lands on a genuine edge** (`mLookup_mem_of_mem_dom`): whenever `n` is in
  the domain, `(n, mLookup L n) ∈ L`. This is the converse companion to
  `mLookup_eq_of_mem` and is what lets the range/inverse be read back off the same list.
* the read-off is **injective across the domain** (`mLookup_injOn`): distinct domain
  points get distinct partners, from range-side `Nodup` (`matching_cofunctional`). This is
  the finite-stage witness of injectivity of the limit `σ`.
* the read-off is **stable along a growing chain** (`mLookup_stable`): enlarging the
  matching does not change the value on the already-covered domain. This is exactly the
  coherence that makes the stage-wise read-offs converge to a single well-defined limit
  (`σ n` may be computed at *any* stage past the one where `n` enters the domain).

These are the well-definedness, injectivity, and coherence obligations the assembly of
`myhill_isomorphism` consumes; they are collision-independent, so they hold for every
matching regardless of how the scheduler resolves collisions (Section 4g).
-/

/-- **The read-off lands on a recorded edge.** If `n` is in the domain of a matching,
    then `(n, mLookup L n) ∈ L`: the looked-up partner is genuinely paired with `n`.
    Converse companion to `mLookup_eq_of_mem`. -/
theorem mLookup_mem_of_mem_dom {L : List (ℕ × ℕ)} (hL : IsMatching L)
    {n : ℕ} (hn : n ∈ mDom L) : (n, mLookup L n) ∈ L := by
  simp only [mDom, List.mem_map] at hn
  obtain ⟨⟨a, b⟩, hmem, ha⟩ := hn
  have ha' : a = n := ha
  subst ha'
  rw [mLookup_eq_of_mem hL hmem]
  exact hmem

/-- **The read-off is injective across the domain.** On a matching, distinct domain
    points have distinct partners: if `m, n ∈ dom L` and `mLookup L m = mLookup L n`
    then `m = n`. Follows from range-side `Nodup` via `matching_cofunctional`; this is the
    finite-stage witness of injectivity of the limit permutation. -/
theorem mLookup_injOn {L : List (ℕ × ℕ)} (hL : IsMatching L)
    {m n : ℕ} (hm : m ∈ mDom L) (hn : n ∈ mDom L)
    (h : mLookup L m = mLookup L n) : m = n := by
  have hm' := mLookup_mem_of_mem_dom hL hm
  have hn' := mLookup_mem_of_mem_dom hL hn
  rw [h] at hm'
  exact matching_cofunctional hL hm' hn'

/-- **Read-off coherence along a growing chain.** If every pair of the matching `L₁` is
    also a pair of the larger matching `L₂`, the two agree on `L₁`'s domain:
    `mLookup L₁ n = mLookup L₂ n` for `n ∈ dom L₁`. This is what makes the stage-wise
    read-offs converge to a single well-defined limit — `σ n` may be computed at any stage
    at or beyond the one where `n` first enters the domain. -/
theorem mLookup_stable {L₁ L₂ : List (ℕ × ℕ)} (h₁ : IsMatching L₁) (h₂ : IsMatching L₂)
    (hsub : ∀ x ∈ L₁, x ∈ L₂) {n : ℕ} (hn : n ∈ mDom L₁) :
    mLookup L₁ n = mLookup L₂ n := by
  have hmem := mLookup_mem_of_mem_dom h₁ hn
  exact (mLookup_eq_of_mem h₂ (hsub _ hmem)).symm

/-!
## Section 4g: Collision structure — what blocks a fresh domain/range extension

Sections 4c–4f supply the *collision-free* atomic steps (`matching_step_f`,
`matching_step_g`), the least-fresh target (`firstMissing`), the strictly-increasing
progress measure, and the computable read-off (`mLookup`). The single obligation they
leave open — the crux of `myhill_isomorphism`, where the classical orbit classification
fails because `isGFree` is Π₁ (Section 4a) — is what to do when an atomic step's
*freshness* hypothesis fails: the target `f a` is already used in the range (a
**collision**), so `matching_step_f` does not apply.

This section pins down the exact structure of such a collision. The handle is a
construction invariant satisfied by every matching the scheduler builds: each recorded
pair is either an `f`-edge `(x, f x)` (a domain step) or a `g`-edge `(g y, y)` (a range
step). Call this `BuiltFrom f g L`. It is preserved by both atomic steps
(`builtFrom_cons_f`, `builtFrom_cons_g`) and is self-dual under coordinate swap with
`f`, `g` exchanged (`builtFrom_map_swap`), so it holds throughout the back-and-forth.

Under this invariant a domain-side collision has a **unique, explicitly identified
source**: if the fresh point `a`'s image `f a` is already in the range, the blocking
pair *must* be the `g`-edge `(g (f a), f a)` — it cannot be an `f`-edge, since `f x = f
a` would force `x = a`, putting `a` back in the domain (`collision_f_source`). Dually, a
range-side collision when placing `c` is blocked precisely by the `f`-edge
`(g c, f (g c))` (`collision_g_source`). Contrapositively, whenever the identified
blocking edge is *absent* the naive atomic step is available
(`step_f_available_or_collision`). This is exactly the determinacy the collision-chasing
recursion needs: it turns an opaque "the target is taken" into a named already-placed
element (`g (f a)`), i.e. the next orbit point to chase — reducing the residual work in
`myhill_isomorphism` to bounding that chase, with no appeal to the non-computable
`isGFree`.
-/

/-- **Construction invariant.** Every pair in the matching is either an `f`-edge
    `(x, f x)` (a domain step, `matching_step_f`) or a `g`-edge `(g y, y)` (a range step,
    `matching_step_g`). The scheduler only ever prepends pairs of these two shapes, so
    this predicate holds along the entire back-and-forth. -/
def BuiltFrom (f g : ℕ → ℕ) (L : List (ℕ × ℕ)) : Prop :=
  ∀ ab ∈ L, ab.2 = f ab.1 ∨ ab.1 = g ab.2

/-- The empty matching is (vacuously) built from `f`, `g`. -/
theorem builtFrom_nil (f g : ℕ → ℕ) : BuiltFrom f g [] := by
  intro _ h; simp at h

/-- A domain step preserves the invariant: the new pair `(a, f a)` is an `f`-edge. -/
theorem builtFrom_cons_f {f g : ℕ → ℕ} {L : List (ℕ × ℕ)} (hB : BuiltFrom f g L)
    (a : ℕ) : BuiltFrom f g ((a, f a) :: L) := by
  intro ab hmem
  rcases List.mem_cons.mp hmem with h | h
  · subst h; exact Or.inl rfl
  · exact hB ab h

/-- A range step preserves the invariant: the new pair `(g c, c)` is a `g`-edge. -/
theorem builtFrom_cons_g {f g : ℕ → ℕ} {L : List (ℕ × ℕ)} (hB : BuiltFrom f g L)
    (c : ℕ) : BuiltFrom f g ((g c, c) :: L) := by
  intro ab hmem
  rcases List.mem_cons.mp hmem with h | h
  · subst h; exact Or.inr rfl
  · exact hB ab h

/-- The invariant is self-dual under coordinate swap, with `f`, `g` exchanged: an
    `f`-edge `(x, f x)` becomes a `g`-edge `(f x, x)` of the swapped problem, and a
    `g`-edge becomes an `f`-edge. This is what lets the range-side collision analysis be
    obtained from the domain-side one (Section 4e duality). -/
theorem builtFrom_map_swap {f g : ℕ → ℕ} {L : List (ℕ × ℕ)} (hB : BuiltFrom f g L) :
    BuiltFrom g f (L.map Prod.swap) := by
  intro ab hmem
  rw [List.mem_map] at hmem
  obtain ⟨cd, hcd, rfl⟩ := hmem
  exact (hB cd hcd).symm

/-- **Domain-side collision has a determined source.** Assume the matching `L` satisfies
    the construction invariant and `f` is injective, and we try to place a fresh domain
    point `a ∉ mDom L` via its image `f a`. If that image is already used
    (`f a ∈ mRan L` — the collision case *not* covered by `matching_step_f`), then the
    blocking pair is necessarily the `g`-edge `(g (f a), f a)`: the collision cannot come
    from an `f`-edge, since `f x = f a` would force `x = a ∈ mDom L`. Thus the element
    obstructing `a` is `g (f a)`, already in the domain — the next point of the orbit to
    chase. No decision of the Π₁ predicate `isGFree` is involved. -/
theorem collision_f_source {f g : ℕ → ℕ} (hf : Injective f)
    {L : List (ℕ × ℕ)} (hB : BuiltFrom f g L) {a : ℕ} (ha : a ∉ mDom L)
    (hfa : f a ∈ mRan L) : (g (f a), f a) ∈ L := by
  simp only [mRan, List.mem_map] at hfa
  obtain ⟨⟨u, w⟩, hmem, hw⟩ := hfa
  have hw' : w = f a := hw
  subst hw'
  rcases hB (u, f a) hmem with h | h
  · -- f-edge: `f a = f u` ⟹ `a = u` ⟹ `a ∈ mDom L`, contradicting freshness
    exfalso
    have hau : a = u := hf h
    apply ha
    rw [hau]
    exact List.mem_map.mpr ⟨(u, f a), hmem, rfl⟩
  · -- g-edge: `u = g (f a)`, so the blocking pair is `(g (f a), f a)`
    have hu : u = g (f a) := h
    rw [hu] at hmem
    exact hmem

/-- **Range-side collision has a determined source** (dual to `collision_f_source`).
    Assume the invariant and `g` injective, and try to place a fresh range point
    `c ∉ mRan L` via `g c`. If `g c` is already used in the domain (`g c ∈ mDom L`), the
    blocking pair is necessarily the `f`-edge `(g c, f (g c))`: it cannot be a `g`-edge,
    since `g w = g c` would force `w = c ∈ mRan L`. So the obstructing element is
    `f (g c)`, already in the range. -/
theorem collision_g_source {f g : ℕ → ℕ} (hg : Injective g)
    {L : List (ℕ × ℕ)} (hB : BuiltFrom f g L) {c : ℕ} (hc : c ∉ mRan L)
    (hgc : g c ∈ mDom L) : (g c, f (g c)) ∈ L := by
  simp only [mDom, List.mem_map] at hgc
  obtain ⟨⟨u, w⟩, hmem, hu⟩ := hgc
  have hu' : u = g c := hu
  subst hu'
  rcases hB (g c, w) hmem with h | h
  · -- f-edge: `w = f (g c)`, so the blocking pair is `(g c, f (g c))`
    have hw : w = f (g c) := h
    rw [hw] at hmem
    exact hmem
  · -- g-edge: `g c = g w` ⟹ `c = w` ⟹ `c ∈ mRan L`, contradicting freshness
    exfalso
    have hcw : c = w := hg h
    apply hc
    rw [hcw]
    exact List.mem_map.mpr ⟨(g c, w), hmem, rfl⟩

/-- **The domain step is either available or its blocker is named.** Combining the
    atomic freshness condition with `collision_f_source`: for a fresh domain point `a`,
    either `f a` is fresh in the range (so `matching_step_f` applies directly), or the
    matching already contains the specific `g`-edge `(g (f a), f a)` that blocks it. This
    is the case split the scheduler performs at each even stage — no unbounded search and
    no `isGFree` decision. -/
theorem step_f_available_or_collision {f g : ℕ → ℕ} (hf : Injective f)
    {L : List (ℕ × ℕ)} (hB : BuiltFrom f g L) {a : ℕ} (ha : a ∉ mDom L) :
    f a ∉ mRan L ∨ (g (f a), f a) ∈ L := by
  by_cases h : f a ∈ mRan L
  · exact Or.inr (collision_f_source hf hB ha h)
  · exact Or.inl h

/-!
## Section 4h: Correspondence is preserved along the chase — the general domain step

Sections 4·chase and 4g reduced the domain step to a *bounded* forward-orbit walk
(`fwdOrbit_chase_length_le`) whose collisions have a named source (`collision_f_source`).
What is still missing to actually *place* the fresh anchor `a` is the **correspondence**
half: whatever green point the chase lands on, the scheduler pairs `a` with it, and that
pairing must preserve `MatchingCorr p q` (Section 4c). This section supplies exactly that,
with no reference to the non-computable `isGFree`.

The key observation is that the reductions make the `p`-value **constant along the forward
orbit**: one orbit step `x ↦ g (f x)` crosses `p x → q (f x)` (the `f`-reduction) and back
`q (f x) → p (g (f x))` (the `g`-reduction), so `p (fwdOrbit f g a k) ↔ p a` for every `k`
(`fwdOrbit_pred_iff`). Hence the `k`-th green candidate `chaseTarget f g a k = f (fwdOrbit
f g a k)` always corresponds to the anchor: `p a ↔ q (chaseTarget f g a k)`
(`chaseTarget_corr`). Combining this with the freshness bookkeeping of Section 4c gives
`matching_step_chase`: prepending `(a, chaseTarget f g a k)` keeps the list a matching and
preserves the correspondence — the domain step valid at **any** chase depth `k`, not only
the collision-free `k = 0` case handled by `matching_step_f`.
-/

/-- **Membership is constant along the forward orbit.** Given the two reductions
    `p n ↔ q (f n)` and `q n ↔ p (g n)`, every forward-orbit point has the same
    `p`-value as the anchor: `p (fwdOrbit f g a k) ↔ p a`. One orbit step `x ↦ g (f x)`
    crosses to `q (f x)` (via the `f`-reduction) and back to `p (g (f x))` (via the
    `g`-reduction), leaving the `p`-value unchanged. -/
theorem fwdOrbit_pred_iff {p q : ℕ → Prop} {f g : ℕ → ℕ}
    (hfpq : ∀ n, p n ↔ q (f n)) (hgpq : ∀ n, q n ↔ p (g n))
    (a : ℕ) : ∀ k, p (fwdOrbit f g a k) ↔ p a := by
  intro k
  induction k with
  | zero => exact Iff.rfl
  | succ k ih =>
      rw [fwdOrbit_succ, ← hgpq (f (fwdOrbit f g a k)), ← hfpq (fwdOrbit f g a k)]
      exact ih

/-- **Collision-chase target.** The `k`-th green point the domain step inspects while
    chasing a collision from a fresh anchor `a`: `chaseTarget f g a k = f (fwdOrbit f g a
    k)`. Stage `0` is the naive image `f a`; each further stage advances one forward-orbit
    step ("apply `g` then `f`"), matching the informal chase rule "apply `f`; if the green
    point is taken, apply `g` then `f` repeatedly until a fresh green point is found". -/
def chaseTarget (f g : ℕ → ℕ) (a k : ℕ) : ℕ := f (fwdOrbit f g a k)

@[simp] theorem chaseTarget_zero (f g : ℕ → ℕ) (a : ℕ) :
    chaseTarget f g a 0 = f a := rfl

/-- **Chase-target recurrence** ("apply `g` then `f`"): each successive green candidate is
    obtained from the previous one by `x ↦ f (g x)`. Confirms `chaseTarget` realises the
    informal alternation and links it to the forward-orbit recurrence `fwdOrbit_succ`. -/
theorem chaseTarget_succ (f g : ℕ → ℕ) (a k : ℕ) :
    chaseTarget f g a (k + 1) = f (g (chaseTarget f g a k)) := by
  simp only [chaseTarget, fwdOrbit_succ]

/-- **Correspondence at every chase target.** Whatever fresh green point the bounded chase
    lands on, it corresponds to the anchor: `p a ↔ q (chaseTarget f g a k)`. This is the
    correspondence invariant the scheduler needs to pair `a` with the discovered fresh
    target while preserving `MatchingCorr`, complementing the termination bound
    `fwdOrbit_chase_length_le`. -/
theorem chaseTarget_corr {p q : ℕ → Prop} {f g : ℕ → ℕ}
    (hfpq : ∀ n, p n ↔ q (f n)) (hgpq : ∀ n, q n ↔ p (g n))
    (a k : ℕ) : p a ↔ q (chaseTarget f g a k) :=
  (fwdOrbit_pred_iff hfpq hgpq a k).symm.trans (hfpq (fwdOrbit f g a k))

/-- **The chase target is computable** as a two-argument function of anchor and stage,
    since `fwdOrbit` is (`fwdOrbit_computable`) and `f` is. This keeps the domain step's
    bounded search computable. -/
theorem chaseTarget_computable {f g : ℕ → ℕ} (hf : Computable f) (hg : Computable g) :
    Computable₂ (chaseTarget f g) := by
  have h : Computable (fun p : ℕ × ℕ => f (fwdOrbit f g p.1 p.2)) :=
    hf.comp (fwdOrbit_computable hf hg)
  exact h.of_eq (fun p => rfl)

/-- **The general domain step (any chase depth).** If the anchor `a` is fresh in the
    domain and the chase target `chaseTarget f g a k` is fresh in the range, then
    prepending `(a, chaseTarget f g a k)` keeps the list a matching *and* preserves the
    correspondence `p ↔ q`. This is `matching_step_f` extended past the collision-free
    `k = 0` case: it is exactly the extension the scheduler performs once the bounded
    collision chase (Section 4·chase) has located a fresh green target. -/
theorem matching_step_chase {p q : ℕ → Prop} {f g : ℕ → ℕ}
    (hfpq : ∀ n, p n ↔ q (f n)) (hgpq : ∀ n, q n ↔ p (g n))
    {L : List (ℕ × ℕ)} (hL : IsMatching L) (hC : MatchingCorr p q L)
    {a k : ℕ} (ha : a ∉ mDom L) (ht : chaseTarget f g a k ∉ mRan L) :
    IsMatching ((a, chaseTarget f g a k) :: L) ∧
      MatchingCorr p q ((a, chaseTarget f g a k) :: L) :=
  ⟨isMatching_cons hL ha ht, matchingCorr_cons hC (chaseTarget_corr hfpq hgpq a k)⟩


/-!
## Section 4i: Escape existence — the collision chase always finds a fresh target

Sections 4·chase / 4g / 4h supply the pieces of the domain step *given* a fresh green
target `chaseTarget f g a N ∉ mRan L` (`matching_step_chase`). What was still open — the
residual crux flagged across several prior sessions — is that such an `N` **exists**: the
bounded collision chase cannot collide forever. This section closes that gap, with no
reference to the non-computable Π₁ predicate `isGFree`.

The key is that a *persistent* collision forces the forward orbit into the finite occupied
domain `mDom L`. At each colliding stage the blocker is the `g`-edge `(fwdOrbit f g a (k+1),
f (fwdOrbit f g a k))`; the alternative `f`-edge is ruled out by **matching functionality** —
an `f`-edge at `fwdOrbit f g a k` would share a domain point with the previous stage's
`g`-edge, forcing (`matching_functional` + injectivity of `f`) an orbit repeat, hence — via
`fwdOrbit_prefix_distinct` — `a ∈ mDom L`, contradicting freshness. So every chase point lies
in `mDom L`, and `fwdOrbit_chase_length_le` bounds the chase by `L.length`; a chase surviving
`L.length + 1` collisions is impossible, so some stage `N ≤ L.length` escapes.

This resolves the specific "escape existence is not free" obstruction recorded in the
knowledge base: the naive "keep colliding ⟹ stay in `mDom L`" induction does fail *pointwise*,
but the `g`-edge chain (threaded through matching functionality) recovers it.
-/

/-- **The persistent-collision `g`-edge chain.** If every green candidate up to (but not
    including) stage `N` is already used (`f (fwdOrbit f g a j) ∈ mRan L` for `j < N`), then
    for every `1 ≤ m ≤ N` the matching contains the `g`-edge `(fwdOrbit f g a m,
    f (fwdOrbit f g a (m-1)))`. In particular each chase point `fwdOrbit f g a m` then lies in
    `mDom L`. The `f`-edge alternative is excluded by matching functionality (it would create
    an orbit repeat and hence, by freshness of `a`, a contradiction). Proved by induction on
    the stage bound `t`, so the inductive hypothesis supplies *all* earlier `g`-edges at once —
    exactly what the functionality/acyclicity argument consumes. -/
theorem chase_gedge_chain {f g : ℕ → ℕ} (hf : Function.Injective f)
    (hg : Function.Injective g) {L : List (ℕ × ℕ)} (hL : IsMatching L) (hB : BuiltFrom f g L)
    {a : ℕ} (ha : a ∉ mDom L) {N : ℕ}
    (hcoll : ∀ j, j < N → f (fwdOrbit f g a j) ∈ mRan L) :
    ∀ t, t ≤ N → ∀ m, 1 ≤ m → m ≤ t →
      (fwdOrbit f g a m, f (fwdOrbit f g a (m - 1))) ∈ L := by
  intro t
  induction t with
  | zero => intro _ m hm1 hm0; omega
  | succ i IH =>
    intro hiN m hm1 hmi
    have hiN' : i ≤ N := by omega
    rcases Nat.lt_or_ge m (i + 1) with hlt | _
    · exact IH hiN' m hm1 (by omega)
    · have hm : m = i + 1 := by omega
      subst hm
      have himg : f (fwdOrbit f g a i) ∈ mRan L := hcoll i (by omega)
      simp only [mRan, List.mem_map] at himg
      obtain ⟨⟨u, w⟩, hmem, hw⟩ := himg
      have hw' : w = f (fwdOrbit f g a i) := hw
      subst hw'
      have hstep : fwdOrbit f g a (i + 1) = g (f (fwdOrbit f g a i)) := fwdOrbit_succ f g a i
      have hidx : (i + 1) - 1 = i := by omega
      rw [hidx]
      rcases hB (u, f (fwdOrbit f g a i)) hmem with hedge | hedge
      · -- f-edge: `f (o i) = f u ⟹ u = o i`; then matching functionality forces a repeat
        have hue : f (fwdOrbit f g a i) = f u := hedge
        have hu : u = fwdOrbit f g a i := (hf hue).symm
        rw [hu] at hmem
        rcases Nat.eq_zero_or_pos i with hi0 | hipos
        · exfalso
          apply ha
          subst hi0
          exact List.mem_map.mpr ⟨(fwdOrbit f g a 0, f (fwdOrbit f g a 0)), hmem, rfl⟩
        · exfalso
          have hprev : (fwdOrbit f g a i, f (fwdOrbit f g a (i - 1))) ∈ L :=
            IH hiN' i hipos (by omega)
          have hfun : f (fwdOrbit f g a i) = f (fwdOrbit f g a (i - 1)) :=
            matching_functional hL hmem hprev
          have hrepeat : fwdOrbit f g a i = fwdOrbit f g a (i - 1) := hf hfun
          have hdomk : ∀ k, 1 ≤ k → k ≤ i → fwdOrbit f g a k ∈ mDom L := by
            intro k hk1 hki
            have hk := IH hiN' k hk1 hki
            exact List.mem_map.mpr ⟨(fwdOrbit f g a k, f (fwdOrbit f g a (k - 1))), hk, rfl⟩
          have hinj := fwdOrbit_prefix_distinct hf hg (D := fun n => n ∈ mDom L) ha
            (N := i) hdomk
          have hcontra : i = i - 1 := hinj (le_refl i) (by omega) hrepeat
          omega
      · -- g-edge: `u = g (f (o i)) = o (i+1)`
        have hue : u = g (f (fwdOrbit f g a i)) := hedge
        have hu : u = fwdOrbit f g a (i + 1) := by rw [hue]; exact hstep.symm
        rw [hu] at hmem
        exact hmem

/-!
## Section 4i-bis: `BuiltFrom`-free escape via the orbit dichotomy

`escape_exists` (below) discharges the domain step's termination obligation from the
`BuiltFrom` construction invariant — the hypothesis that every recorded pair is an
`f`-edge `(x, f x)` or a `g`-edge `(g y, y)`. Carrying `BuiltFrom` forces the
augmenting-path list surgery (Section 4j) at every stage. The extension-only (cons)
scheduler resolved in the 2026-07-03 fork replaces `BuiltFrom` by the cons-preserved
**cycle-balance** invariant, and its escape obligation splits by the dichotomy on
whether the anchor's forward orbit is periodic (`OnCycle`) or infinite.

This section proves the **infinite-orbit half** — the `BuiltFrom`-free, `Balanced`-free
pigeonhole that is self-contained: if `a` is not `g∘f`-periodic then the forward-orbit
map is globally injective, so `f (fwdOrbit f g a ·)` is injective and cannot embed the
`(mRan L).length + 1` stages `0, …, (mRan L).length` into the smaller occupied range
`mRan L`. The periodic half (`escape_of_balanced`) needs the balance invariant and is
left for the scheduler-assembly session; combined they give `escape_exists'`.
-/

/-- `a` is periodic under `g ∘ f`: its forward orbit returns to the anchor. Under injective
    `g ∘ f` this is the exact complement of an all-distinct (infinite) forward orbit — there
    are no ρ-shaped orbits, since injectivity forbids a tail merging into a cycle. -/
def OnCycle (f g : ℕ → ℕ) (a : ℕ) : Prop := ∃ m, 1 ≤ m ∧ fwdOrbit f g a m = a

/-- **Non-periodic ⟹ globally injective forward orbit.** If `a` is not `g∘f`-periodic then
    `fwdOrbit f g a` is injective on all of `ℕ`. A collision `fwdOrbit a i = fwdOrbit a j`
    with `i < j` would, cancelling the shared injective prefix `(g∘f)^[i]`, force
    `a = (g∘f)^[j-i] a = fwdOrbit a (j-i)` with `1 ≤ j-i`, i.e. `OnCycle f g a`. -/
theorem fwdOrbit_injective_of_not_onCycle {f g : ℕ → ℕ}
    (hf : Function.Injective f) (hg : Function.Injective g)
    {a : ℕ} (hac : ¬ OnCycle f g a) :
    Function.Injective (fwdOrbit f g a) := by
  have hT : Function.Injective (fun x => g (f x)) := fun x y h => hf (hg h)
  have hiter : ∀ k, fwdOrbit f g a k = (fun x => g (f x))^[k] a :=
    fun k => fwdOrbit_eq_iterate f g a k
  intro i j hij
  rcases le_total i j with hle | hle
  · obtain ⟨d, rfl⟩ := Nat.le.dest hle
    rcases Nat.eq_zero_or_pos d with hd | hd
    · omega
    · exfalso
      rw [hiter i, hiter (i + d), Function.iterate_add_apply] at hij
      have hax : a = (fun x => g (f x))^[d] a := (hT.iterate i) hij
      exact hac ⟨d, hd, by rw [hiter d]; exact hax.symm⟩
  · obtain ⟨d, rfl⟩ := Nat.le.dest hle
    rcases Nat.eq_zero_or_pos d with hd | hd
    · omega
    · exfalso
      rw [hiter (j + d), hiter j, Function.iterate_add_apply] at hij
      have hax : (fun x => g (f x))^[d] a = a := (hT.iterate j) hij
      exact hac ⟨d, hd, by rw [hiter d]; exact hax⟩

/-- **Infinite-orbit escape (`BuiltFrom`-free).** If the anchor `a` is not `g∘f`-periodic,
    then within the first `(mRan L).length + 1` forward-orbit stages some green image
    `f (fwdOrbit f g a N)` escapes the occupied range `mRan L`. This is the easy half of the
    extension-only scheduler's escape obligation: no construction invariant is needed, only
    that the orbit is genuinely infinite (injective). Were every stage `N ≤ (mRan L).length`
    a collision, `f ∘ fwdOrbit f g a` would inject the `(mRan L).length + 1` stages into the
    `≤ (mRan L).length`-element finset `(mRan L).toFinset` — a pigeonhole contradiction. -/
theorem escape_of_infinite_orbit {f g : ℕ → ℕ}
    (hf : Function.Injective f) (hg : Function.Injective g)
    {L : List (ℕ × ℕ)} {a : ℕ} (hac : ¬ OnCycle f g a) :
    ∃ N, N ≤ (mRan L).length ∧ f (fwdOrbit f g a N) ∉ mRan L := by
  by_contra hcon
  push_neg at hcon
  have horb : Function.Injective (fwdOrbit f g a) :=
    fwdOrbit_injective_of_not_onCycle hf hg hac
  have hmap : Function.Injective (fun k => f (fwdOrbit f g a k)) := hf.comp horb
  have hInj : Set.InjOn (fun k => f (fwdOrbit f g a k))
      ↑(Finset.range ((mRan L).length + 1)) := fun i _ j _ hij => hmap hij
  have hmaps : ∀ k ∈ Finset.range ((mRan L).length + 1),
      (fun k => f (fwdOrbit f g a k)) k ∈ (mRan L).toFinset := by
    intro k hk
    simp only [Finset.mem_range] at hk
    exact List.mem_toFinset.mpr (hcon k (by omega))
  have hcard : (Finset.range ((mRan L).length + 1)).card ≤ (mRan L).toFinset.card :=
    Finset.card_le_card_of_injOn _ hmaps hInj
  rw [Finset.card_range] at hcard
  have hle := le_trans hcard (List.toFinset_card_le (mRan L))
  omega

/-!
### Cycle-period infrastructure for the periodic (`OnCycle`) arm

The periodic half `escape_of_balanced` (scaffold step 4) counts points on the finite
`g∘f`-cycle through `a`. Whatever Lean encoding of "cycle" the `Balanced` invariant
eventually uses, it rests on the **least positive period** `orbitPeriod` and the fact
that the first `period` orbit points are *distinct* — so the cycle is exactly the image
`(Finset.range orbitPeriod).image (fwdOrbit f g a)`, of cardinality `orbitPeriod`. These
lemmas are built here, independent of the (still-open) `Balanced` encoding choice, so the
step-4 session can pick an encoding on top of a verified period/cardinality substrate.
-/

/-- The least positive period of a `g∘f`-periodic anchor. Well-defined and computable:
    `OnCycle f g a = ∃ m, 1 ≤ m ∧ fwdOrbit f g a m = a` is a decidable predicate over `ℕ`
    (`≤` and `Nat` equality are decidable), so `Nat.find` applies. -/
def orbitPeriod (f g : ℕ → ℕ) {a : ℕ} (h : OnCycle f g a) : ℕ := Nat.find h

theorem orbitPeriod_pos {f g : ℕ → ℕ} {a : ℕ} (h : OnCycle f g a) :
    1 ≤ orbitPeriod f g h := (Nat.find_spec h).1

theorem fwdOrbit_orbitPeriod {f g : ℕ → ℕ} {a : ℕ} (h : OnCycle f g a) :
    fwdOrbit f g a (orbitPeriod f g h) = a := (Nat.find_spec h).2

/-- Minimality of the period: no positive `m` below `orbitPeriod` returns the orbit to `a`. -/
theorem orbitPeriod_min {f g : ℕ → ℕ} {a : ℕ} (h : OnCycle f g a) {m : ℕ}
    (hm : 1 ≤ m) (hlt : m < orbitPeriod f g h) : fwdOrbit f g a m ≠ a := by
  intro heq
  exact Nat.find_min h hlt ⟨hm, heq⟩

/-- **The period prefix is injective.** The first `orbitPeriod` forward-orbit points
    `fwdOrbit f g a 0, …, fwdOrbit f g a (orbitPeriod-1)` are pairwise distinct: a repeat
    at `i < j < period` would cancel the shared injective prefix `(g∘f)^[i]` to give
    `fwdOrbit f g a (j-i) = a` with `1 ≤ j-i < period`, contradicting minimality. -/
theorem fwdOrbit_injOn_range_period {f g : ℕ → ℕ}
    (hf : Function.Injective f) (hg : Function.Injective g)
    {a : ℕ} (h : OnCycle f g a) :
    Set.InjOn (fwdOrbit f g a) ↑(Finset.range (orbitPeriod f g h)) := by
  have hT : Function.Injective (fun x => g (f x)) := fun x y hxy => hf (hg hxy)
  have hiter : ∀ k, fwdOrbit f g a k = (fun x => g (f x))^[k] a :=
    fun k => fwdOrbit_eq_iterate f g a k
  intro i hi j hj hij
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  rcases le_total i j with hle | hle
  · obtain ⟨d, rfl⟩ := Nat.le.dest hle
    rcases Nat.eq_zero_or_pos d with hd | hd
    · omega
    · exfalso
      rw [hiter i, hiter (i + d), Function.iterate_add_apply] at hij
      have hax : a = (fun x => g (f x))^[d] a := (hT.iterate i) hij
      exact orbitPeriod_min h hd (by omega) (by rw [hiter d]; exact hax.symm)
  · obtain ⟨d, rfl⟩ := Nat.le.dest hle
    rcases Nat.eq_zero_or_pos d with hd | hd
    · omega
    · exfalso
      rw [hiter (j + d), hiter j, Function.iterate_add_apply] at hij
      have hax : (fun x => g (f x))^[d] a = a := (hT.iterate j) hij
      exact orbitPeriod_min h hd (by omega) (by rw [hiter d]; exact hax)

/-- **The finite `g∘f`-cycle through a periodic anchor `a`.** The image of the least-period
    prefix under the forward orbit: `{a, g(f a), (g∘f)² a, …, (g∘f)^{period-1} a}`. This is the
    ready-made `Finset` the `Balanced` invariant counts occupancy over — no bespoke cycle-set
    machinery, and its cardinality is proven below (`orbitCycle_card`). -/
def orbitCycle (f g : ℕ → ℕ) {a : ℕ} (h : OnCycle f g a) : Finset ℕ :=
  (Finset.range (orbitPeriod f g h)).image (fwdOrbit f g a)

/-- The anchor lies on its own cycle (stage `0`). -/
theorem self_mem_orbitCycle {f g : ℕ → ℕ} {a : ℕ} (h : OnCycle f g a) :
    a ∈ orbitCycle f g h := by
  refine Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (orbitPeriod_pos h), rfl⟩

/-- Membership in the cycle is exactly "reached within one period". -/
theorem mem_orbitCycle_iff {f g : ℕ → ℕ} {a x : ℕ} (h : OnCycle f g a) :
    x ∈ orbitCycle f g h ↔ ∃ k, k < orbitPeriod f g h ∧ fwdOrbit f g a k = x := by
  simp only [orbitCycle, Finset.mem_image, Finset.mem_range]

/-- **The cycle through `a` has exactly `orbitPeriod` points.** Injectivity of the period
    prefix (`fwdOrbit_injOn_range_period`) gives its cardinality `= orbitPeriod`. This is the
    cardinal the `Balanced` counting argument (scaffold step 3/4) compares against `mDom`/`mRan`
    occupancy. -/
theorem orbitCycle_card {f g : ℕ → ℕ}
    (hf : Function.Injective f) (hg : Function.Injective g)
    {a : ℕ} (h : OnCycle f g a) :
    (orbitCycle f g h).card = orbitPeriod f g h := by
  rw [orbitCycle, Finset.card_image_of_injOn (fwdOrbit_injOn_range_period hf hg h),
    Finset.card_range]

/-!
### Section 4i-ter: The cycle-balance invariant and the periodic (`OnCycle`) escape arm

The extension-only scheduler carries the **cons-preserved balance invariant** in place of
`BuiltFrom`: on every `g∘f`-cycle the recorded domain occupancy equals the recorded range
occupancy of the cycle's `f`-image. This section defines `Balanced`, proves the base case
`balanced_nil`, and closes the **periodic escape arm** `escape_of_balanced` — the second half
of the `BuiltFrom`-free escape dichotomy. Combined with `escape_of_infinite_orbit` (Section
4i-bis) it yields `escape_exists'`, the drop-in `Balanced`-hypothesised replacement for
`escape_exists`. The invariant-preservation lemmas (`balanced_cons_domain`/`_range`) that let
the scheduler *maintain* `Balanced` are the remaining piece, left for the assembly session.
-/

/-- **The cycle-balance invariant.** For every `g∘f`-cycle `C` (indexed by any periodic anchor
    `a`), the number of cycle points already recorded in the domain equals the number of
    `f`-images of cycle points already recorded in the range:
    `(C ∩ mDom L).card = (f '' C ∩ mRan L).card`. Faithfully encoded over the ready-made
    `orbitCycle`. This is the conserved quantity of the extension-only back-and-forth: each cons
    adds exactly one fresh domain point and one fresh range point on the affected cycle. -/
def Balanced (f g : ℕ → ℕ) (L : List (ℕ × ℕ)) : Prop :=
  ∀ {a : ℕ} (h : OnCycle f g a),
    ((orbitCycle f g h) ∩ (mDom L).toFinset).card
      = ((orbitCycle f g h).image f ∩ (mRan L).toFinset).card

/-- **Base case.** The empty matching is balanced: both intersections are empty (nothing is
    recorded), so both cardinalities are `0` on every cycle. -/
theorem balanced_nil (f g : ℕ → ℕ) : Balanced f g [] := by
  intro a h
  simp only [mDom, mRan, List.map_nil, List.toFinset_nil, Finset.inter_empty, Finset.card_empty]

/-- **Periodic escape (`Balanced`).** If the anchor `a` is `g∘f`-periodic and `L` is balanced,
    then a fresh domain anchor `a ∉ mDom L` still escapes: some forward-orbit stage
    `N ≤ (mRan L).length` has a green image `f (fwdOrbit f g a N)` outside `mRan L`.

    *Why.* Let `C` be `a`'s cycle, of size `m = period`. Since `a ∈ C` but `a ∉ mDom L`,
    `(C ∩ mDom L).card ≤ m - 1`. Balance transports this: `(f '' C ∩ mRan L).card ≤ m - 1 < m =
    |f '' C|` (the last equality by injectivity of `f` on `C`). So `f '' C ⊄ mRan L`: some cycle
    point's `f`-image is fresh. Taking the *least* escaping stage `N` and using injectivity of
    `f ∘ fwdOrbit` on `{0,…,N}` (all inside one period), the `N` earlier collisions are distinct
    range points, giving `N ≤ (mRan L).length`. -/
theorem escape_of_balanced {f g : ℕ → ℕ}
    (hf : Function.Injective f) (hg : Function.Injective g)
    {L : List (ℕ × ℕ)} (hbal : Balanced f g L)
    {a : ℕ} (hac : OnCycle f g a) (ha : a ∉ mDom L) :
    ∃ N, N ≤ (mRan L).length ∧ f (fwdOrbit f g a N) ∉ mRan L := by
  classical
  have hbalance := hbal hac
  set m := orbitPeriod f g hac with hm
  set C := orbitCycle f g hac with hCdef
  have hmpos : 1 ≤ m := orbitPeriod_pos hac
  have hCcard : C.card = m := orbitCycle_card hf hg hac
  -- `f` is injective on `C`, so its image has the full `m` points.
  have hImgCard : (C.image f).card = m := by
    rw [Finset.card_image_of_injOn (hf.injOn), hCcard]
  -- the anchor is on its cycle but not in the recorded domain
  have haC : a ∈ C := self_mem_orbitCycle hac
  have haDom : a ∉ (mDom L).toFinset := by simpa [List.mem_toFinset] using ha
  -- domain occupancy of the cycle misses `a`, so is at most `m - 1`
  have hInterDom : (C ∩ (mDom L).toFinset).card ≤ m - 1 := by
    have hsub : C ∩ (mDom L).toFinset ⊆ C.erase a := by
      intro x hx
      rw [Finset.mem_inter] at hx
      rw [Finset.mem_erase]
      exact ⟨fun hxa => haDom (hxa ▸ hx.2), hx.1⟩
    calc (C ∩ (mDom L).toFinset).card
        ≤ (C.erase a).card := Finset.card_le_card hsub
      _ = C.card - 1 := Finset.card_erase_of_mem haC
      _ = m - 1 := by rw [hCcard]
  -- balance transports the domain bound to the range side
  have hRanBound : (C.image f ∩ (mRan L).toFinset).card ≤ m - 1 := by
    rw [← hbalance]; exact hInterDom
  -- so the `f`-image is not fully occupied: strictly fewer than its `m` points are in range
  have hlt : (C.image f ∩ (mRan L).toFinset).card < (C.image f).card := by
    rw [hImgCard]; omega
  have hnsub : ¬ (C.image f ⊆ (mRan L).toFinset) := by
    intro hsub
    rw [Finset.inter_eq_left.mpr hsub] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨y, hyImg, hyRan⟩ := Finset.not_subset.mp hnsub
  -- unpack the fresh `f`-image `y = f (fwdOrbit f g a k)` with `k < m`
  rw [Finset.mem_image] at hyImg
  obtain ⟨x, hxC, hxy⟩ := hyImg
  rw [hCdef, mem_orbitCycle_iff] at hxC
  obtain ⟨k, hk, hkx⟩ := hxC
  rw [← hm] at hk
  have hk_fresh : f (fwdOrbit f g a k) ∉ mRan L := by
    rw [hkx, hxy]
    exact fun hy => hyRan (List.mem_toFinset.mpr hy)
  have hex : ∃ N, f (fwdOrbit f g a N) ∉ mRan L := ⟨k, hk_fresh⟩
  -- take the least escaping stage
  set N := Nat.find hex with hN
  have hNspec : f (fwdOrbit f g a N) ∉ mRan L := Nat.find_spec hex
  have hNle_k : N ≤ k := Nat.find_min' hex hk_fresh
  have hN_lt_m : N < m := lt_of_le_of_lt hNle_k hk
  -- every earlier stage is a collision (in range)
  have hcoll : ∀ j, j < N → f (fwdOrbit f g a j) ∈ mRan L := by
    intro j hj
    have := Nat.find_min hex hj
    exact not_not.mp this
  -- the earlier collisions are distinct range points ⇒ `N ≤ length`
  have hInjOn : Set.InjOn (fun j => f (fwdOrbit f g a j)) ↑(Finset.range N) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    exact fwdOrbit_injOn_range_period hf hg hac
      (by simp only [Finset.coe_range, Set.mem_Iio]; omega)
      (by simp only [Finset.coe_range, Set.mem_Iio]; omega) (hf hij)
  have hmaps : ∀ j ∈ Finset.range N,
      (fun j => f (fwdOrbit f g a j)) j ∈ (mRan L).toFinset := by
    intro j hj
    rw [Finset.mem_range] at hj
    exact List.mem_toFinset.mpr (hcoll j hj)
  have hcard : (Finset.range N).card ≤ (mRan L).toFinset.card :=
    Finset.card_le_card_of_injOn _ hmaps hInjOn
  rw [Finset.card_range] at hcard
  exact ⟨N, le_trans hcard (List.toFinset_card_le (mRan L)), hNspec⟩

/-- **`BuiltFrom`-free escape, by dichotomy on `OnCycle`.** For a fresh domain anchor `a` in a
    balanced matching, some forward-orbit stage has a green image outside `mRan L` — regardless
    of whether `a`'s orbit is a finite cycle (`escape_of_balanced`) or infinite
    (`escape_of_infinite_orbit`). This is the drop-in replacement for the `BuiltFrom`-hypothesised
    `escape_exists`: the extension-only scheduler carries `Balanced` (cons-preserved) instead. -/
theorem escape_exists' {f g : ℕ → ℕ}
    (hf : Function.Injective f) (hg : Function.Injective g)
    {L : List (ℕ × ℕ)} (hbal : Balanced f g L) {a : ℕ} (ha : a ∉ mDom L) :
    ∃ N, f (fwdOrbit f g a N) ∉ mRan L := by
  by_cases hac : OnCycle f g a
  · obtain ⟨N, _, hN⟩ := escape_of_balanced hf hg hbal hac ha
    exact ⟨N, hN⟩
  · obtain ⟨N, _, hN⟩ := escape_of_infinite_orbit hf hg hac (L := L)
    exact ⟨N, hN⟩

/-!
### Section 4i-quater: Cons-preservation of `Balanced` (Claim B)

The scheduler *maintains* `Balanced` across a domain (even) step that prepends `(a, b)` with
`a` a fresh domain anchor and `b = f (fwdOrbit f g a N)` the escaped green image. On the cycle
through `a`, the cons adds exactly one fresh domain point (`a`) and one fresh range point (`b`,
which lands in that same cycle's `f`-image because the forward orbit stays on the cycle); on
every *other* cycle both intersections are inert (`b` cannot land in a foreign cycle's image,
by injectivity and the no-tails property of an injective `g ∘ f`). Both facts rest on a short
tower of orbit-algebra lemmas proved first: additivity of `fwdOrbit`, period wrap-around, and
the "reach / back / closure" membership characterisations of `orbitCycle`. -/

/-- **Additivity of the forward orbit.** Running `i + j` steps from `a` equals running `i` steps
    from the `j`-step point. Immediate from `fwdOrbit_eq_iterate` and `Function.iterate_add_apply`. -/
theorem fwdOrbit_add (f g : ℕ → ℕ) (a i j : ℕ) :
    fwdOrbit f g a (i + j) = fwdOrbit f g (fwdOrbit f g a j) i := by
  simp only [fwdOrbit_eq_iterate, Function.iterate_add_apply]

/-- Adding a full period to the step count leaves the forward orbit unchanged. -/
theorem fwdOrbit_add_period {f g : ℕ → ℕ} {a : ℕ} (h : OnCycle f g a) (m : ℕ) :
    fwdOrbit f g a (m + orbitPeriod f g h) = fwdOrbit f g a m := by
  rw [fwdOrbit_add, fwdOrbit_orbitPeriod]

/-- Adding any multiple of the period leaves the forward orbit unchanged. -/
theorem fwdOrbit_add_mul_period {f g : ℕ → ℕ} {a : ℕ} (h : OnCycle f g a) (m t : ℕ) :
    fwdOrbit f g a (m + orbitPeriod f g h * t) = fwdOrbit f g a m := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hstep : m + orbitPeriod f g h * (t + 1)
          = (m + orbitPeriod f g h * t) + orbitPeriod f g h := by ring
      rw [hstep, fwdOrbit_add_period, ih]

/-- A pure multiple of the period returns the orbit to the anchor. -/
theorem fwdOrbit_mul_period {f g : ℕ → ℕ} {a : ℕ} (h : OnCycle f g a) (t : ℕ) :
    fwdOrbit f g a (orbitPeriod f g h * t) = a := by
  have hz := fwdOrbit_add_mul_period h 0 t
  rw [Nat.zero_add] at hz
  rw [hz]; rfl

/-- Reducing the step count modulo the period leaves the forward orbit unchanged. -/
theorem fwdOrbit_mod_period {f g : ℕ → ℕ} {a : ℕ} (h : OnCycle f g a) (m : ℕ) :
    fwdOrbit f g a (m % orbitPeriod f g h) = fwdOrbit f g a m := by
  conv_rhs => rw [← Nat.mod_add_div m (orbitPeriod f g h), fwdOrbit_add_mul_period]

/-- **Reach ⟹ membership.** Any point forward-reachable from the anchor `a` lies on `a`'s cycle
    (wrap the reaching step count modulo the period into the `< period` window). -/
theorem mem_orbitCycle_of_reach {f g : ℕ → ℕ} {a x : ℕ} (h : OnCycle f g a)
    (k : ℕ) (hk : fwdOrbit f g a k = x) : x ∈ orbitCycle f g h := by
  rw [mem_orbitCycle_iff]
  exact ⟨k % orbitPeriod f g h, Nat.mod_lt _ (orbitPeriod_pos h), by
    rw [fwdOrbit_mod_period]; exact hk⟩

/-- **Every cycle point is periodic.** A point reached within one period of a periodic anchor is
    itself `g∘f`-periodic (return to it after a full period). -/
theorem onCycle_of_mem_orbitCycle {f g : ℕ → ℕ} {a x : ℕ} (h : OnCycle f g a)
    (hx : x ∈ orbitCycle f g h) : OnCycle f g x := by
  rw [mem_orbitCycle_iff] at hx
  obtain ⟨k, _, hkx⟩ := hx
  refine ⟨orbitPeriod f g h, orbitPeriod_pos h, ?_⟩
  rw [← hkx, ← fwdOrbit_add, add_comm, fwdOrbit_add_period]

/-- **Cycles are closed under the forward orbit.** Stepping forward from any cycle point stays on
    the cycle. -/
theorem fwdOrbit_mem_orbitCycle {f g : ℕ → ℕ} {a x : ℕ} (h : OnCycle f g a)
    (hx : x ∈ orbitCycle f g h) (N : ℕ) : fwdOrbit f g x N ∈ orbitCycle f g h := by
  rw [mem_orbitCycle_iff] at hx
  obtain ⟨k, _, hkx⟩ := hx
  apply mem_orbitCycle_of_reach h (N + k)
  rw [fwdOrbit_add, hkx]

/-- **No tails (injectivity).** If a forward-orbit point `fwdOrbit f g a N` is `g∘f`-periodic then
    so is its base `a`: cancel the shared injective prefix `(g∘f)^[N]`. This is exactly why an
    injective `g ∘ f` has no ρ-shaped orbits — a tail cannot merge into a cycle. -/
theorem onCycle_of_fwdOrbit {f g : ℕ → ℕ}
    (hf : Function.Injective f) (hg : Function.Injective g)
    {a N : ℕ} (h : OnCycle f g (fwdOrbit f g a N)) : OnCycle f g a := by
  obtain ⟨q, hq1, hq⟩ := h
  have hT : Function.Injective (fun x => g (f x)) := fun x y hxy => hf (hg hxy)
  refine ⟨q, hq1, ?_⟩
  rw [← fwdOrbit_add] at hq
  simp only [fwdOrbit_eq_iterate] at hq ⊢
  rw [Nat.add_comm, Function.iterate_add_apply] at hq
  exact hT.iterate N hq

/-- **Back to the anchor.** From any cycle point one reaches the anchor again in `period - k`
    steps. -/
theorem exists_fwdOrbit_eq_anchor {f g : ℕ → ℕ} {a x : ℕ} (h : OnCycle f g a)
    (hx : x ∈ orbitCycle f g h) : ∃ j, fwdOrbit f g x j = a := by
  rw [mem_orbitCycle_iff] at hx
  obtain ⟨k, hk, hkx⟩ := hx
  refine ⟨orbitPeriod f g h - k, ?_⟩
  rw [← hkx, ← fwdOrbit_add]
  have hkk : orbitPeriod f g h - k + k = orbitPeriod f g h := by omega
  rw [hkk, fwdOrbit_orbitPeriod]

/-- **Foreign-cycle exclusion.** If a forward-orbit point of a periodic base `a` lands on a cycle
    `C_c`, then `a` itself is on `C_c`. (Reach `c` from `a`, then close the loop back to `a` using
    `a`'s own period.) This forces the escaped image to land only on `a`'s own cycle. -/
theorem mem_orbitCycle_of_fwdOrbit_mem {f g : ℕ → ℕ} {c a : ℕ} (hc : OnCycle f g c)
    (ha : OnCycle f g a) {N : ℕ} (hmem : fwdOrbit f g a N ∈ orbitCycle f g hc) :
    a ∈ orbitCycle f g hc := by
  obtain ⟨j, hj⟩ := exists_fwdOrbit_eq_anchor hc hmem
  rw [← fwdOrbit_add] at hj      -- hj : fwdOrbit f g a (j + N) = c
  set m := j + N with hmdef
  have hpapos : 0 < orbitPeriod f g ha := orbitPeriod_pos ha
  have key : (orbitPeriod f g ha - m % orbitPeriod f g ha) + m
      = orbitPeriod f g ha * (m / orbitPeriod f g ha + 1) := by
    have h1 : orbitPeriod f g ha * (m / orbitPeriod f g ha) + m % orbitPeriod f g ha = m :=
      Nat.div_add_mod m (orbitPeriod f g ha)
    have h2 : m % orbitPeriod f g ha < orbitPeriod f g ha := Nat.mod_lt m hpapos
    rw [Nat.mul_add, Nat.mul_one]
    omega
  apply mem_orbitCycle_of_reach hc (orbitPeriod f g ha - m % orbitPeriod f g ha)
  rw [← hj, ← fwdOrbit_add, key, fwdOrbit_mul_period]

/-- **Cons-preservation of `Balanced` (domain step).** Prepending a fresh domain anchor `a` paired
    with its escaped green image `b = f (fwdOrbit f g a N)` preserves the cycle-balance invariant.
    On `a`'s own cycle both sides gain exactly one fresh point; every other cycle is inert because
    `b` cannot land in a foreign cycle's `f`-image. This is the hard half of the invariant that lets
    the extension-only scheduler carry `Balanced` and discharge escape via `escape_exists'`. -/
theorem balanced_cons_domain {f g : ℕ → ℕ}
    (hf : Function.Injective f) (hg : Function.Injective g)
    {L : List (ℕ × ℕ)} (hbal : Balanced f g L) {a b : ℕ}
    (ha : a ∉ mDom L) (hb : b ∉ mRan L) {N : ℕ} (hbN : b = f (fwdOrbit f g a N)) :
    Balanced f g ((a, b) :: L) := by
  intro c hc
  have hdom : (mDom ((a, b) :: L)).toFinset = insert a (mDom L).toFinset := by
    simp [mDom, List.toFinset_cons]
  have hran : (mRan ((a, b) :: L)).toFinset = insert b (mRan L).toFinset := by
    simp [mRan, List.toFinset_cons]
  have haF : a ∉ (mDom L).toFinset := fun h => ha (List.mem_toFinset.mp h)
  have hbF : b ∉ (mRan L).toFinset := fun h => hb (List.mem_toFinset.mp h)
  rw [hdom, hran]
  by_cases haC : a ∈ orbitCycle f g hc
  · -- `a` is on `c`'s cycle: both intersections gain one fresh point.
    have hfN : fwdOrbit f g a N ∈ orbitCycle f g hc := fwdOrbit_mem_orbitCycle hc haC N
    have hbImg : b ∈ (orbitCycle f g hc).image f := by
      rw [hbN]; exact Finset.mem_image.mpr ⟨fwdOrbit f g a N, hfN, rfl⟩
    rw [Finset.inter_insert_of_mem haC, Finset.inter_insert_of_mem hbImg,
      Finset.card_insert_of_notMem (fun h => haF (Finset.mem_inter.mp h).2),
      Finset.card_insert_of_notMem (fun h => hbF (Finset.mem_inter.mp h).2),
      hbal hc]
  · -- `a` is not on `c`'s cycle: `b` cannot land in `c`'s image, so both sides are inert.
    have hbnImg : b ∉ (orbitCycle f g hc).image f := by
      rw [hbN]
      intro hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨x, hxC, hxeq⟩ := hmem
      have hxN : x = fwdOrbit f g a N := hf hxeq
      rw [hxN] at hxC
      have hoc : OnCycle f g (fwdOrbit f g a N) := onCycle_of_mem_orbitCycle hc hxC
      have hoa : OnCycle f g a := onCycle_of_fwdOrbit hf hg hoc
      exact haC (mem_orbitCycle_of_fwdOrbit_mem hc hoa hxC)
    rw [Finset.inter_insert_of_notMem haC, Finset.inter_insert_of_notMem hbnImg]
    exact hbal hc

/-- **Cons-preservation of `Balanced` (range step), by coordinate-swap duality.** The odd-stage
    range step prepends `(a, b)` with `b` a fresh range anchor and `a = g (fwdOrbit g f b N)` its
    escaped `g`-image (the swapped-problem chase target). It preserves the swapped balance invariant
    `Balanced g f (L.map Prod.swap)` — exactly `balanced_cons_domain` applied to the swapped problem
    `(g, f, L.map Prod.swap)`, mirroring how Section 4l obtains the whole range step for free from
    the domain step (Section 4e duality). The `f∘g` cycles of the swapped dynamics are the reverse
    orbits of the original `g∘f` cycles, so no new orbit algebra is needed. -/
theorem balanced_cons_range {f g : ℕ → ℕ}
    (hf : Function.Injective f) (hg : Function.Injective g)
    {L : List (ℕ × ℕ)} (hbal : Balanced g f (L.map Prod.swap)) {a b : ℕ}
    (ha : a ∉ mDom L) (hb : b ∉ mRan L) {N : ℕ} (haN : a = g (fwdOrbit g f b N)) :
    Balanced g f (((a, b) :: L).map Prod.swap) := by
  simp only [List.map_cons, Prod.swap_prod_mk]
  exact balanced_cons_domain hg hf hbal
    (by rw [mDom_map_swap]; exact hb)
    (by rw [mRan_map_swap]; exact ha)
    haN

/-!
### Section 4i-quinquies: Cross-preservation of `Balanced` — the domain step preserves the
    *swapped* balance too

The extension-only scheduler alternates a domain (even) step and a range (odd) step, and each
step's *escape* obligation is discharged on a different side: the domain step's escape
(`escape_exists'`) needs `Balanced f g L`, while the range step's escape needs the swapped
`Balanced g f (L.map Prod.swap)`. So the scheduler must carry **both** balances at once, and each
atomic move must preserve **both**.

`balanced_cons_domain` already shows a domain cons preserves `Balanced f g L`; the missing
"cross" half is that a domain cons *also* preserves `Balanced g f (L.map Prod.swap)`. Note this is
**not** an instance of `balanced_cons_range`: that lemma needs the placed pair `(a, b)` to satisfy
`a = g (fwdOrbit g f b N')` (an `f∘g`-orbit relation), which holds only when `a`'s orbit is a
*finite* cycle. When `a`'s `g∘f`-orbit is infinite no such `N'` exists, yet the swapped balance is
still preserved (both intersections are inert on every `f∘g`-cycle). `balanced_swap_cons_domain`
covers both cases uniformly, via a single `by_cases` on whether the escaped image `b` lies on the
cycle `c` in question.

The proof rests on two small orbit-algebra facts proved first:
  * `fwdOrbit_swap_apply` — conjugation of the forward orbit by the head map: running the *swapped*
    dynamics from `f x` equals `f ∘ (running the original dynamics from x)`. This is what lets the
    escaped image `b = f (fwdOrbit f g a N)` be relocated onto the swapped `f∘g`-orbit.
  * `onCycle_of_onCycle_apply` — if `f x` is `f∘g`-periodic then `x` is `g∘f`-periodic (cancel the
    shared injective `f`). This transports periodicity of `b` back to periodicity of `a`.
-/

/-- **Conjugation of the forward orbit.** Running the swapped dynamics `g, f` from the point `f x`
    is the `f`-image of running the original dynamics `f, g` from `x`:
    `fwdOrbit g f (f x) j = f (fwdOrbit f g x j)`. (The `g∘f` and `f∘g` iterations are conjugate by
    `f`.) The engine that moves the escaped green image between the two dynamics. -/
theorem fwdOrbit_swap_apply (f g : ℕ → ℕ) (x j : ℕ) :
    fwdOrbit g f (f x) j = f (fwdOrbit f g x j) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [fwdOrbit, ih]

/-- **Periodicity transports across `f`.** If `f x` is `f∘g`-periodic (`OnCycle g f (f x)`) then `x`
    is `g∘f`-periodic (`OnCycle f g x`): the same positive period works after cancelling the shared
    injective `f`. -/
theorem onCycle_of_onCycle_apply {f g : ℕ → ℕ} (hf : Function.Injective f)
    {x : ℕ} (h : OnCycle g f (f x)) : OnCycle f g x := by
  obtain ⟨m, hm, hmeq⟩ := h
  refine ⟨m, hm, ?_⟩
  rw [fwdOrbit_swap_apply] at hmeq
  exact hf hmeq

/-- **Cross-preservation of `Balanced` (domain step preserves the swapped balance).** A domain cons
    that prepends `(a, b)` with fresh domain anchor `a` and escaped green image
    `b = f (fwdOrbit f g a N)` preserves the *swapped* cycle-balance `Balanced g f (L.map Prod.swap)`
    — the invariant the odd-stage range escape (`escape_exists'` on the swapped problem) consumes.

    Together with `balanced_cons_domain` (which preserves `Balanced f g L`) this discharges the
    scheduler's obligation to carry both balances across a domain step; the range step is handled by
    the coordinate-swap dual. On the `f∘g`-cycle `C` through any anchor `c`: if the escaped image
    `b ∈ C` then `a` lands in `C.image g` (both sides gain one point); if `b ∉ C` then `a ∉ C.image g`
    (both sides inert). The dichotomy is uniform — no separate periodic/infinite split at the top
    level — because the "`a ∈ C.image g`" side is controlled entirely by whether `b ∈ C`. -/
theorem balanced_swap_cons_domain {f g : ℕ → ℕ}
    (hf : Function.Injective f) (hg : Function.Injective g)
    {L : List (ℕ × ℕ)} (hbal : Balanced g f (L.map Prod.swap)) {a b : ℕ}
    (ha : a ∉ mDom L) (hb : b ∉ mRan L) {N : ℕ} (hbN : b = f (fwdOrbit f g a N)) :
    Balanced g f (((a, b) :: L).map Prod.swap) := by
  simp only [List.map_cons, Prod.swap_prod_mk]
  intro c hc
  have hdom : (mDom ((b, a) :: L.map Prod.swap)).toFinset = insert b (mRan L).toFinset := by
    rw [mDom_cons, List.toFinset_cons, mDom_map_swap]
  have hran : (mRan ((b, a) :: L.map Prod.swap)).toFinset = insert a (mDom L).toFinset := by
    rw [mRan_cons, List.toFinset_cons, mRan_map_swap]
  rw [hdom, hran]
  have hbF : b ∉ (mRan L).toFinset := fun h => hb (List.mem_toFinset.mp h)
  have haF : a ∉ (mDom L).toFinset := fun h => ha (List.mem_toFinset.mp h)
  have hbalc := hbal hc
  rw [mDom_map_swap, mRan_map_swap] at hbalc
  by_cases hbC : b ∈ orbitCycle g f hc
  · -- `b` on `c`'s `f∘g`-cycle ⟹ `a ∈ (cycle).image g`; both sides gain one fresh point.
    have haImg : a ∈ (orbitCycle g f hc).image g := by
      -- `b` periodic ⟹ `f (fwdOrbit f g a N)` periodic ⟹ `a` is `g∘f`-periodic.
      have hocb : OnCycle g f b := onCycle_of_mem_orbitCycle hc hbC
      rw [hbN] at hocb
      have hoc_oN : OnCycle f g (fwdOrbit f g a N) := onCycle_of_onCycle_apply hf hocb
      have hoa : OnCycle f g a := onCycle_of_fwdOrbit hf hg hoc_oN
      have hmpos : 1 ≤ orbitPeriod f g hoa := orbitPeriod_pos hoa
      refine Finset.mem_image.mpr
        ⟨fwdOrbit g f b (orbitPeriod f g hoa * (N + 2) - (N + 1)), ?_, ?_⟩
      · exact fwdOrbit_mem_orbitCycle hc hbC _
      · -- `g (fwdOrbit g f b j) = fwdOrbit f g a (N + j + 1) = a` for the chosen `j`.
        rw [hbN, fwdOrbit_swap_apply,
          ← fwdOrbit_succ f g (fwdOrbit f g a N) (orbitPeriod f g hoa * (N + 2) - (N + 1)),
          ← fwdOrbit_add f g a (orbitPeriod f g hoa * (N + 2) - (N + 1) + 1) N]
        have hge : N + 1 ≤ orbitPeriod f g hoa * (N + 2) := by nlinarith [hmpos]
        have harith :
            orbitPeriod f g hoa * (N + 2) - (N + 1) + 1 + N = orbitPeriod f g hoa * (N + 2) := by
          omega
        rw [harith, fwdOrbit_mul_period hoa (N + 2)]
    rw [Finset.inter_insert_of_mem hbC, Finset.inter_insert_of_mem haImg,
      Finset.card_insert_of_notMem (fun h => hbF (Finset.mem_inter.mp h).2),
      Finset.card_insert_of_notMem (fun h => haF (Finset.mem_inter.mp h).2),
      hbalc]
  · -- `b` off `c`'s cycle ⟹ `a ∉ (cycle).image g`; both intersections are inert.
    have hanImg : a ∉ (orbitCycle g f hc).image g := by
      intro hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨y, hyC, hya⟩ := hmem
      -- if `a = g y` with `y` on the cycle then `b = fwdOrbit g f y (N+1)` is on it too.
      apply hbC
      have hby : b = fwdOrbit g f y (N + 1) := by
        have hconj : fwdOrbit f g (g y) N = g (fwdOrbit g f y N) := fwdOrbit_swap_apply g f y N
        rw [hbN, ← hya, hconj]
        simp only [fwdOrbit]
      rw [hby]
      exact fwdOrbit_mem_orbitCycle hc hyC (N + 1)
    rw [Finset.inter_insert_of_notMem hbC, Finset.inter_insert_of_notMem hanImg]
    exact hbalc

/-- **Cross-preservation of `Balanced` (range step preserves the *un-swapped* balance).** The dual
    of `balanced_swap_cons_domain`: a range cons that prepends `(a, b)` with fresh range anchor `b`
    and escaped `g`-image `a = g (fwdOrbit g f b N)` preserves the un-swapped cycle-balance
    `Balanced f g L` — the invariant the even-stage domain escape (`escape_exists'`) consumes.

    Obtained for free from `balanced_swap_cons_domain` on the coordinate-swapped problem
    `(g, f, L.map Prod.swap)`, exactly as `balanced_cons_range` is obtained from
    `balanced_cons_domain` (Section 4e duality). Together with `balanced_cons_range` (which
    preserves the *swapped* `Balanced g f (L.map Prod.swap)`) this discharges the scheduler's
    obligation to carry **both** balances across a range step — completing the 2×2 matrix of
    (domain step | range step) × (un-swapped balance | swapped balance) preservation lemmas that
    the extension-only back-and-forth scheduler of `myhill_isomorphism` maintains at every stage. -/
theorem balanced_swap_cons_range {f g : ℕ → ℕ}
    (hf : Function.Injective f) (hg : Function.Injective g)
    {L : List (ℕ × ℕ)} (hbal : Balanced f g L) {a b : ℕ}
    (ha : a ∉ mDom L) (hb : b ∉ mRan L) {N : ℕ} (haN : a = g (fwdOrbit g f b N)) :
    Balanced f g ((a, b) :: L) := by
  -- Exact `f ↔ g` mirror of `balanced_swap_cons_domain`: here the placed pair is `(a, b)` with
  -- fresh range anchor `b` and escaped `g`-image `a = g (fwdOrbit g f b N)`, and the invariant kept
  -- is the un-swapped `Balanced f g`. On the `g∘f`-cycle `C` through `c`: if `a ∈ C` then `b` lands
  -- in `C.image f` (both sides gain a point); if `a ∉ C` then `b ∉ C.image f` (both inert).
  intro c hc
  have hdom : (mDom ((a, b) :: L)).toFinset = insert a (mDom L).toFinset := by
    rw [mDom_cons, List.toFinset_cons]
  have hran : (mRan ((a, b) :: L)).toFinset = insert b (mRan L).toFinset := by
    rw [mRan_cons, List.toFinset_cons]
  rw [hdom, hran]
  have haF : a ∉ (mDom L).toFinset := fun h => ha (List.mem_toFinset.mp h)
  have hbF : b ∉ (mRan L).toFinset := fun h => hb (List.mem_toFinset.mp h)
  have hbalc := hbal hc
  by_cases haC : a ∈ orbitCycle f g hc
  · -- `a` on `c`'s `g∘f`-cycle ⟹ `b ∈ (cycle).image f`; both sides gain one fresh point.
    have hbImg : b ∈ (orbitCycle f g hc).image f := by
      -- `a` periodic ⟹ `g (fwdOrbit g f b N)` periodic ⟹ `b` is `f∘g`-periodic.
      have hoca : OnCycle f g a := onCycle_of_mem_orbitCycle hc haC
      rw [haN] at hoca
      have hoc_oN : OnCycle g f (fwdOrbit g f b N) := onCycle_of_onCycle_apply hg hoca
      have hob : OnCycle g f b := onCycle_of_fwdOrbit hg hf hoc_oN
      have hmpos : 1 ≤ orbitPeriod g f hob := orbitPeriod_pos hob
      refine Finset.mem_image.mpr
        ⟨fwdOrbit f g a (orbitPeriod g f hob * (N + 2) - (N + 1)), ?_, ?_⟩
      · exact fwdOrbit_mem_orbitCycle hc haC _
      · -- `f (fwdOrbit f g a j) = fwdOrbit g f b (N + j + 1) = b` for the chosen `j`.
        rw [haN, fwdOrbit_swap_apply,
          ← fwdOrbit_succ g f (fwdOrbit g f b N) (orbitPeriod g f hob * (N + 2) - (N + 1)),
          ← fwdOrbit_add g f b (orbitPeriod g f hob * (N + 2) - (N + 1) + 1) N]
        have hge : N + 1 ≤ orbitPeriod g f hob * (N + 2) := by nlinarith [hmpos]
        have harith :
            orbitPeriod g f hob * (N + 2) - (N + 1) + 1 + N = orbitPeriod g f hob * (N + 2) := by
          omega
        rw [harith, fwdOrbit_mul_period hob (N + 2)]
    rw [Finset.inter_insert_of_mem haC, Finset.inter_insert_of_mem hbImg,
      Finset.card_insert_of_notMem (fun h => haF (Finset.mem_inter.mp h).2),
      Finset.card_insert_of_notMem (fun h => hbF (Finset.mem_inter.mp h).2),
      hbalc]
  · -- `a` off `c`'s cycle ⟹ `b ∉ (cycle).image f`; both intersections are inert.
    have hbnImg : b ∉ (orbitCycle f g hc).image f := by
      intro hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨y, hyC, hyb⟩ := hmem
      -- if `b = f y` with `y` on the cycle then `a = fwdOrbit f g y (N+1)` is on it too.
      apply haC
      have hay : a = fwdOrbit f g y (N + 1) := by
        have hconj : fwdOrbit g f (f y) N = f (fwdOrbit f g y N) := fwdOrbit_swap_apply f g y N
        rw [haN, ← hyb, hconj]
        simp only [fwdOrbit]
      rw [hay]
      exact fwdOrbit_mem_orbitCycle hc hyC (N + 1)
    rw [Finset.inter_insert_of_notMem haC, Finset.inter_insert_of_notMem hbnImg]
    exact hbalc

/-- **Escape existence (bounded).** For a fresh domain anchor `a ∉ mDom L` in a matching `L`
    satisfying the construction invariant, some forward-orbit stage `N ≤ (mDom L).length` has a
    green image `f (fwdOrbit f g a N)` that is *fresh* in the range. Equivalently the collision
    chase `chaseTarget f g a 0, 1, 2, …` cannot stay inside `mRan L` forever; it escapes within
    `L.length` steps, so the domain step's search is a genuine bounded (hence computable) loop.

    This is the termination certificate the priority scheduler's even stage rests on, and the
    missing ingredient that turns `matching_step_chase` into a *total* domain step
    (`domain_step_exists`). Proof: were every stage `N ≤ (mDom L).length` a collision, the
    `g`-edge chain (`chase_gedge_chain`) would put all of `fwdOrbit f g a 1, …,
    (mDom L).length + 1` into `mDom L`, and `fwdOrbit_chase_length_le` would then bound
    `(mDom L).length + 1 ≤ (mDom L).length` — impossible. -/
theorem escape_exists {f g : ℕ → ℕ} (hf : Function.Injective f) (hg : Function.Injective g)
    {L : List (ℕ × ℕ)} (hL : IsMatching L) (hB : BuiltFrom f g L) {a : ℕ} (ha : a ∉ mDom L) :
    ∃ N, N ≤ (mDom L).length ∧ f (fwdOrbit f g a N) ∉ mRan L := by
  by_contra hcon
  push_neg at hcon
  have hcoll : ∀ j, j < (mDom L).length + 1 → f (fwdOrbit f g a j) ∈ mRan L := by
    intro j hj; exact hcon j (by omega)
  have hdom : ∀ i, 1 ≤ i → i ≤ (mDom L).length + 1 → fwdOrbit f g a i ∈ mDom L := by
    intro i hi1 hiM
    have hpair := chase_gedge_chain hf hg hL hB ha hcoll ((mDom L).length + 1) (le_refl _) i hi1 hiM
    exact List.mem_map.mpr ⟨(fwdOrbit f g a i, f (fwdOrbit f g a (i - 1))), hpair, rfl⟩
  have hlen : (mDom L).length + 1 ≤ (mDom L).length :=
    fwdOrbit_chase_length_le hf hg (D := mDom L) ha hdom
  omega

/-- **The even-stage domain step is total.** Any fresh domain anchor `a ∉ mDom L` can be placed:
    there is a partner `b` (the escaped chase target `chaseTarget f g a N` of `escape_exists`)
    such that prepending `(a, b)` keeps `L` a matching *and* preserves the correspondence
    `p ↔ q`. This combines the bounded collision chase (`escape_exists`) with the correspondence
    invariant (`matching_step_chase`), discharging the "each even stage terminates and extends"
    obligation of the `myhill_isomorphism` priority construction.

    Note this places `a` while preserving `IsMatching` and `MatchingCorr`, the two invariants
    `matching_step_chase` maintains. It does **not** by itself preserve `BuiltFrom` (the added
    pair `(a, f (fwdOrbit f g a N))` is in general neither an `f`-edge nor a `g`-edge when
    `N > 0`); iterating the scheduler while keeping the invariant that feeds `collision_f_source`
    requires the augmenting-path variant that re-labels the chased `g`-edges `(oₖ, f oₖ₋₁)` as
    `f`-edges `(oₖ, f oₖ)` — see the knowledge base. That list surgery is the remaining piece of
    the full construction; the termination heart of it is exactly `escape_exists` above. -/
theorem domain_step_exists {p q : ℕ → Prop} {f g : ℕ → ℕ}
    (hfpq : ∀ n, p n ↔ q (f n)) (hgpq : ∀ n, q n ↔ p (g n))
    (hf : Function.Injective f) (hg : Function.Injective g)
    {L : List (ℕ × ℕ)} (hL : IsMatching L) (hC : MatchingCorr p q L) (hB : BuiltFrom f g L)
    {a : ℕ} (ha : a ∉ mDom L) :
    ∃ b, IsMatching ((a, b) :: L) ∧ MatchingCorr p q ((a, b) :: L) := by
  obtain ⟨N, _, hN⟩ := escape_exists hf hg hL hB ha
  exact ⟨chaseTarget f g a N, matching_step_chase hfpq hgpq hL hC ha hN⟩

/-!
## Section 4j: The augmenting path — a `BuiltFrom`-preserving domain step

`domain_step_exists` places a fresh anchor `a` at the escaped chase target
`chaseTarget f g a N = f (fwdOrbit f g a N)`, preserving `IsMatching` and
`MatchingCorr` — but **not** `BuiltFrom`: for `N > 0` the pair
`(a, f (fwdOrbit f g a N))` is neither an `f`-edge `(x, f x)` nor a `g`-edge
`(g y, y)`, so the collision analysis (`collision_f_source`, `escape_exists`) that
the *next* stage rests on would no longer apply. The fix is the classical
back-and-forth **augmenting path**: rather than record the single anchor pair, the
scheduler re-labels the whole chased chain into `f`-edges.

Concretely, writing `oₖ = fwdOrbit f g a k`, the chase from a fresh anchor `a = o₀`
walks `o₀, o₁, …, o_N`, where each `oₖ` (`1 ≤ k ≤ N`) is currently occupied by the
stale `g`-edge `(oₖ, f o_{k-1})` and `f o_N` is the escaped (fresh) range point.
The augmenting path replaces those `N` `g`-edges with the `N+1` `f`-edges
`(oₖ, f oₖ)` for `k = 0, …, N`. Every replacement pair is an `f`-edge, so the
result satisfies `BuiltFrom`; the anchor `a = o₀` gains a partner; and only the
fresh range point `f o_N` is newly occupied.

This section builds the augmenting-path block `augPath f g a N` and establishes its
three structural invariants (`BuiltFrom`, `MatchingCorr`, `IsMatching`) in isolation.
Splicing the block into the existing matching (deleting the re-labelled `g`-edges) is
the remaining list-surgery step; the block itself — the object prior sessions never
constructed — is provided here.
-/

/-- **The augmenting path** for a fresh anchor `a` whose collision chase escapes at
    forward-orbit depth `N`: the list of `f`-edges `(oₖ, f oₖ)` for `k = 0, …, N`, where
    `oₖ = fwdOrbit f g a k`. Stage `0` is the anchor edge `(a, f a)`; each later stage
    re-labels the stale `g`-edge `(oₖ, f o_{k-1})` as the `f`-edge `(oₖ, f oₖ)`. -/
def augPath (f g : ℕ → ℕ) (a N : ℕ) : List (ℕ × ℕ) :=
  (List.range (N + 1)).map (fun k => (fwdOrbit f g a k, f (fwdOrbit f g a k)))

/-- Membership in the augmenting path: its pairs are exactly `(oₖ, f oₖ)` for `k ≤ N`. -/
theorem mem_augPath_iff {f g : ℕ → ℕ} {a N : ℕ} {ab : ℕ × ℕ} :
    ab ∈ augPath f g a N ↔ ∃ k ≤ N, ab = (fwdOrbit f g a k, f (fwdOrbit f g a k)) := by
  simp only [augPath, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, hkab⟩
    exact ⟨k, Nat.lt_succ_iff.mp hk, hkab.symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, Nat.lt_succ_iff.mpr hk, rfl⟩

/-- The domain of the augmenting path is the forward-orbit prefix `o₀, …, o_N`. -/
theorem mDom_augPath (f g : ℕ → ℕ) (a N : ℕ) :
    mDom (augPath f g a N) = (List.range (N + 1)).map (fwdOrbit f g a) := by
  simp only [mDom, augPath, List.map_map, Function.comp_def]

/-- The range of the augmenting path is `f o₀, …, f o_N`. -/
theorem mRan_augPath (f g : ℕ → ℕ) (a N : ℕ) :
    mRan (augPath f g a N) = (List.range (N + 1)).map (fun k => f (fwdOrbit f g a k)) := by
  simp only [mRan, augPath, List.map_map, Function.comp_def]

/-- **The augmenting path satisfies `BuiltFrom`.** Every pair `(oₖ, f oₖ)` is an `f`-edge,
    so the whole block preserves the construction invariant — this is the point of the
    re-labelling that `domain_step_exists` alone cannot achieve. -/
theorem augPath_builtFrom (f g : ℕ → ℕ) (a N : ℕ) : BuiltFrom f g (augPath f g a N) := by
  intro ab hmem
  rw [mem_augPath_iff] at hmem
  obtain ⟨k, _, rfl⟩ := hmem
  exact Or.inl rfl

/-- **The augmenting path respects the correspondence.** Each `f`-edge `(oₖ, f oₖ)`
    corresponds directly by the `f`-reduction `p oₖ ↔ q (f oₖ)` — no appeal to the anchor
    or to the non-computable `isGFree` is needed. -/
theorem augPath_matchingCorr {p q : ℕ → Prop} {f g : ℕ → ℕ} (hfpq : ∀ n, p n ↔ q (f n))
    (a N : ℕ) : MatchingCorr p q (augPath f g a N) := by
  intro ab hmem
  rw [mem_augPath_iff] at hmem
  obtain ⟨k, _, rfl⟩ := hmem
  exact hfpq (fwdOrbit f g a k)

/-- **The augmenting path is a matching**, provided the forward-orbit prefix
    `o₀, …, o_N` is injective (distinct points). Both `Nodup` sides follow: the domain is
    the orbit prefix itself, and the range is its image under the injective `f`. -/
theorem augPath_isMatching {f g : ℕ → ℕ} (hf : Function.Injective f) {a N : ℕ}
    (hdist : ∀ ⦃i⦄, i ≤ N → ∀ ⦃j⦄, j ≤ N →
      fwdOrbit f g a i = fwdOrbit f g a j → i = j) :
    IsMatching (augPath f g a N) := by
  refine ⟨?_, ?_⟩
  · rw [mDom_augPath]
    refine List.nodup_range.map_on ?_
    intro i hi j hj hij
    rw [List.mem_range] at hi hj
    exact hdist (Nat.lt_succ_iff.mp hi) (Nat.lt_succ_iff.mp hj) hij
  · rw [mRan_augPath]
    refine List.nodup_range.map_on ?_
    intro i hi j hj hij
    rw [List.mem_range] at hi hj
    exact hdist (Nat.lt_succ_iff.mp hi) (Nat.lt_succ_iff.mp hj) (hf hij)

/-- **The augmenting path is a matching, in the scheduler's collision context.** When the
    anchor `a` is fresh (`a ∉ mDom L`) and every chased orbit point `oₖ` (`1 ≤ k ≤ N`) is
    already occupied (`oₖ ∈ mDom L`) — exactly the situation the collision chase produces —
    the orbit prefix is automatically distinct (`fwdOrbit_prefix_distinct`), so the
    augmenting path built for that anchor is a valid matching. This is the form
    `augPath_isMatching` takes when invoked by the priority scheduler. -/
theorem augPath_isMatching_of_chase {f g : ℕ → ℕ} (hf : Function.Injective f)
    (hg : Function.Injective g) {L : List (ℕ × ℕ)} {a N : ℕ} (ha : a ∉ mDom L)
    (hchase : ∀ k, 1 ≤ k → k ≤ N → fwdOrbit f g a k ∈ mDom L) :
    IsMatching (augPath f g a N) :=
  augPath_isMatching hf (fwdOrbit_prefix_distinct hf hg (D := fun n => n ∈ mDom L) ha hchase)

/-!
## Section 4k: Splicing the augmenting path — the `BuiltFrom`-preserving domain step

Sections 4i/4j supplied the two halves of the even-stage domain step: `escape_exists`
(the collision chase terminates at a range-fresh target) and `augPath`/`augPath_*` (the
re-labelled `f`-edge block that restores `BuiltFrom`). What remained — named across several
prior sessions as the genuine outstanding list-surgery — is to *splice* that block into the
current matching, deleting the stale `g`-edges it re-labels, and verify the result is again a
`BuiltFrom` matching respecting the correspondence.

`augment_domain_step` does exactly that. Given a fresh anchor `a ∉ mDom L`, let `N` be the
*minimal* escape depth (`Nat.find` on `f (fwdOrbit f g a N) ∉ mRan L`), so every earlier stage
collides: `f (fwdOrbit f g a j) ∈ mRan L` for `j < N`. By `chase_gedge_chain` the matching then
contains the `N` stale `g`-edges `(oₖ, f oₖ₋₁)` (`1 ≤ k ≤ N`, `oₖ = fwdOrbit f g a k`). Splicing
`augPath f g a N` — the `f`-edges `(oₖ, f oₖ)` for `0 ≤ k ≤ N` — in place of those `g`-edges
yields `L' := augPath f g a N ++ keptL`, where `keptL` drops exactly the pairs whose domain
point lies on the re-labelled orbit prefix. The result:

* **is a matching** — domains: `mDom (augPath …)` is the distinct orbit prefix, and `keptL`'s
  domains are, by the filter, disjoint from it; ranges: `augPath`'s range values `f oₖ` for
  `k < N` are the *removed* `g`-edges' range values (unique by co-functionality), while `f o_N`
  is the escaped fresh point, so they avoid `mRan keptL`;
* **respects the correspondence** — `augPath` does (each `f`-edge via `hfpq`), `keptL ⊆ L` does;
* **preserves `BuiltFrom`** — `augPath` is all `f`-edges, `keptL ⊆ L`;
* **covers the anchor** `a = o₀ ∈ mDom L'` and is **monotone** on both sides
  (`mDom L ⊆ mDom L'`, `mRan L ⊆ mRan L'`): the removed `g`-edges' endpoints are all re-added by
  the augmenting path.

This is the total, invariant-preserving even-stage move the priority scheduler iterates; the
odd (range) stage is its `Prod.swap` dual (Section 4e). Only the outer stage recursion +
coverage read-off of `myhill_isomorphism` remains after this.
-/

/-- **The augmenting-path domain step.** For a fresh domain anchor `a ∉ mDom L` in a matching
    `L` satisfying `BuiltFrom` and the correspondence, there is an extended matching `L'` that
    still satisfies all three invariants, *covers* `a` (`a ∈ mDom L'`), and is monotone on both
    domain and range (`mDom L ⊆ mDom L'`, `mRan L ⊆ mRan L'`). `L'` is obtained by splicing the
    augmenting path `augPath f g a N` (for the minimal escape depth `N`) in place of the stale
    `g`-edges it re-labels. Unlike `domain_step_exists`, this preserves `BuiltFrom`, so the next
    stage's collision analysis (`collision_f_source`, `escape_exists`) still applies — making it
    the move the scheduler can actually iterate. -/
theorem augment_domain_step {p q : ℕ → Prop} {f g : ℕ → ℕ}
    (hfpq : ∀ n, p n ↔ q (f n))
    (hf : Function.Injective f) (hg : Function.Injective g)
    {L : List (ℕ × ℕ)} (hL : IsMatching L) (hC : MatchingCorr p q L) (hB : BuiltFrom f g L)
    {a : ℕ} (ha : a ∉ mDom L) :
    ∃ L', IsMatching L' ∧ MatchingCorr p q L' ∧ BuiltFrom f g L' ∧
      a ∈ mDom L' ∧ (∀ x ∈ mDom L, x ∈ mDom L') ∧ (∀ y ∈ mRan L, y ∈ mRan L') ∧
      (∀ ab ∈ L, ab.2 = f ab.1 → ab ∈ L') := by
  -- Elementwise membership descriptions of `mDom`/`mRan` and their append behaviour.
  have mem_mDom : ∀ (l : List (ℕ × ℕ)) (x : ℕ), x ∈ mDom l ↔ ∃ ab, ab ∈ l ∧ ab.1 = x := by
    intro l x; simp only [mDom, List.mem_map]
  have mem_mRan : ∀ (l : List (ℕ × ℕ)) (y : ℕ), y ∈ mRan l ↔ ∃ ab, ab ∈ l ∧ ab.2 = y := by
    intro l y; simp only [mRan, List.mem_map]
  have mDom_append : ∀ (l₁ l₂ : List (ℕ × ℕ)), mDom (l₁ ++ l₂) = mDom l₁ ++ mDom l₂ := by
    intro l₁ l₂; simp only [mDom, List.map_append]
  have mRan_append : ∀ (l₁ l₂ : List (ℕ × ℕ)), mRan (l₁ ++ l₂) = mRan l₁ ++ mRan l₂ := by
    intro l₁ l₂; simp only [mRan, List.map_append]
  -- Minimal escape depth: first orbit stage whose green image is range-fresh; all earlier
  -- stages collide.
  obtain ⟨N, hN, hcoll⟩ :
      ∃ N, f (fwdOrbit f g a N) ∉ mRan L ∧ ∀ j, j < N → f (fwdOrbit f g a j) ∈ mRan L := by
    have hEsc : ∃ M, f (fwdOrbit f g a M) ∉ mRan L := by
      obtain ⟨M, _, hM⟩ := escape_exists hf hg hL hB ha; exact ⟨M, hM⟩
    refine ⟨Nat.find hEsc, Nat.find_spec hEsc, ?_⟩
    intro j hj
    exact not_not.mp (Nat.find_min hEsc hj)
  -- The stale `g`-edges the chase runs over, and hence each chased orbit point is occupied.
  have hgedges : ∀ m, 1 ≤ m → m ≤ N →
      (fwdOrbit f g a m, f (fwdOrbit f g a (m - 1))) ∈ L :=
    fun m hm1 hmN => chase_gedge_chain hf hg hL hB ha hcoll N (le_refl N) m hm1 hmN
  have hchase : ∀ k, 1 ≤ k → k ≤ N → fwdOrbit f g a k ∈ mDom L := by
    intro k hk1 hkN
    exact (mem_mDom L _).mpr ⟨_, hgedges k hk1 hkN, rfl⟩
  -- Membership descriptions of the augmenting path's domain and range.
  have hDomA : ∀ x, x ∈ mDom (augPath f g a N) ↔ ∃ k, k ≤ N ∧ x = fwdOrbit f g a k := by
    intro x
    rw [mDom_augPath, List.mem_map]
    constructor
    · rintro ⟨k, hk, rfl⟩; exact ⟨k, Nat.lt_succ_iff.mp (List.mem_range.mp hk), rfl⟩
    · rintro ⟨k, hk, rfl⟩; exact ⟨k, List.mem_range.mpr (Nat.lt_succ_iff.mpr hk), rfl⟩
  have hRanA : ∀ y, y ∈ mRan (augPath f g a N) ↔ ∃ k, k ≤ N ∧ y = f (fwdOrbit f g a k) := by
    intro y
    rw [mRan_augPath, List.mem_map]
    constructor
    · rintro ⟨k, hk, rfl⟩; exact ⟨k, Nat.lt_succ_iff.mp (List.mem_range.mp hk), rfl⟩
    · rintro ⟨k, hk, rfl⟩; exact ⟨k, List.mem_range.mpr (Nat.lt_succ_iff.mpr hk), rfl⟩
  -- The kept part of `L`: pairs whose domain point is not re-labelled by the aug path.
  set keptL := L.filter (fun ab => decide (ab.1 ∉ mDom (augPath f g a N))) with hkeptL
  have hmemKept : ∀ ab, ab ∈ keptL ↔ ab ∈ L ∧ ab.1 ∉ mDom (augPath f g a N) := by
    intro ab
    simp only [hkeptL, List.mem_filter, decide_eq_true_eq]
  have hApathM : IsMatching (augPath f g a N) := augPath_isMatching_of_chase hf hg ha hchase
  have hkeptSub : List.Sublist keptL L := by rw [hkeptL]; exact List.filter_sublist
  have hDomKeptNodup : (mDom keptL).Nodup := by
    have hs : List.Sublist (mDom keptL) (mDom L) := hkeptSub.map Prod.fst
    exact hL.1.sublist hs
  have hRanKeptNodup : (mRan keptL).Nodup := by
    have hs : List.Sublist (mRan keptL) (mRan L) := hkeptSub.map Prod.snd
    exact hL.2.sublist hs
  refine ⟨augPath f g a N ++ keptL, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- IsMatching
    refine ⟨?_, ?_⟩
    · -- domain side
      rw [mDom_append, List.nodup_append]
      refine ⟨hApathM.1, hDomKeptNodup, ?_⟩
      intro x hxA x' hx'K hne
      obtain ⟨ab, habK, hab1⟩ := (mem_mDom keptL x').mp hx'K
      apply ((hmemKept ab).mp habK).2
      rw [hab1, ← hne]
      exact hxA
    · -- range side
      rw [mRan_append, List.nodup_append]
      refine ⟨hApathM.2, hRanKeptNodup, ?_⟩
      intro y hyA y' hy'K hne
      obtain ⟨k, hkN, hyk⟩ := (hRanA y).mp hyA
      obtain ⟨⟨u, w⟩, habK, hab2⟩ := (mem_mRan keptL y').mp hy'K
      have hwy : w = y' := hab2
      have habL : (u, w) ∈ L := ((hmemKept (u, w)).mp habK).1
      have habD : u ∉ mDom (augPath f g a N) := ((hmemKept (u, w)).mp habK).2
      have hwfok : w = f (fwdOrbit f g a k) := by rw [hwy, ← hne, hyk]
      rcases Nat.lt_or_ge k N with hklt | hkge
      · -- k < N: the removed `g`-edge (o_{k+1}, f o_k) shares the range value `f o_k` with
        -- (u, w); co-functionality forces u = o_{k+1} ∈ mDom (augPath), contradiction.
        have hgedge := hgedges (k + 1) (by omega) (by omega)
        rw [show (k + 1) - 1 = k from by omega] at hgedge
        have hval : (u, f (fwdOrbit f g a k)) ∈ L := by rw [← hwfok]; exact habL
        have hueq : u = fwdOrbit f g a (k + 1) := matching_cofunctional hL hval hgedge
        exact habD ((hDomA u).mpr ⟨k + 1, by omega, hueq⟩)
      · -- k = N: `w = f o_N ∉ mRan L`, contradicting (u, w) ∈ L.
        have hkeqN : k = N := by omega
        refine hN ((mem_mRan L (f (fwdOrbit f g a N))).mpr ⟨(u, w), habL, ?_⟩)
        rw [hkeqN] at hwfok
        exact hwfok
  · -- MatchingCorr
    intro ab hab
    rw [List.mem_append] at hab
    rcases hab with hA | hK
    · exact augPath_matchingCorr hfpq a N ab hA
    · exact hC ab ((hmemKept ab).mp hK).1
  · -- BuiltFrom
    intro ab hab
    rw [List.mem_append] at hab
    rcases hab with hA | hK
    · exact augPath_builtFrom f g a N ab hA
    · exact hB ab ((hmemKept ab).mp hK).1
  · -- a ∈ mDom L'
    rw [mDom_append, List.mem_append]
    exact Or.inl ((hDomA a).mpr ⟨0, Nat.zero_le N, rfl⟩)
  · -- domain monotone
    intro x hx
    rw [mDom_append, List.mem_append]
    by_cases hxA : x ∈ mDom (augPath f g a N)
    · exact Or.inl hxA
    · right
      obtain ⟨ab, habL, hab1⟩ := (mem_mDom L x).mp hx
      refine (mem_mDom keptL x).mpr ⟨ab, ?_, hab1⟩
      exact (hmemKept ab).mpr ⟨habL, by rw [hab1]; exact hxA⟩
  · -- range monotone
    intro y hy
    rw [mRan_append, List.mem_append]
    obtain ⟨⟨u, w⟩, habL, hab2⟩ := (mem_mRan L y).mp hy
    have hwy : w = y := hab2
    by_cases hu : u ∈ mDom (augPath f g a N)
    · -- u = o_k on the orbit prefix; k ≥ 1 (else u = a ∈ mDom L), and functionality gives
      -- w = f o_{k-1} ∈ mRan (augPath).
      obtain ⟨k, hkN, hk⟩ := (hDomA u).mp hu
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · have hua : u = a := by rw [hk0] at hk; exact hk
        exact absurd ((mem_mDom L a).mpr ⟨(u, w), habL, hua⟩) ha
      · left
        have hgedge : (fwdOrbit f g a k, f (fwdOrbit f g a (k - 1))) ∈ L :=
          hgedges k hkpos hkN
        have hgedge' : (u, f (fwdOrbit f g a (k - 1))) ∈ L := by rw [hk]; exact hgedge
        have hval : w = f (fwdOrbit f g a (k - 1)) := matching_functional hL habL hgedge'
        rw [← hwy, hval]
        exact (hRanA (f (fwdOrbit f g a (k - 1)))).mpr ⟨k - 1, by omega, rfl⟩
    · right
      exact (mem_mRan keptL y).mpr ⟨(u, w), (hmemKept (u, w)).mpr ⟨habL, hu⟩, hwy⟩
  · -- f-edge preservation: an existing `f`-edge `(x, f x)` of `L` survives the splice.
    -- Only stale `g`-edges on the orbit prefix `{o₁,…,o_N}` are removed (`keptL` filter),
    -- and an `f`-edge domain point cannot lie on that prefix without forcing an orbit
    -- repeat: if `x = oₖ` then the stale `g`-edge `(oₖ, f o_{k-1}) ∈ L` and functionality
    -- give `f x = f o_{k-1}`, so `f oₖ = f o_{k-1}`, hence (`f` injective) `oₖ = o_{k-1}`,
    -- contradicting prefix distinctness. So `x ∉ mDom (augPath …)` and `(x, f x) ∈ keptL`.
    rintro ⟨x, y⟩ hxyL hyfx
    have hxdom : x ∈ mDom L := (mem_mDom L x).mpr ⟨(x, y), hxyL, rfl⟩
    rw [List.mem_append]
    right
    refine (hmemKept (x, y)).mpr ⟨hxyL, ?_⟩
    intro hxA
    obtain ⟨k, hkN, hxk⟩ := (hDomA x).mp hxA
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · -- k = 0 ⇒ x = a, contradicting freshness `a ∉ mDom L`.
      rw [hk0] at hxk
      have hxa : x = a := hxk
      exact ha (hxa ▸ hxdom)
    · -- k ≥ 1 ⇒ orbit repeat, impossible.
      have hgedge := hgedges k hkpos hkN
      have hval : (fwdOrbit f g a k, y) ∈ L := hxk ▸ hxyL
      have hyeq : y = f (fwdOrbit f g a (k - 1)) := matching_functional hL hval hgedge
      have hyfok : y = f (fwdOrbit f g a k) := by rw [← hxk]; exact hyfx
      have hokk : fwdOrbit f g a k = fwdOrbit f g a (k - 1) := hf (hyfok ▸ hyeq)
      have hinj := fwdOrbit_prefix_distinct hf hg (D := fun n => n ∈ mDom L) ha hchase
      have hkk : k = k - 1 := hinj hkN (by omega) hokk
      omega

/-!
## Section 4l: The dual range step — odd-stage coverage by `Prod.swap` duality

`augment_domain_step` (Section 4k) is the even-stage move: it makes a fresh *domain* anchor
`a` covered while preserving all three invariants (`IsMatching`, `MatchingCorr`, `BuiltFrom`)
and both monotonicities. The scheduler also needs the odd-stage move: make a fresh *range*
anchor `c` covered. Rather than re-run the entire collision-chase argument on the range side,
we obtain it *for free* from the coordinate-swap duality of Section 4e.

The range step on the problem `(p, q, f, g)` is exactly the domain step on the swapped
problem `(q, p, g, f)` with the swapped matching `L.map Prod.swap`: swapping exchanges
`mDom ↔ mRan` (`mDom_map_swap`/`mRan_map_swap`), turns a matching into a matching
(`isMatching_map_swap`), a `p ↔ q` correspondence into a `q ↔ p` one
(`matchingCorr_map_swap`), and — crucially — carries the construction invariant across with
`f`, `g` exchanged (`builtFrom_map_swap`). So we push the fresh range anchor `c` through
`augment_domain_step` in the swapped world and swap the resulting matching back. This
discharges the odd stage with no new list surgery, leaving only the outer stage recursion +
computable read-off of `myhill_isomorphism`.
-/

/-- **The augmenting-path range step** (dual of `augment_domain_step`). For a fresh *range*
    anchor `c ∉ mRan L` in a matching `L` satisfying `BuiltFrom` and the correspondence, there
    is an extended matching `L'` still satisfying all three invariants, *covering* `c`
    (`c ∈ mRan L'`), and monotone on both domain and range (`mDom L ⊆ mDom L'`,
    `mRan L ⊆ mRan L'`). It is obtained by applying `augment_domain_step` to the
    coordinate-swapped problem `(q, p, g, f)` with matching `L.map Prod.swap` (Section 4e
    duality) and swapping the result back. This is the odd-stage move the priority scheduler
    iterates, complementing the even-stage `augment_domain_step`. -/
theorem augment_range_step {p q : ℕ → Prop} {f g : ℕ → ℕ}
    (hgpq : ∀ n, q n ↔ p (g n))
    (hf : Function.Injective f) (hg : Function.Injective g)
    {L : List (ℕ × ℕ)} (hL : IsMatching L) (hC : MatchingCorr p q L) (hB : BuiltFrom f g L)
    {c : ℕ} (hc : c ∉ mRan L) :
    ∃ L', IsMatching L' ∧ MatchingCorr p q L' ∧ BuiltFrom f g L' ∧
      c ∈ mRan L' ∧ (∀ x ∈ mDom L, x ∈ mDom L') ∧ (∀ y ∈ mRan L, y ∈ mRan L') ∧
      (∀ ab ∈ L, ab.1 = g ab.2 → ab ∈ L') := by
  -- Move to the swapped problem `(q, p, g, f)` with matching `L.map Prod.swap`; the fresh
  -- range anchor `c` becomes a fresh *domain* anchor there.
  have hc' : c ∉ mDom (L.map Prod.swap) := by rw [mDom_map_swap]; exact hc
  obtain ⟨M, hMmatch, hMcorr, hMbuilt, hcM, hdomMono, hranMono, hMfedge⟩ :=
    augment_domain_step (p := q) (q := p) (f := g) (g := f) hgpq hg hf
      (isMatching_map_swap hL) (matchingCorr_map_swap hC) (builtFrom_map_swap hB) hc'
  -- Swap the witness back: `L' := M.map Prod.swap`.
  refine ⟨M.map Prod.swap, isMatching_map_swap hMmatch, matchingCorr_map_swap hMcorr,
    builtFrom_map_swap hMbuilt, ?_, ?_, ?_, ?_⟩
  · -- `c ∈ mRan (M.map swap) = mDom M`
    rw [mRan_map_swap]; exact hcM
  · -- domain monotone: `mDom L ⊆ mDom (M.map swap) = mRan M`
    intro x hx
    rw [mDom_map_swap]
    exact hranMono x (by rw [mRan_map_swap]; exact hx)
  · -- range monotone: `mRan L ⊆ mRan (M.map swap) = mDom M`
    intro y hy
    rw [mRan_map_swap]
    exact hdomMono y (by rw [mDom_map_swap]; exact hy)
  · -- g-edge preservation, dual to the domain step's f-edge preservation. A `g`-edge
    -- `(u, w)` of `L` (`u = g w`) becomes an `f`-edge `(w, u)` of the swapped matching
    -- (`(w,u).2 = u = g (w,u).1`), which `augment_domain_step` preserves into `M`; swapping
    -- back returns `(u, w) ∈ M.map Prod.swap`.
    rintro ⟨u, w⟩ huwL hguw
    have hswapMem : (w, u) ∈ L.map Prod.swap := List.mem_map.mpr ⟨(u, w), huwL, rfl⟩
    have hcond : (w, u).2 = g ((w, u).1) := hguw
    have hMmem : (w, u) ∈ M := hMfedge (w, u) hswapMem hcond
    exact List.mem_map.mpr ⟨(w, u), hMmem, rfl⟩

/-!
## Section 4m: The stage sequence — iterating the atomic steps into a back-and-forth

Sections 4k/4l provide the two atomic moves as existence statements: `augment_domain_step`
(cover a fresh domain anchor) and `augment_range_step` (cover a fresh range anchor). Each
preserves the three invariants `IsMatching`, `MatchingCorr`, `BuiltFrom` and is monotone on
`mDom`/`mRan`. This section iterates them into a single sequence `stageSeq s`: the finite
matching after `s` stages, alternating domain (even `s`) and range (odd `s`) coverage of the
element `s / 2`.

The invariants travel *with* the value in a subtype so each step can feed `augment_*_step`
exactly the hypotheses it needs. We then read off:
  * `stageSeq_isMatching` / `_matchingCorr` / `_builtFrom` — the three invariants hold at
    every stage;
  * `stageSeq_mDom_mono` / `_mRan_mono` — coverage grows monotonically along `s ≤ t`;
  * `stageSeq_covers_dom` / `_covers_ran` — element `k` is covered by stage `2k+1` (domain)
    resp. `2k+2` (range). These are the domain/range exhaustion facts the limit read-off
    consumes.

`stageSeq` is built with `Classical.choose` on the (existential) atomic steps, so it is
noncomputable. Upgrading it to a genuinely computable stage function — required for the
`.Computable` half of `myhill_isomorphism` — is the remaining obstruction, tracked at the
main theorem below.
-/

/-- The three back-and-forth invariants bundled: `L` is a matching, respects the `p ↔ q`
    correspondence, and is built only from `f`/`g` edges. Carried in a subtype by `stageSeq`
    so each atomic step can consume the hypotheses `augment_*_step` requires. -/
def StageInv (p q : ℕ → Prop) (f g : ℕ → ℕ) (L : List (ℕ × ℕ)) : Prop :=
  IsMatching L ∧ MatchingCorr p q L ∧ BuiltFrom f g L

/-- One stage of the back-and-forth. Stage index `s` targets element `s / 2` on the domain
    side when `s` is even and on the range side when `s` is odd. If the target is already
    covered the matching is returned unchanged; otherwise the corresponding atomic step
    (`augment_domain_step` / `augment_range_step`) extends it, and the new invariants come
    from that step's specification. -/
noncomputable def stageStep {p q : ℕ → Prop} {f g : ℕ → ℕ}
    (hfpq : ∀ n, p n ↔ q (f n)) (hgpq : ∀ n, q n ↔ p (g n))
    (hf : Function.Injective f) (hg : Function.Injective g)
    (s : ℕ) (prev : {L : List (ℕ × ℕ) // StageInv p q f g L}) :
    {L : List (ℕ × ℕ) // StageInv p q f g L} :=
  if s % 2 = 0 then
    if h : s / 2 ∈ mDom prev.1 then prev
    else
      let ex := augment_domain_step hfpq hf hg prev.2.1 prev.2.2.1 prev.2.2.2 h
      ⟨ex.choose, ex.choose_spec.1, ex.choose_spec.2.1, ex.choose_spec.2.2.1⟩
  else
    if h : s / 2 ∈ mRan prev.1 then prev
    else
      let ex := augment_range_step hgpq hf hg prev.2.1 prev.2.2.1 prev.2.2.2 h
      ⟨ex.choose, ex.choose_spec.1, ex.choose_spec.2.1, ex.choose_spec.2.2.1⟩

/-- The stage sequence: `stageSeq 0 = []`, and each successive stage applies `stageStep`. -/
noncomputable def stageSeq {p q : ℕ → Prop} {f g : ℕ → ℕ}
    (hfpq : ∀ n, p n ↔ q (f n)) (hgpq : ∀ n, q n ↔ p (g n))
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ℕ → {L : List (ℕ × ℕ) // StageInv p q f g L}
  | 0 => ⟨[], isMatching_nil, matchingCorr_nil p q, builtFrom_nil f g⟩
  | (s + 1) => stageStep hfpq hgpq hf hg s (stageSeq hfpq hgpq hf hg s)

section StageSeqLemmas

variable {p q : ℕ → Prop} {f g : ℕ → ℕ}
  (hfpq : ∀ n, p n ↔ q (f n)) (hgpq : ∀ n, q n ↔ p (g n))
  (hf : Function.Injective f) (hg : Function.Injective g)

/-- Every stage is a matching. -/
theorem stageSeq_isMatching (s : ℕ) : IsMatching (stageSeq hfpq hgpq hf hg s).1 :=
  (stageSeq hfpq hgpq hf hg s).2.1

/-- Every stage respects the `p ↔ q` correspondence. -/
theorem stageSeq_matchingCorr (s : ℕ) : MatchingCorr p q (stageSeq hfpq hgpq hf hg s).1 :=
  (stageSeq hfpq hgpq hf hg s).2.2.1

/-- Every stage is built only from `f`/`g` edges. -/
theorem stageSeq_builtFrom (s : ℕ) : BuiltFrom f g (stageSeq hfpq hgpq hf hg s).1 :=
  (stageSeq hfpq hgpq hf hg s).2.2.2

/-- A single stage only grows the covered domain. -/
theorem stageStep_mDom_subset (s : ℕ)
    (prev : {L : List (ℕ × ℕ) // StageInv p q f g L}) {x : ℕ}
    (hx : x ∈ mDom prev.1) : x ∈ mDom (stageStep hfpq hgpq hf hg s prev).1 := by
  unfold stageStep
  split_ifs with h1 h2 h3
  · exact hx
  · exact (augment_domain_step hfpq hf hg prev.2.1 prev.2.2.1 prev.2.2.2
      h2).choose_spec.2.2.2.2.1 x hx
  · exact hx
  · exact (augment_range_step hgpq hf hg prev.2.1 prev.2.2.1 prev.2.2.2
      h3).choose_spec.2.2.2.2.1 x hx

/-- A single stage only grows the covered range. -/
theorem stageStep_mRan_subset (s : ℕ)
    (prev : {L : List (ℕ × ℕ) // StageInv p q f g L}) {y : ℕ}
    (hy : y ∈ mRan prev.1) : y ∈ mRan (stageStep hfpq hgpq hf hg s prev).1 := by
  unfold stageStep
  split_ifs with h1 h2 h3
  · exact hy
  · exact (augment_domain_step hfpq hf hg prev.2.1 prev.2.2.1 prev.2.2.2
      h2).choose_spec.2.2.2.2.2.1 y hy
  · exact hy
  · exact (augment_range_step hgpq hf hg prev.2.1 prev.2.2.1 prev.2.2.2
      h3).choose_spec.2.2.2.2.2.1 y hy

/-- One stage of the sequence only grows the covered domain. -/
theorem stageSeq_mDom_step (s : ℕ) {x : ℕ}
    (hx : x ∈ mDom (stageSeq hfpq hgpq hf hg s).1) :
    x ∈ mDom (stageSeq hfpq hgpq hf hg (s + 1)).1 :=
  stageStep_mDom_subset hfpq hgpq hf hg s (stageSeq hfpq hgpq hf hg s) hx

/-- One stage of the sequence only grows the covered range. -/
theorem stageSeq_mRan_step (s : ℕ) {y : ℕ}
    (hy : y ∈ mRan (stageSeq hfpq hgpq hf hg s).1) :
    y ∈ mRan (stageSeq hfpq hgpq hf hg (s + 1)).1 :=
  stageStep_mRan_subset hfpq hgpq hf hg s (stageSeq hfpq hgpq hf hg s) hy

/-- Domain coverage is monotone along the sequence: once `x` is covered at stage `s` it
    stays covered at every later stage `t ≥ s`. -/
theorem stageSeq_mDom_mono {s t : ℕ} (hst : s ≤ t) {x : ℕ}
    (hx : x ∈ mDom (stageSeq hfpq hgpq hf hg s).1) :
    x ∈ mDom (stageSeq hfpq hgpq hf hg t).1 := by
  induction t, hst using Nat.le_induction with
  | base => exact hx
  | succ n _ ih => exact stageSeq_mDom_step hfpq hgpq hf hg n ih

/-- Range coverage is monotone along the sequence. -/
theorem stageSeq_mRan_mono {s t : ℕ} (hst : s ≤ t) {y : ℕ}
    (hy : y ∈ mRan (stageSeq hfpq hgpq hf hg s).1) :
    y ∈ mRan (stageSeq hfpq hgpq hf hg t).1 := by
  induction t, hst using Nat.le_induction with
  | base => exact hy
  | succ n _ ih => exact stageSeq_mRan_step hfpq hgpq hf hg n ih

/-- A single even stage covers its target domain element `s / 2`. -/
theorem stageStep_covers_dom_of_even (s : ℕ)
    (prev : {L : List (ℕ × ℕ) // StageInv p q f g L}) (hs : s % 2 = 0) :
    s / 2 ∈ mDom (stageStep hfpq hgpq hf hg s prev).1 := by
  unfold stageStep
  rw [if_pos hs]
  split_ifs with h
  · exact h
  · exact (augment_domain_step hfpq hf hg prev.2.1 prev.2.2.1 prev.2.2.2
      h).choose_spec.2.2.2.1

/-- A single odd stage covers its target range element `s / 2`. -/
theorem stageStep_covers_ran_of_odd (s : ℕ)
    (prev : {L : List (ℕ × ℕ) // StageInv p q f g L}) (hs : s % 2 = 1) :
    s / 2 ∈ mRan (stageStep hfpq hgpq hf hg s prev).1 := by
  unfold stageStep
  rw [if_neg (by omega : ¬ s % 2 = 0)]
  split_ifs with h
  · exact h
  · exact (augment_range_step hgpq hf hg prev.2.1 prev.2.2.1 prev.2.2.2
      h).choose_spec.2.2.2.1

/-- **Domain exhaustion.** The even stage `2k` targets domain element `k`, so `k` is in the
    domain of the matching from stage `2k+1` onward. -/
theorem stageSeq_covers_dom (k : ℕ) :
    k ∈ mDom (stageSeq hfpq hgpq hf hg (2 * k + 1)).1 := by
  have h := stageStep_covers_dom_of_even hfpq hgpq hf hg (2 * k)
    (stageSeq hfpq hgpq hf hg (2 * k)) (by omega)
  have hdiv : 2 * k / 2 = k := by omega
  rw [hdiv] at h
  exact h

/-- **Range exhaustion.** The odd stage `2k+1` targets range element `k`, so `k` is in the
    range of the matching from stage `2k+2` onward. -/
theorem stageSeq_covers_ran (k : ℕ) :
    k ∈ mRan (stageSeq hfpq hgpq hf hg (2 * k + 2)).1 := by
  have h := stageStep_covers_ran_of_odd hfpq hgpq hf hg (2 * k + 1)
    (stageSeq hfpq hgpq hf hg (2 * k + 1)) (by omega)
  have hdiv : (2 * k + 1) / 2 = k := by omega
  rw [hdiv] at h
  exact h

/-!
## Section 5·entry: The entry-stage threshold for the limit read-off

Assembling the stage-wise matchings into a single permutation `σ : ℕ ≃ ℕ` requires knowing,
for each point `n`, a stage index from which `n` is *permanently* available. The domain and
range coverage lemmas above (`stageSeq_covers_dom` / `stageSeq_covers_ran`) give existence;
monotonicity (`stageSeq_mDom_mono` / `stageSeq_mRan_mono`) gives permanence. Together they make
the **least** covering stage well-defined — the discrete "time of first appearance" `entryStage`.

The characterization `n ∈ dom (stageSeq s) ↔ entryStageDom n ≤ s` compresses the entire
domain-growth history of a point into a single threshold, and dually on the range side. This is
the totality/surjectivity skeleton of the limit permutation: every `n` enters the domain (so `σ`
is total) and every `n` enters the range (so `σ` is surjective), each at a computable-in-principle
stage index.

**Scope caveat (recorded for the open direction).** These thresholds are *membership*-level only.
The read-off *value* `mLookup (stageSeq s) n` is **not** stable past `entryStageDom n`: the
domain-augmentation step (`augment_domain_step`) splices `L' = augPath ++ keptL`, deleting the
stale `g`-edges it re-labels, so a previously covered domain point can have its partner reassigned
at a later stage. Hence the limit `σ n` is *not* the naive pointwise stage-limit of `mLookup`; a
finite-injury bound (each point is re-labelled only finitely often) is the genuine outstanding
obligation of `myhill_isomorphism`. The entry-stage layer below is deliberately confined to the
membership facts that *do* hold unconditionally.
-/

/-- **Entry stage (domain).** The least stage index at which the domain point `n` is covered.
    Well-defined: `stageSeq_covers_dom` guarantees coverage by stage `2n+1`, and
    `stageSeq_mDom_mono` guarantees `n` stays covered thereafter. So `entryStageDom n` is the
    exact threshold past which `n` is permanently in the domain. -/
noncomputable def entryStageDom (n : ℕ) : ℕ :=
  Nat.find (⟨2 * n + 1, stageSeq_covers_dom hfpq hgpq hf hg n⟩ :
    ∃ s, n ∈ mDom (stageSeq hfpq hgpq hf hg s).1)

/-- The domain point `n` is covered at its own entry stage. -/
theorem mem_mDom_entryStageDom (n : ℕ) :
    n ∈ mDom (stageSeq hfpq hgpq hf hg (entryStageDom hfpq hgpq hf hg n)).1 :=
  Nat.find_spec (⟨2 * n + 1, stageSeq_covers_dom hfpq hgpq hf hg n⟩ :
    ∃ s, n ∈ mDom (stageSeq hfpq hgpq hf hg s).1)

/-- **Domain membership is governed by the entry stage.** `n` is covered at stage `s` iff `s`
    has reached the entry stage (`→` by minimality of `Nat.find`; `←` by domain monotonicity).
    This packages the sequence's domain growth as a single per-point threshold. -/
theorem mem_mDom_stageSeq_iff_entryStageDom_le (s n : ℕ) :
    n ∈ mDom (stageSeq hfpq hgpq hf hg s).1 ↔ entryStageDom hfpq hgpq hf hg n ≤ s := by
  constructor
  · intro h
    exact Nat.find_le h
  · intro h
    exact stageSeq_mDom_mono hfpq hgpq hf hg h (mem_mDom_entryStageDom hfpq hgpq hf hg n)

/-- **Entry stage (range).** The least stage index at which the range point `n` is covered.
    Dual to `entryStageDom`, via `stageSeq_covers_ran` (coverage by stage `2n+2`) and
    `stageSeq_mRan_mono` (permanence). Underlies surjectivity of the limit permutation. -/
noncomputable def entryStageRan (n : ℕ) : ℕ :=
  Nat.find (⟨2 * n + 2, stageSeq_covers_ran hfpq hgpq hf hg n⟩ :
    ∃ s, n ∈ mRan (stageSeq hfpq hgpq hf hg s).1)

/-- The range point `n` is covered at its own entry stage. -/
theorem mem_mRan_entryStageRan (n : ℕ) :
    n ∈ mRan (stageSeq hfpq hgpq hf hg (entryStageRan hfpq hgpq hf hg n)).1 :=
  Nat.find_spec (⟨2 * n + 2, stageSeq_covers_ran hfpq hgpq hf hg n⟩ :
    ∃ s, n ∈ mRan (stageSeq hfpq hgpq hf hg s).1)

/-- **Range membership is governed by the entry stage** (dual of the domain version). -/
theorem mem_mRan_stageSeq_iff_entryStageRan_le (s n : ℕ) :
    n ∈ mRan (stageSeq hfpq hgpq hf hg s).1 ↔ entryStageRan hfpq hgpq hf hg n ≤ s := by
  constructor
  · intro h
    exact Nat.find_le h
  · intro h
    exact stageSeq_mRan_mono hfpq hgpq hf hg h (mem_mRan_entryStageRan hfpq hgpq hf hg n)

end StageSeqLemmas

/-!
## Section 5·B: Extension-only (cons) scheduler and the limit permutation — Path B

The scheduler in `Section 4m` (`stageSeq`, built on the splicing `augment_*_step`) preserves
`BuiltFrom` but is **not pair-monotone** — a domain step re-labels stale `g`-edges — so the
read-off `mLookup_stable` cannot be applied to it (a placed point's partner changes between
stages). The decided route (Path B, Rogers §7.4 extend-only back-and-forth; see the problem's
knowledge base) instead carries the *cons-preserved* `Balanced` counts (both `Balanced f g L`
and the swapped `Balanced g f (L.map swap)`), so every stage is a pure cons and nothing is ever
removed. Then `mLookup_stable` applies directly along the whole chain and the limit permutation
`σ = sigmaB` is well-defined with **no finite-injury / stabilization argument**.

This section assembles the atomic cons steps (`domain_consStep`, `range_consStep`, from the
already-verified `escape_exists'` + the four balance-preservation lemmas), iterates them into
`stageSeqB` with pair-monotonicity (`stageSeqB_pair_subset`) and domain/range exhaustion, and
reads off the bijection `sigmaEquivB : ℕ ≃ ℕ` satisfying `p n ↔ q (σ n)` (`sigmaEquivB_corr`).

Everything here is VERIFIED 0-axiom. The **sole** remaining gap to closing `myhill_isomorphism`
is *computability* of `sigmaEquivB`: `stageSeqB` is `noncomputable` (built via `Classical.choose`
on the escape existentials), so `σ` is not yet a `Computable` function. Upgrading the escape
depth to the bounded `Nat.rfind` search that `escape_exists'` licenses (`N ≤ (mRan L).length`)
and rebuilding a computable parallel `stageSeqB` is the residual work — the mathematics (the
bijection + correspondence) is now complete.
-/

/-- Bundled invariant for the extension-only (cons) scheduler: a matching, respecting the
    `p ↔ q` correspondence, balanced on both the `g∘f` cycles (`Balanced f g L`) and the
    reverse `f∘g` cycles (`Balanced g f (L.map swap)`). Unlike `StageInv` it carries the two
    `Balanced` counts instead of `BuiltFrom`, so it is preserved by pure conses. -/
def StageInvB (p q : ℕ → Prop) (f g : ℕ → ℕ) (L : List (ℕ × ℕ)) : Prop :=
  IsMatching L ∧ MatchingCorr p q L ∧ Balanced f g L ∧ Balanced g f (L.map Prod.swap)

/-- **Even (domain) cons step.** A fresh domain anchor `a ∉ mDom L` can be matched by
    prepending the single pair `(a, chaseTarget f g a N)` for a least escaping depth `N`,
    preserving all four invariants. Escape is discharged by `escape_exists'` from the
    balance count (no `BuiltFrom`). Nothing is removed — the result is `(a,b) :: L`. -/
theorem domain_consStep {p q : ℕ → Prop} {f g : ℕ → ℕ}
    (hfpq : ∀ n, p n ↔ q (f n)) (hgpq : ∀ n, q n ↔ p (g n))
    (hf : Function.Injective f) (hg : Function.Injective g)
    {L : List (ℕ × ℕ)} (hinv : StageInvB p q f g L)
    {a : ℕ} (ha : a ∉ mDom L) :
    ∃ b, StageInvB p q f g ((a, b) :: L) ∧ (a, b) ∈ ((a, b) :: L) := by
  obtain ⟨hM, hC, hBfg, hBgf⟩ := hinv
  obtain ⟨N, hN⟩ := escape_exists' hf hg hBfg ha
  have hstep := matching_step_chase hfpq hgpq hM hC ha hN
  refine ⟨chaseTarget f g a N, ⟨hstep.1, hstep.2, ?_, ?_⟩, List.mem_cons_self⟩
  · exact balanced_cons_domain hf hg hBfg ha hN rfl
  · exact balanced_swap_cons_domain hf hg hBgf ha hN rfl

/-- **Odd (range) cons step.** A fresh range anchor `b ∉ mRan L` can be matched by prepending
    the pair `(chaseTarget g f b N, b)` for a least escaping depth `N` in the swapped problem,
    preserving all four invariants. This is the `Prod.swap` dual of `domain_consStep`: escape
    uses the swapped balance `Balanced g f (L.map swap)` via `escape_exists' hg hf`. -/
theorem range_consStep {p q : ℕ → Prop} {f g : ℕ → ℕ}
    (hfpq : ∀ n, p n ↔ q (f n)) (hgpq : ∀ n, q n ↔ p (g n))
    (hf : Function.Injective f) (hg : Function.Injective g)
    {L : List (ℕ × ℕ)} (hinv : StageInvB p q f g L)
    {b : ℕ} (hb : b ∉ mRan L) :
    ∃ a, StageInvB p q f g ((a, b) :: L) ∧ (a, b) ∈ ((a, b) :: L) := by
  obtain ⟨hM, hC, hBfg, hBgf⟩ := hinv
  -- Escape in the swapped problem `(q, p, g, f)`: `b ∉ mDom (L.map swap) = mRan L`.
  have hb' : b ∉ mDom (L.map Prod.swap) := by rw [mDom_map_swap]; exact hb
  obtain ⟨N, hN⟩ := escape_exists' hg hf hBgf hb'
  -- `a := chaseTarget g f b N = g (fwdOrbit g f b N)`; `a ∉ mRan (L.map swap) = mDom L`.
  set a := chaseTarget g f b N with ha_def
  have ha : a ∉ mDom L := by rw [← mRan_map_swap]; exact hN
  have haN : a = g (fwdOrbit g f b N) := rfl
  refine ⟨a, ⟨isMatching_cons hM ha hb, ?_, ?_, ?_⟩, List.mem_cons_self⟩
  · exact matchingCorr_cons hC (chaseTarget_corr hgpq hfpq b N).symm
  · exact balanced_swap_cons_range hf hg hBfg ha hb haN
  · exact balanced_cons_range hf hg hBgf ha hb haN

/-!
### Section 5·B-comp: The computable escape-depth core (`Classical.choose`-free)

`stageStepB` is `noncomputable` for exactly one reason: it reads its fresh partner off the
existential `domain_consStep`/`range_consStep` via `.choose`, and those rest on
`escape_exists'`'s `Classical.choose`. This block removes that dependency for the domain
(even) step.

The pivot is that the escape predicate `fun N => f (fwdOrbit f g a N) ∉ mRan L` is **decidable**
(list membership over `ℕ`), and escape is *guaranteed* (`escape_exists'`). Hence the least
escaping depth is a genuine `Nat.find`, and — crucially — `Nat.find` is **computable even when
its existence witness is a `noncomputable` proof**, because that witness is a `Prop` and is
*erased* at runtime; only the decidable 0,1,2,… search actually runs. This is precisely the
"re-parameterise to the bounded search that `escape_exists'` licenses" step the module docstring
flags as the sole remaining gap: the concrete target `chaseTarget f g a (escapeDepth …)` is
computable, and `domain_consStepC` supplies its `StageInvB`-preservation proof with **no**
`Classical.choose` anywhere in the computational content. -/

/-- **Computable least escape depth.** The smallest forward-orbit stage `N` at which the green
    image `f (fwdOrbit f g a N)` escapes `mRan L`. Decidable predicate + guaranteed escape
    (`escape_exists'`) ⇒ a genuine `Nat.find`; the existence witness `hex` is a `Prop` and is
    erased at runtime, so this reduces by a real bounded search and is computable regardless of
    how `hex` was proved. This is the `Classical.choose`-free core of the domain step. -/
def escapeDepth (f g : ℕ → ℕ) (L : List (ℕ × ℕ)) (a : ℕ)
    (hex : ∃ N, f (fwdOrbit f g a N) ∉ mRan L) : ℕ :=
  Nat.find hex

/-- The escape depth genuinely escapes: its green image lies outside `mRan L`. -/
theorem escapeDepth_spec (f g : ℕ → ℕ) (L : List (ℕ × ℕ)) (a : ℕ)
    (hex : ∃ N, f (fwdOrbit f g a N) ∉ mRan L) :
    f (fwdOrbit f g a (escapeDepth f g L a hex)) ∉ mRan L :=
  Nat.find_spec hex

/-- **Minimality** of the escape depth: every earlier stage still collides (stays in `mRan L`).
    This is the bound the scheduler uses to match the *least*-depth semantics of the classical
    construction, so the computable rebuild yields the *same* pairing, not merely *a* pairing. -/
theorem escapeDepth_min (f g : ℕ → ℕ) (L : List (ℕ × ℕ)) (a : ℕ)
    (hex : ∃ N, f (fwdOrbit f g a N) ∉ mRan L) {j : ℕ}
    (hj : j < escapeDepth f g L a hex) :
    f (fwdOrbit f g a j) ∈ mRan L :=
  not_not.mp (Nat.find_min hex hj)

/-- The chase target at the escape depth is the concrete fresh green partner
    (`chaseTarget` unfolds to `f ∘ fwdOrbit`), packaged for the cons step. -/
theorem chaseTarget_escapeDepth_notMem (f g : ℕ → ℕ) (L : List (ℕ × ℕ)) (a : ℕ)
    (hex : ∃ N, f (fwdOrbit f g a N) ∉ mRan L) :
    chaseTarget f g a (escapeDepth f g L a hex) ∉ mRan L :=
  escapeDepth_spec f g L a hex

/-- **Bounded merged escape.** The `escape_exists'` dichotomy, but *retaining the length bound*
    that both arms already prove (`escape_of_balanced` on the periodic arm,
    `escape_of_infinite_orbit` on the infinite arm): some forward-orbit stage `N ≤ (mRan L).length`
    has a green image outside `mRan L`. `escape_exists'` discards this bound; keeping it is exactly
    what lets the `Nat.find` escape depth be relocated into a *bounded* (plainly computable) search
    over `List.range ((mRan L).length + 1)` — see `escapeDepth_le`. -/
theorem escape_exists_bounded {f g : ℕ → ℕ}
    (hf : Function.Injective f) (hg : Function.Injective g)
    {L : List (ℕ × ℕ)} (hbal : Balanced f g L) {a : ℕ} (ha : a ∉ mDom L) :
    ∃ N, N ≤ (mRan L).length ∧ f (fwdOrbit f g a N) ∉ mRan L := by
  by_cases hac : OnCycle f g a
  · exact escape_of_balanced hf hg hbal hac ha
  · exact escape_of_infinite_orbit hf hg hac

/-- **The escape depth is bounded by `(mRan L).length`.** Because `escapeDepth` is the *least*
    escaping stage (`Nat.find`) and `escape_exists_bounded` supplies *some* escaping stage
    `N ≤ (mRan L).length`, the least one is `≤ (mRan L).length` too. Consequences: the canonical
    domain-cons partner `chaseTarget f g a (escapeDepth …)` can be found by scanning only the first
    `(mRan L).length + 1` forward-orbit stages, so a plain bounded search (no `Nat.find`, no
    existence-proof argument) computes the *same* value. This is the numerical fact that unblocks a
    fully computable rebuild of the extension-only scheduler. -/
theorem escapeDepth_le {f g : ℕ → ℕ}
    (hf : Function.Injective f) (hg : Function.Injective g)
    {L : List (ℕ × ℕ)} (hbal : Balanced f g L) {a : ℕ} (ha : a ∉ mDom L) :
    escapeDepth f g L a (escape_exists' hf hg hbal ha) ≤ (mRan L).length := by
  obtain ⟨N, hNle, hN⟩ := escape_exists_bounded hf hg hbal ha
  exact le_trans (Nat.find_min' _ hN) hNle

/-- **Bounded escape search (plain, proof-free).** A `List.findIdx` over the *finite* window
    `List.range ((mRan L).length + 1)` for the first stage whose green image escapes `mRan L`.
    Unlike `escapeDepth` (which is `Nat.find` and carries the escape-existence proof `hex` as an
    argument), `firstEscapeB` is an honest total function `List (ℕ × ℕ) → ℕ → ℕ` with **no** proof
    argument and **no** `Classical.choose` — it is amenable to Mathlib's `Computable` typeclass.
    By `firstEscapeB_eq_escapeDepth` it computes the *same* value as `escapeDepth` whenever escape is
    guaranteed within the window (`escapeDepth_le`), so a scheduler may replace the choice-carrying
    `escapeDepth` by `firstEscapeB` without changing the pairing. This is the computability keystone
    the module docstring flags: relocating the unbounded `Nat.find` into a bounded, plainly
    executable scan licensed by `escape_exists'`'s `N ≤ (mRan L).length` bound. -/
def firstEscapeB (f g : ℕ → ℕ) (L : List (ℕ × ℕ)) (a : ℕ) : ℕ :=
  (List.range ((mRan L).length + 1)).findIdx
    (fun N => decide (f (fwdOrbit f g a N) ∉ mRan L))

/-- **The bounded search equals the canonical escape depth.** Under the balance invariant that
    licenses escape (`escape_exists'`), the least escaping stage `escapeDepth = Nat.find` lies in the
    window `[0, (mRan L).length]` (`escapeDepth_le`); hence the bounded `List.findIdx` over
    `List.range ((mRan L).length + 1)` returns exactly that least stage. The proof is
    `List.findIdx_eq` at the index `escapeDepth`: the predicate is `true` there
    (`escapeDepth_spec`, the escape) and `false` at every earlier stage (`escapeDepth_min`, the
    collisions), and `List.getElem_range` identifies `(range _)[j] = j`. This is the flagged
    correctness keystone: it certifies that the *plain, choice-free, computable* `firstEscapeB`
    reproduces the *least-depth* pairing of the classical construction, not merely *some* pairing. -/
theorem firstEscapeB_eq_escapeDepth {f g : ℕ → ℕ}
    (hf : Function.Injective f) (hg : Function.Injective g)
    {L : List (ℕ × ℕ)} (hbal : Balanced f g L) {a : ℕ} (ha : a ∉ mDom L) :
    firstEscapeB f g L a = escapeDepth f g L a (escape_exists' hf hg hbal ha) := by
  have hle : escapeDepth f g L a (escape_exists' hf hg hbal ha) ≤ (mRan L).length :=
    escapeDepth_le hf hg hbal ha
  have hlen : escapeDepth f g L a (escape_exists' hf hg hbal ha)
      < (List.range ((mRan L).length + 1)).length := by
    rw [List.length_range]; omega
  rw [firstEscapeB, List.findIdx_eq hlen]
  refine ⟨?_, fun j hji => ?_⟩
  · simp only [List.getElem_range, decide_eq_true_eq]
    exact escapeDepth_spec f g L a _
  · simp only [List.getElem_range, decide_eq_false_iff_not, not_not]
    exact escapeDepth_min f g L a _ hji

/-- **Choice-free domain cons step.** Prepends the concrete escaping pair
    `(a, chaseTarget f g a (escapeDepth …))` — the least-depth green image, located by the
    decidable `Nat.find` above rather than `Classical.choose` — and preserves all four
    `StageInvB` invariants. This is the computable-ready twin of `domain_consStep`: same result
    list, but the partner is a *definite computable term* instead of an `.choose` read-off, so a
    scheduler built on it needs no `noncomputable` marker. -/
theorem domain_consStepC {p q : ℕ → Prop} {f g : ℕ → ℕ}
    (hfpq : ∀ n, p n ↔ q (f n)) (hgpq : ∀ n, q n ↔ p (g n))
    (hf : Function.Injective f) (hg : Function.Injective g)
    {L : List (ℕ × ℕ)} (hinv : StageInvB p q f g L)
    {a : ℕ} (ha : a ∉ mDom L) :
    StageInvB p q f g
      ((a, chaseTarget f g a
            (escapeDepth f g L a (escape_exists' hf hg hinv.2.2.1 ha))) :: L) := by
  have hbRan :
      chaseTarget f g a (escapeDepth f g L a (escape_exists' hf hg hinv.2.2.1 ha)) ∉ mRan L :=
    chaseTarget_escapeDepth_notMem f g L a _
  have hbN :
      chaseTarget f g a (escapeDepth f g L a (escape_exists' hf hg hinv.2.2.1 ha))
        = f (fwdOrbit f g a (escapeDepth f g L a (escape_exists' hf hg hinv.2.2.1 ha))) := rfl
  have hstep := matching_step_chase hfpq hgpq hinv.1 hinv.2.1 ha hbRan
  exact ⟨hstep.1, hstep.2,
    balanced_cons_domain hf hg hinv.2.2.1 ha hbRan hbN,
    balanced_swap_cons_domain hf hg hinv.2.2.2 ha hbRan hbN⟩

/-- **Choice-free range cons step.** The `Prod.swap` dual of `domain_consStepC`: prepends the
    concrete escaping pair `(chaseTarget g f b (escapeDepth …), b)` — the least-depth `g`-image of
    the fresh range anchor `b`, located by the decidable `Nat.find` (`escapeDepth`) applied to the
    *swapped* list `L.map Prod.swap` rather than `Classical.choose` — and preserves all four
    `StageInvB` invariants. Escape is licensed by `escape_exists' hg hf` on the swapped balance
    `Balanced g f (L.map Prod.swap)` (carried as `hinv.2.2.2`). Because the partner is a definite
    computable term, a scheduler built on `domain_consStepC` + this range twin needs no
    `noncomputable` marker: together they are the `Classical.choose`-free replacement for the
    existential `domain_consStep` / `range_consStep` pair. The direct hypothesis is
    `hb' : b ∉ mDom (L.map Prod.swap)` (defeq to `b ∉ mRan L`), parallel to `domain_consStepC`'s
    `a ∉ mDom L`, so the `escapeDepth` argument in the conclusion is a literal term. -/
theorem range_consStepC {p q : ℕ → Prop} {f g : ℕ → ℕ}
    (hfpq : ∀ n, p n ↔ q (f n)) (hgpq : ∀ n, q n ↔ p (g n))
    (hf : Function.Injective f) (hg : Function.Injective g)
    {L : List (ℕ × ℕ)} (hinv : StageInvB p q f g L)
    {b : ℕ} (hb' : b ∉ mDom (L.map Prod.swap)) :
    StageInvB p q f g
      ((chaseTarget g f b
            (escapeDepth g f (L.map Prod.swap) b
              (escape_exists' hg hf hinv.2.2.2 hb')), b) :: L) := by
  have hb : b ∉ mRan L := by rw [← mDom_map_swap]; exact hb'
  have haRan :
      chaseTarget g f b
          (escapeDepth g f (L.map Prod.swap) b (escape_exists' hg hf hinv.2.2.2 hb'))
        ∉ mRan (L.map Prod.swap) :=
    chaseTarget_escapeDepth_notMem g f (L.map Prod.swap) b _
  have ha :
      chaseTarget g f b
          (escapeDepth g f (L.map Prod.swap) b (escape_exists' hg hf hinv.2.2.2 hb'))
        ∉ mDom L := by rw [← mRan_map_swap]; exact haRan
  have haN :
      chaseTarget g f b
          (escapeDepth g f (L.map Prod.swap) b (escape_exists' hg hf hinv.2.2.2 hb'))
        = g (fwdOrbit g f b
            (escapeDepth g f (L.map Prod.swap) b (escape_exists' hg hf hinv.2.2.2 hb'))) := rfl
  exact ⟨isMatching_cons hinv.1 ha hb,
    matchingCorr_cons hinv.2.1 (chaseTarget_corr hgpq hfpq b _).symm,
    balanced_swap_cons_range hf hg hinv.2.2.1 ha hb haN,
    balanced_cons_range hf hg hinv.2.2.2 ha hb haN⟩

/-- One stage of the extension-only scheduler, carrying `StageInvB` in a subtype. Even `s`
    targets domain element `s/2`; odd `s` targets range element `s/2`. If already covered the
    matching is returned unchanged; otherwise the matching *grows by one cons* (nothing removed). -/
noncomputable def stageStepB {p q : ℕ → Prop} {f g : ℕ → ℕ}
    (hfpq : ∀ n, p n ↔ q (f n)) (hgpq : ∀ n, q n ↔ p (g n))
    (hf : Function.Injective f) (hg : Function.Injective g)
    (s : ℕ) (prev : {L : List (ℕ × ℕ) // StageInvB p q f g L}) :
    {L : List (ℕ × ℕ) // StageInvB p q f g L} :=
  if s % 2 = 0 then
    if h : s / 2 ∈ mDom prev.1 then prev
    else
      let ex := domain_consStep hfpq hgpq hf hg prev.2 h
      ⟨(s / 2, ex.choose) :: prev.1, ex.choose_spec.1⟩
  else
    if h : s / 2 ∈ mRan prev.1 then prev
    else
      let ex := range_consStep hfpq hgpq hf hg prev.2 h
      ⟨(ex.choose, s / 2) :: prev.1, ex.choose_spec.1⟩

/-- The extension-only stage sequence. -/
noncomputable def stageSeqB {p q : ℕ → Prop} {f g : ℕ → ℕ}
    (hfpq : ∀ n, p n ↔ q (f n)) (hgpq : ∀ n, q n ↔ p (g n))
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ℕ → {L : List (ℕ × ℕ) // StageInvB p q f g L}
  | 0 => ⟨[], isMatching_nil, matchingCorr_nil p q, balanced_nil f g, balanced_nil g f⟩
  | (s + 1) => stageStepB hfpq hgpq hf hg s (stageSeqB hfpq hgpq hf hg s)

section StageSeqBLemmas
variable {p q : ℕ → Prop} {f g : ℕ → ℕ}
  (hfpq : ∀ n, p n ↔ q (f n)) (hgpq : ∀ n, q n ↔ p (g n))
  (hf : Function.Injective f) (hg : Function.Injective g)

theorem stageSeqB_isMatching (s : ℕ) : IsMatching (stageSeqB hfpq hgpq hf hg s).1 :=
  (stageSeqB hfpq hgpq hf hg s).2.1

/-- **Pair-monotonicity of a single step** — the property Path A (splicing) lacked. Every
    recorded pair of `prev` survives into the next stage (keep-case: identical; cons-case:
    `mem_cons_of_mem`). Nothing is ever removed. -/
theorem stageStepB_pair_subset (s : ℕ)
    (prev : {L : List (ℕ × ℕ) // StageInvB p q f g L}) {x : ℕ × ℕ}
    (hx : x ∈ prev.1) : x ∈ (stageStepB hfpq hgpq hf hg s prev).1 := by
  unfold stageStepB
  split_ifs with h1 h2 h3
  · exact hx
  · exact List.mem_cons_of_mem _ hx
  · exact hx
  · exact List.mem_cons_of_mem _ hx

/-- **Pair-monotonicity along the sequence**: every pair present at stage `s` is present at
    every later stage `t ≥ s`. This makes `mLookup_stable` applicable — the read-off value of
    a covered point is immutable, so the limit permutation is well-defined without any
    finite-injury argument. -/
theorem stageSeqB_pair_subset {s t : ℕ} (hst : s ≤ t) {x : ℕ × ℕ}
    (hx : x ∈ (stageSeqB hfpq hgpq hf hg s).1) :
    x ∈ (stageSeqB hfpq hgpq hf hg t).1 := by
  induction t, hst using Nat.le_induction with
  | base => exact hx
  | succ n _ ih => exact stageStepB_pair_subset hfpq hgpq hf hg n (stageSeqB hfpq hgpq hf hg n) ih

/-- A single even stage covers its target domain element `s/2`. -/
theorem stageStepB_covers_dom_of_even (s : ℕ)
    (prev : {L : List (ℕ × ℕ) // StageInvB p q f g L}) (hs : s % 2 = 0) :
    s / 2 ∈ mDom (stageStepB hfpq hgpq hf hg s prev).1 := by
  unfold stageStepB
  rw [if_pos hs]
  split_ifs with h
  · exact h
  · simp [mDom]

/-- A single odd stage covers its target range element `s/2`. -/
theorem stageStepB_covers_ran_of_odd (s : ℕ)
    (prev : {L : List (ℕ × ℕ) // StageInvB p q f g L}) (hs : s % 2 = 1) :
    s / 2 ∈ mRan (stageStepB hfpq hgpq hf hg s prev).1 := by
  unfold stageStepB
  rw [if_neg (by omega : ¬ s % 2 = 0)]
  split_ifs with h
  · exact h
  · simp [mRan]

theorem stageSeqB_covers_dom (k : ℕ) :
    k ∈ mDom (stageSeqB hfpq hgpq hf hg (2 * k + 1)).1 := by
  have h := stageStepB_covers_dom_of_even hfpq hgpq hf hg (2 * k)
    (stageSeqB hfpq hgpq hf hg (2 * k)) (by omega)
  have hdiv : 2 * k / 2 = k := by omega
  rw [hdiv] at h; exact h

theorem stageSeqB_covers_ran (k : ℕ) :
    k ∈ mRan (stageSeqB hfpq hgpq hf hg (2 * k + 2)).1 := by
  have h := stageStepB_covers_ran_of_odd hfpq hgpq hf hg (2 * k + 1)
    (stageSeqB hfpq hgpq hf hg (2 * k + 1)) (by omega)
  have hdiv : (2 * k + 1) / 2 = k := by omega
  rw [hdiv] at h; exact h

end StageSeqBLemmas

section ReadOff
variable {p q : ℕ → Prop} {f g : ℕ → ℕ}
  (hfpq : ∀ n, p n ↔ q (f n)) (hgpq : ∀ n, q n ↔ p (g n))
  (hf : Function.Injective f) (hg : Function.Injective g)

/-- `(n, y) ∈ L` puts `n` in the domain list. -/
theorem mem_mDom_of_pair {L : List (ℕ × ℕ)} {n y : ℕ} (h : (n, y) ∈ L) : n ∈ mDom L :=
  List.mem_map.mpr ⟨(n, y), h, rfl⟩

/-- **Entry stage (domain).** Least stage at which `n` is covered on the domain side. -/
noncomputable def entryStageDomB (n : ℕ) : ℕ :=
  Nat.find (⟨2 * n + 1, stageSeqB_covers_dom hfpq hgpq hf hg n⟩ :
    ∃ s, n ∈ mDom (stageSeqB hfpq hgpq hf hg s).1)

theorem mem_mDom_entryStageDomB (n : ℕ) :
    n ∈ mDom (stageSeqB hfpq hgpq hf hg (entryStageDomB hfpq hgpq hf hg n)).1 :=
  Nat.find_spec (⟨2 * n + 1, stageSeqB_covers_dom hfpq hgpq hf hg n⟩ :
    ∃ s, n ∈ mDom (stageSeqB hfpq hgpq hf hg s).1)

/-- **The limit permutation (read-off).** `σ n` = the partner of `n` at its entry stage. -/
noncomputable def sigmaB (n : ℕ) : ℕ :=
  mLookup (stageSeqB hfpq hgpq hf hg (entryStageDomB hfpq hgpq hf hg n)).1 n

/-- **Stability of the read-off.** At any stage `s` with `n` already covered, the lookup equals
    `σ n` (pair-monotonicity + `mLookup_stable`). -/
theorem sigmaB_eq_of_mem_dom {s n : ℕ}
    (hn : n ∈ mDom (stageSeqB hfpq hgpq hf hg s).1) :
    mLookup (stageSeqB hfpq hgpq hf hg s).1 n = sigmaB hfpq hgpq hf hg n := by
  have hle : entryStageDomB hfpq hgpq hf hg n ≤ s := Nat.find_le hn
  exact (mLookup_stable (stageSeqB_isMatching hfpq hgpq hf hg _)
    (stageSeqB_isMatching hfpq hgpq hf hg _)
    (fun x hx => stageSeqB_pair_subset hfpq hgpq hf hg hle hx)
    (mem_mDom_entryStageDomB hfpq hgpq hf hg n)).symm

/-- **Read-off at the explicit bound `2n+1`.** The limit value `σ n` is already realised at stage
    `2n+1`, because `n` is covered on the domain side by then (`stageSeqB_covers_dom`) and the
    read-off is stable (`sigmaB_eq_of_mem_dom`). This eliminates the *noncomputable*
    `entryStageDomB` search from the read-off formula: `σ n` is a lookup into the list at a *fixed,
    computable* stage index `2n+1`. Combined with the (forthcoming) computability of the stage
    list, `σ` becomes computable via `mLookup_computable`. -/
theorem sigmaB_eq_bound (n : ℕ) :
    sigmaB hfpq hgpq hf hg n = mLookup (stageSeqB hfpq hgpq hf hg (2 * n + 1)).1 n :=
  (sigmaB_eq_of_mem_dom hfpq hgpq hf hg (stageSeqB_covers_dom hfpq hgpq hf hg n)).symm

/-- The pair `(n, σ n)` is recorded at `n`'s entry stage. -/
theorem sigmaB_pair_mem (n : ℕ) :
    (n, sigmaB hfpq hgpq hf hg n) ∈
      (stageSeqB hfpq hgpq hf hg (entryStageDomB hfpq hgpq hf hg n)).1 :=
  mLookup_mem_of_mem_dom (stageSeqB_isMatching hfpq hgpq hf hg _)
    (mem_mDom_entryStageDomB hfpq hgpq hf hg n)

/-- **Correspondence** `p n ↔ q (σ n)`. -/
theorem sigmaB_corr (n : ℕ) : p n ↔ q (sigmaB hfpq hgpq hf hg n) :=
  (stageSeqB hfpq hgpq hf hg _).2.2.1 _ (sigmaB_pair_mem hfpq hgpq hf hg n)

/-- **Injectivity** of the limit permutation. -/
theorem sigmaB_injective : Function.Injective (sigmaB hfpq hgpq hf hg) := by
  intro m n hmn
  set s := max (entryStageDomB hfpq hgpq hf hg m) (entryStageDomB hfpq hgpq hf hg n) with hs
  have hmpair : (m, sigmaB hfpq hgpq hf hg m) ∈ (stageSeqB hfpq hgpq hf hg s).1 :=
    stageSeqB_pair_subset hfpq hgpq hf hg (le_max_left _ _)
      (sigmaB_pair_mem hfpq hgpq hf hg m)
  have hnpair : (n, sigmaB hfpq hgpq hf hg n) ∈ (stageSeqB hfpq hgpq hf hg s).1 :=
    stageSeqB_pair_subset hfpq hgpq hf hg (le_max_right _ _)
      (sigmaB_pair_mem hfpq hgpq hf hg n)
  have hm : m ∈ mDom (stageSeqB hfpq hgpq hf hg s).1 := mem_mDom_of_pair hmpair
  have hn : n ∈ mDom (stageSeqB hfpq hgpq hf hg s).1 := mem_mDom_of_pair hnpair
  have em := sigmaB_eq_of_mem_dom hfpq hgpq hf hg hm
  have en := sigmaB_eq_of_mem_dom hfpq hgpq hf hg hn
  exact mLookup_injOn (stageSeqB_isMatching hfpq hgpq hf hg s) hm hn (by rw [em, en, hmn])

/-- **Surjectivity** of the limit permutation, from range exhaustion. -/
theorem sigmaB_surjective : Function.Surjective (sigmaB hfpq hgpq hf hg) := by
  intro m
  have hmem : m ∈ mRan (stageSeqB hfpq hgpq hf hg (2 * m + 2)).1 :=
    stageSeqB_covers_ran hfpq hgpq hf hg m
  rw [mRan, List.mem_map] at hmem
  obtain ⟨⟨d, m'⟩, hpair, hm'⟩ := hmem
  simp only at hm'
  rw [hm'] at hpair
  refine ⟨d, ?_⟩
  have hd : d ∈ mDom (stageSeqB hfpq hgpq hf hg (2 * m + 2)).1 := mem_mDom_of_pair hpair
  rw [← sigmaB_eq_of_mem_dom hfpq hgpq hf hg hd]
  exact mLookup_eq_of_mem (stageSeqB_isMatching hfpq hgpq hf hg (2 * m + 2)) hpair

/-- **The limit permutation as a bijection** `ℕ ≃ ℕ`. Noncomputable (built via `stageSeqB`,
    which uses `Classical.choose` on the escape existentials); the `.Computable` upgrade is
    the sole remaining obstruction to `myhill_isomorphism`. -/
noncomputable def sigmaEquivB : ℕ ≃ ℕ :=
  Equiv.ofBijective (sigmaB hfpq hgpq hf hg)
    ⟨sigmaB_injective hfpq hgpq hf hg, sigmaB_surjective hfpq hgpq hf hg⟩

/-- The bijection satisfies the `p ↔ q` correspondence. -/
theorem sigmaEquivB_corr (n : ℕ) : p n ↔ q (sigmaEquivB hfpq hgpq hf hg n) :=
  sigmaB_corr hfpq hgpq hf hg n

end ReadOff


/-!
## Section 5·C: The computable extension-only scheduler

`stageSeqB` (Section 5·B) is `noncomputable` for exactly one reason: `stageStepB` reads its
fresh partner off the existential `domain_consStep` / `range_consStep` via `.choose`, and those
rest on `escape_exists'`'s `Classical.choose`. This section rebuilds the *identical* extension-only
construction as a **plain `def`** `stageListC`, whose fresh partner is the concrete
`chaseTarget … (firstEscapeB …)` — `firstEscapeB` being the bounded, decidable, hypothesis-free
escape search of Section 5·B-comp, certified by `firstEscapeB_eq_escapeDepth` to reproduce the
least-depth pairing. Because nothing here uses `Classical.choose`, `stageListC` is a genuine
computable function, and the read-off `sigmaC n := mLookup (stageListC (2n+1)) n` is a *computable*
bijection with `p n ↔ q (sigmaC n)`. This discharges the entire mathematical content of
`myhill_isomorphism`'s hard direction; the sole residual obligation is the standalone
computability lemma `sigmaC_computable`.
-/

/-- **Bounded escape scan as a manifestly computable `Nat.rec`.** The escape depth of Section
    5·B-comp is `escapeDepth = Nat.find hex`, whose `hex : ∃ …` argument makes it awkward to feed
    a hypothesis-free scheduler `def`, and `firstEscapeB` (a `List.findIdx`) is not computable at the
    `Computable` level in Mathlib (only `Primrec.list_findIdx` exists, and its scan predicate here
    calls the `Computable`-not-`Primrec` `chaseTarget`). `escScan` searches the same window
    `0,1,…,(mRan prev).length` for the least stage whose green chase image `chaseTarget f g a t`
    escapes `mRan prev`, returning the sentinel `(mRan prev).length + 1` if none — as a plain
    `Nat.rec`, hence computable with the available `Computable.nat_rec` / `Computable.cond`. -/
def escScan (f g : ℕ → ℕ) (prev : List (ℕ × ℕ)) (a : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ)
    ((mRan prev).length + 1)
    (fun t st => if st ≤ (mRan prev).length then st
                 else if chaseTarget f g a t ∈ mRan prev then (mRan prev).length + 1 else t)
    ((mRan prev).length + 1)

/-- List membership as a computable `Bool` (via `List.idxOf`, primitive recursive). -/
theorem computable_mem_bool : Computable₂ (fun (y : ℕ) (l : List ℕ) => decide (y ∈ l)) := by
  have hltC : Computable₂ (fun a b : ℕ => decide (a < b)) := Primrec.nat_lt.decide.to_comp
  have hidx : Computable (fun p : ℕ × List ℕ => List.idxOf p.1 p.2) :=
    Primrec.list_idxOf.to_comp.comp Computable.fst Computable.snd
  have hlen : Computable (fun p : ℕ × List ℕ => p.2.length) :=
    Primrec.list_length.to_comp.comp Computable.snd
  exact (hltC.comp hidx hlen).of_eq
    (fun p => by rw [decide_eq_decide]; exact List.idxOf_lt_length_iff)

/-- **`escScan` is computable** in `(prev, a)`: a `Nat.rec` whose step is built from a `≤` test,
    a membership test (`computable_mem_bool`), and the computable `chaseTarget` — all assembled by
    `Computable.nat_rec` + `Computable.cond`. -/
theorem escScan_computable {f g : ℕ → ℕ} (hfc : Computable f) (hgc : Computable g) :
    Computable (fun p : List (ℕ × ℕ) × ℕ => escScan f g p.1 p.2) := by
  have hmRan : Computable (fun L : List (ℕ × ℕ) => mRan L) := by
    have h : Primrec (fun L : List (ℕ × ℕ) => L.map Prod.snd) :=
      Primrec.list_map Primrec.id (Primrec.snd.comp Primrec.snd)
    exact h.to_comp
  have hbound : Computable (fun pa : List (ℕ × ℕ) × ℕ => (mRan pa.1).length + 1) :=
    Computable.succ.comp (Primrec.list_length.to_comp.comp (hmRan.comp Computable.fst))
  have hleC : Computable₂ (fun a b : ℕ => decide (a ≤ b)) := Primrec.nat_le.decide.to_comp
  have hstep : Computable₂ (fun (pa : List (ℕ × ℕ) × ℕ) (tst : ℕ × ℕ) =>
      if tst.2 ≤ (mRan pa.1).length then tst.2
      else if chaseTarget f g pa.2 tst.1 ∈ mRan pa.1 then (mRan pa.1).length + 1 else tst.1) := by
    have hmRanX : Computable (fun x : (List (ℕ × ℕ) × ℕ) × (ℕ × ℕ) => mRan x.1.1) :=
      hmRan.comp (Computable.fst.comp Computable.fst)
    have hbX : Computable (fun x : (List (ℕ × ℕ) × ℕ) × (ℕ × ℕ) => (mRan x.1.1).length) :=
      Primrec.list_length.to_comp.comp hmRanX
    have hstX : Computable (fun x : (List (ℕ × ℕ) × ℕ) × (ℕ × ℕ) => x.2.2) :=
      Computable.snd.comp Computable.snd
    have htX : Computable (fun x : (List (ℕ × ℕ) × ℕ) × (ℕ × ℕ) => x.2.1) :=
      Computable.fst.comp Computable.snd
    have haX : Computable (fun x : (List (ℕ × ℕ) × ℕ) × (ℕ × ℕ) => x.1.2) :=
      Computable.snd.comp Computable.fst
    have hc1 : Computable (fun x : (List (ℕ × ℕ) × ℕ) × (ℕ × ℕ) =>
        decide (x.2.2 ≤ (mRan x.1.1).length)) := hleC.comp hstX hbX
    have hct : Computable (fun x : (List (ℕ × ℕ) × ℕ) × (ℕ × ℕ) =>
        chaseTarget f g x.1.2 x.2.1) := (chaseTarget_computable hfc hgc).comp haX htX
    have hc2 : Computable (fun x : (List (ℕ × ℕ) × ℕ) × (ℕ × ℕ) =>
        decide (chaseTarget f g x.1.2 x.2.1 ∈ mRan x.1.1)) := computable_mem_bool.comp hct hmRanX
    have hsent : Computable (fun x : (List (ℕ × ℕ) × ℕ) × (ℕ × ℕ) => (mRan x.1.1).length + 1) :=
      Computable.succ.comp hbX
    exact (Computable.cond hc1 hstX (Computable.cond hc2 hsent htX)).of_eq
      (fun x => by
        rcases Decidable.em (x.2.2 ≤ (mRan x.1.1).length) with h1 | h1 <;>
        rcases Decidable.em (chaseTarget f g x.1.2 x.2.1 ∈ mRan x.1.1) with h2 | h2 <;>
        simp [h1, h2])
  exact (Computable.nat_rec (α := List (ℕ × ℕ) × ℕ) (σ := ℕ) hbound hbound hstep).of_eq
    (fun pa => rfl)

/-- **Correctness of `escScan`**: if `m ≤ (mRan prev).length` is the least escaping stage (escapes
    at `m`, collides below `m`), then `escScan` returns `m`. A three-part induction on the `Nat.rec`
    depth: sentinel below `m`, value `m` at `m+1`, and value `m` maintained thereafter. -/
theorem escScan_eq_of_least {f g : ℕ → ℕ} {prev : List (ℕ × ℕ)} {a m : ℕ}
    (hmb : m ≤ (mRan prev).length)
    (hesc : chaseTarget f g a m ∉ mRan prev)
    (hmin : ∀ k < m, chaseTarget f g a k ∈ mRan prev) :
    escScan f g prev a = m := by
  set b := (mRan prev).length with hb
  set step : ℕ → ℕ → ℕ := fun t st =>
    if st ≤ b then st else if chaseTarget f g a t ∈ mRan prev then b + 1 else t with hstep
  set R : ℕ → ℕ := fun d => Nat.rec (motive := fun _ => ℕ) (b + 1) step d with hR
  have hlow : ∀ d, d ≤ m → R d = b + 1 := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      have hRn : R n = b + 1 := ih (by omega)
      have hchase : chaseTarget f g a n ∈ mRan prev := hmin n (by omega)
      have hstepval : R (n + 1) = step n (R n) := rfl
      rw [hstepval, hRn]
      show (if (b : ℕ) + 1 ≤ b then b + 1
            else if chaseTarget f g a n ∈ mRan prev then b + 1 else n) = b + 1
      rw [if_neg (by omega : ¬ ((b : ℕ) + 1 ≤ b)), if_pos hchase]
  have hm1 : R (m + 1) = m := by
    have hRm : R m = b + 1 := hlow m le_rfl
    have hstepval : R (m + 1) = step m (R m) := rfl
    rw [hstepval, hRm]
    show (if (b : ℕ) + 1 ≤ b then b + 1
          else if chaseTarget f g a m ∈ mRan prev then b + 1 else m) = m
    rw [if_neg (by omega : ¬ ((b : ℕ) + 1 ≤ b)), if_neg hesc]
  have hhigh : ∀ d, m + 1 ≤ d → R d = m := by
    intro d hd
    induction d, hd using Nat.le_induction with
    | base => exact hm1
    | succ n _ ih =>
      have hstepval : R (n + 1) = step n (R n) := rfl
      rw [hstepval, ih]
      show (if m ≤ b then m
            else if chaseTarget f g a n ∈ mRan prev then b + 1 else n) = m
      rw [if_pos hmb]
  show R (b + 1) = m
  exact hhigh (b + 1) (by omega)

/-- `escScan` reproduces the least-depth `escapeDepth` pairing, under the balance invariant that
    licenses escape within the window (`escape_exists'` + the `escapeDepth_le` bound). Drop-in
    replacement for `firstEscapeB_eq_escapeDepth`. -/
theorem escScan_eq_escapeDepth {f g : ℕ → ℕ}
    (hf : Function.Injective f) (hg : Function.Injective g)
    {L : List (ℕ × ℕ)} (hbal : Balanced f g L) {a : ℕ} (ha : a ∉ mDom L) :
    escScan f g L a = escapeDepth f g L a (escape_exists' hf hg hbal ha) := by
  refine escScan_eq_of_least (escapeDepth_le hf hg hbal ha) ?_ ?_
  · exact chaseTarget_escapeDepth_notMem f g L a _
  · intro k hk
    exact escapeDepth_min f g L a (escape_exists' hf hg hbal ha) hk

/-- One computable stage of the extension-only scheduler. Even `s` targets domain element `s/2`;
    odd `s` targets range element `s/2`. If already covered the matching is returned unchanged;
    otherwise it grows by a single cons whose partner is the concrete least-depth chase target
    (`escScan`, no `Classical.choose`). This is the choice-free twin of `stageStepB`. -/
def stageStepC (f g : ℕ → ℕ) (s : ℕ) (prev : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  if s % 2 = 0 then
    if s / 2 ∈ mDom prev then prev
    else (s / 2, chaseTarget f g (s / 2) (escScan f g prev (s / 2))) :: prev
  else
    if s / 2 ∈ mRan prev then prev
    else (chaseTarget g f (s / 2) (escScan g f (prev.map Prod.swap) (s / 2)), s / 2) :: prev

/-- The computable stage list (extension-only, `Classical.choose`-free). -/
def stageListC (f g : ℕ → ℕ) : ℕ → List (ℕ × ℕ)
  | 0 => []
  | (s + 1) => stageStepC f g s (stageListC f g s)

/-- **Pair-monotonicity of one step** — every recorded pair survives (keep-case: identical;
    cons-case: `mem_cons_of_mem`). Nothing is ever removed. -/
theorem stageStepC_pair_subset {f g : ℕ → ℕ} (s : ℕ) (prev : List (ℕ × ℕ))
    {x : ℕ × ℕ} (hx : x ∈ prev) : x ∈ stageStepC f g s prev := by
  unfold stageStepC
  split_ifs
  · exact hx
  · exact List.mem_cons_of_mem _ hx
  · exact hx
  · exact List.mem_cons_of_mem _ hx

/-- **Pair-monotonicity along the sequence**: every pair present at stage `s` is present at every
    later stage `t ≥ s`. This is exactly the `L₁ ⊆ L₂` hypothesis of `mLookup_stable`, making the
    read-off immutable (no finite injury). -/
theorem stageListC_pair_subset {f g : ℕ → ℕ} {s t : ℕ} (hst : s ≤ t)
    {x : ℕ × ℕ} (hx : x ∈ stageListC f g s) : x ∈ stageListC f g t := by
  induction t, hst using Nat.le_induction with
  | base => exact hx
  | succ n _ ih => exact stageStepC_pair_subset n _ ih

/-- A single even stage covers its target domain element `s/2`. -/
theorem stageStepC_covers_dom_of_even (f g : ℕ → ℕ) (s : ℕ) (prev : List (ℕ × ℕ))
    (hs : s % 2 = 0) : s / 2 ∈ mDom (stageStepC f g s prev) := by
  unfold stageStepC
  rw [if_pos hs]
  split_ifs with h
  · exact h
  · simp [mDom]

/-- A single odd stage covers its target range element `s/2`. -/
theorem stageStepC_covers_ran_of_odd (f g : ℕ → ℕ) (s : ℕ) (prev : List (ℕ × ℕ))
    (hs : s % 2 = 1) : s / 2 ∈ mRan (stageStepC f g s prev) := by
  unfold stageStepC
  rw [if_neg (by omega : ¬ s % 2 = 0)]
  split_ifs with h
  · exact h
  · simp [mRan]

/-- Domain exhaustion: `k` is covered on the domain side by stage `2k+1`. -/
theorem stageListC_covers_dom (f g : ℕ → ℕ) (k : ℕ) :
    k ∈ mDom (stageListC f g (2 * k + 1)) := by
  have h := stageStepC_covers_dom_of_even f g (2 * k) (stageListC f g (2 * k)) (by omega)
  rw [show (2 : ℕ) * k / 2 = k from by omega] at h
  exact h

/-- Range exhaustion: `k` is covered on the range side by stage `2k+2`. -/
theorem stageListC_covers_ran (f g : ℕ → ℕ) (k : ℕ) :
    k ∈ mRan (stageListC f g (2 * k + 2)) := by
  have h := stageStepC_covers_ran_of_odd f g (2 * k + 1) (stageListC f g (2 * k + 1)) (by omega)
  rw [show (2 * k + 1) / 2 = k from by omega] at h
  exact h

/-- **The limit permutation (computable read-off).** `σ n` is the partner of `n` at the *fixed,
    computable* stage index `2n+1` (where `n` is guaranteed covered on the domain side by
    `stageListC_covers_dom`). Because the read-off is stable along the pair-monotone chain
    (`sigmaC_eq_at`), this fixed-stage value equals the limit; and because the stage index is a
    concrete `2n+1` (not a `Nat.find` entry stage), `σ` is a plain lookup into a computable list. -/
def sigmaC (f g : ℕ → ℕ) (n : ℕ) : ℕ := mLookup (stageListC f g (2 * n + 1)) n

section SigmaC
variable {p q : ℕ → Prop} {f g : ℕ → ℕ}
  (hfpq : ∀ n, p n ↔ q (f n)) (hgpq : ∀ n, q n ↔ p (g n))
  (hf : Function.Injective f) (hg : Function.Injective g)

include hfpq hgpq hf hg

/-- Every computable stage carries the four-fold invariant `StageInvB`. The bridge from the
    hypothesis-free `firstEscapeB` to the choice-carrying `escapeDepth` is
    `firstEscapeB_eq_escapeDepth` (valid because each stage's `Balanced` invariant licenses escape);
    the invariant is then preserved by the choice-free `domain_consStepC` / `range_consStepC`. -/
theorem stageListC_inv (s : ℕ) : StageInvB p q f g (stageListC f g s) := by
  induction s with
  | zero => exact ⟨isMatching_nil, matchingCorr_nil p q, balanced_nil f g, balanced_nil g f⟩
  | succ n ih =>
    rw [stageListC]
    unfold stageStepC
    split_ifs with h1 h2 h3
    · exact ih
    · have ha : n / 2 ∉ mDom (stageListC f g n) := h2
      rw [escScan_eq_escapeDepth hf hg ih.2.2.1 ha]
      exact domain_consStepC hfpq hgpq hf hg ih ha
    · exact ih
    · have hb : n / 2 ∉ mRan (stageListC f g n) := h3
      have hb' : n / 2 ∉ mDom ((stageListC f g n).map Prod.swap) := by
        rw [mDom_map_swap]; exact hb
      rw [escScan_eq_escapeDepth hg hf ih.2.2.2 hb']
      exact range_consStepC hfpq hgpq hf hg ih hb'

/-- **Stability of the read-off.** At any stage `s` at or past `2n+1` (where `n` is covered), the
    lookup equals `σ n` — pair-monotonicity + `mLookup_stable`. -/
theorem sigmaC_eq_at (n s : ℕ) (hs : 2 * n + 1 ≤ s) :
    mLookup (stageListC f g s) n = sigmaC f g n :=
  (mLookup_stable (stageListC_inv hfpq hgpq hf hg (2 * n + 1)).1
    (stageListC_inv hfpq hgpq hf hg s).1
    (fun _ hx => stageListC_pair_subset hs hx)
    (stageListC_covers_dom f g n)).symm

/-- **Correspondence** `p n ↔ q (σ n)`, read off `MatchingCorr` at stage `2n+1`. -/
theorem sigmaC_corr (n : ℕ) : p n ↔ q (sigmaC f g n) := by
  have hinv := stageListC_inv hfpq hgpq hf hg (2 * n + 1)
  exact hinv.2.1 _ (mLookup_mem_of_mem_dom hinv.1 (stageListC_covers_dom f g n))

/-- **Injectivity** of the limit permutation (evaluate both points at a common stage). -/
theorem sigmaC_injective : Function.Injective (sigmaC f g) := by
  intro m n hmn
  set s := max (2 * m + 1) (2 * n + 1) with hs
  have hpm : (m, sigmaC f g m) ∈ stageListC f g (2 * m + 1) :=
    mLookup_mem_of_mem_dom (stageListC_inv hfpq hgpq hf hg (2 * m + 1)).1
      (stageListC_covers_dom f g m)
  have hpn : (n, sigmaC f g n) ∈ stageListC f g (2 * n + 1) :=
    mLookup_mem_of_mem_dom (stageListC_inv hfpq hgpq hf hg (2 * n + 1)).1
      (stageListC_covers_dom f g n)
  have hmdom : m ∈ mDom (stageListC f g s) :=
    mem_mDom_of_pair (stageListC_pair_subset (le_max_left _ _) hpm)
  have hndom : n ∈ mDom (stageListC f g s) :=
    mem_mDom_of_pair (stageListC_pair_subset (le_max_right _ _) hpn)
  have em := sigmaC_eq_at hfpq hgpq hf hg m s (le_max_left _ _)
  have en := sigmaC_eq_at hfpq hgpq hf hg n s (le_max_right _ _)
  exact mLookup_injOn (stageListC_inv hfpq hgpq hf hg s).1 hmdom hndom (by rw [em, en, hmn])

/-- **Surjectivity** of the limit permutation, from range exhaustion. -/
theorem sigmaC_surjective : Function.Surjective (sigmaC f g) := by
  intro m
  have hcov : m ∈ mRan (stageListC f g (2 * m + 2)) := stageListC_covers_ran f g m
  rw [mRan, List.mem_map] at hcov
  obtain ⟨⟨d, m'⟩, hpair, hm'⟩ := hcov
  simp only at hm'
  subst m'
  refine ⟨d, ?_⟩
  set s := max (2 * d + 1) (2 * m + 2) with hs
  have hpair' : (d, m) ∈ stageListC f g s := stageListC_pair_subset (le_max_right _ _) hpair
  have hval : mLookup (stageListC f g s) d = m :=
    mLookup_eq_of_mem (stageListC_inv hfpq hgpq hf hg s).1 hpair'
  have hed := sigmaC_eq_at hfpq hgpq hf hg d s (le_max_left _ _)
  rw [← hed]; exact hval

end SigmaC

set_option maxHeartbeats 1000000 in
/-- **The stage step is computable** as a function of `(s, prev)`: a two-level `cond` over the
    (primitive recursive) parity and membership tests, whose fresh-partner branch is the computable
    `chaseTarget … (escScan …)`. -/
theorem stageStepC_computable {f g : ℕ → ℕ} (hfc : Computable f) (hgc : Computable g) :
    Computable (fun x : ℕ × List (ℕ × ℕ) => stageStepC f g x.1 x.2) := by
  have hmDom : Computable (fun L : List (ℕ × ℕ) => mDom L) := by
    have h : Primrec (fun L : List (ℕ × ℕ) => L.map Prod.fst) :=
      Primrec.list_map Primrec.id (Primrec.fst.comp Primrec.snd)
    exact h.to_comp
  have hmRan : Computable (fun L : List (ℕ × ℕ) => mRan L) := by
    have h : Primrec (fun L : List (ℕ × ℕ) => L.map Prod.snd) :=
      Primrec.list_map Primrec.id (Primrec.snd.comp Primrec.snd)
    exact h.to_comp
  have hsw : Computable (fun L : List (ℕ × ℕ) => L.map Prod.swap) := by
    have hswap : Primrec₂ (fun (_ : List (ℕ × ℕ)) (elt : ℕ × ℕ) => Prod.swap elt) :=
      (Primrec.pair (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd))
    have h : Primrec (fun L : List (ℕ × ℕ) => L.map Prod.swap) :=
      Primrec.list_map Primrec.id hswap
    exact h.to_comp
  have hs2 : Computable (fun x : ℕ × List (ℕ × ℕ) => x.1 / 2) :=
    (Primrec.nat_div.comp Primrec.fst (Primrec.const 2)).to_comp
  have hprev : Computable (fun x : ℕ × List (ℕ × ℕ) => x.2) := Computable.snd
  have hmDomX : Computable (fun x : ℕ × List (ℕ × ℕ) => mDom x.2) := hmDom.comp hprev
  have hmRanX : Computable (fun x : ℕ × List (ℕ × ℕ) => mRan x.2) := hmRan.comp hprev
  have hswX : Computable (fun x : ℕ × List (ℕ × ℕ) => x.2.map Prod.swap) := hsw.comp hprev
  have heqC : Computable₂ (fun a b : ℕ => decide (a = b)) := Primrec.eq.decide.to_comp
  have hmod2 : Computable (fun x : ℕ × List (ℕ × ℕ) => x.1 % 2) :=
    (Primrec.nat_mod.comp Primrec.fst (Primrec.const 2)).to_comp
  have hc0 : Computable (fun x : ℕ × List (ℕ × ℕ) => decide (x.1 % 2 = 0)) :=
    heqC.comp hmod2 (Computable.const 0)
  have hcD : Computable (fun x : ℕ × List (ℕ × ℕ) => decide (x.1 / 2 ∈ mDom x.2)) :=
    computable_mem_bool.comp hs2 hmDomX
  have hcR : Computable (fun x : ℕ × List (ℕ × ℕ) => decide (x.1 / 2 ∈ mRan x.2)) :=
    computable_mem_bool.comp hs2 hmRanX
  have hescD : Computable (fun x : ℕ × List (ℕ × ℕ) => escScan f g x.2 (x.1 / 2)) :=
    (escScan_computable hfc hgc).comp (hprev.pair hs2)
  have hchaseD : Computable (fun x : ℕ × List (ℕ × ℕ) =>
      chaseTarget f g (x.1 / 2) (escScan f g x.2 (x.1 / 2))) :=
    (chaseTarget_computable hfc hgc).comp hs2 hescD
  have hconsD : Computable (fun x : ℕ × List (ℕ × ℕ) =>
      (x.1 / 2, chaseTarget f g (x.1 / 2) (escScan f g x.2 (x.1 / 2))) :: x.2) :=
    Computable.list_cons.comp (hs2.pair hchaseD) hprev
  have hescR : Computable (fun x : ℕ × List (ℕ × ℕ) => escScan g f (x.2.map Prod.swap) (x.1 / 2)) :=
    (escScan_computable hgc hfc).comp (hswX.pair hs2)
  have hchaseR : Computable (fun x : ℕ × List (ℕ × ℕ) =>
      chaseTarget g f (x.1 / 2) (escScan g f (x.2.map Prod.swap) (x.1 / 2))) :=
    (chaseTarget_computable hgc hfc).comp hs2 hescR
  have hconsR : Computable (fun x : ℕ × List (ℕ × ℕ) =>
      (chaseTarget g f (x.1 / 2) (escScan g f (x.2.map Prod.swap) (x.1 / 2)), x.1 / 2) :: x.2) :=
    Computable.list_cons.comp (hchaseR.pair hs2) hprev
  exact (Computable.cond hc0 (Computable.cond hcD hprev hconsD)
      (Computable.cond hcR hprev hconsR)).of_eq
    (fun x => by
      rcases Decidable.em (x.1 % 2 = 0) with h0 | h0 <;>
      rcases Decidable.em (x.1 / 2 ∈ mDom x.2) with hD | hD <;>
      rcases Decidable.em (x.1 / 2 ∈ mRan x.2) with hR | hR <;>
      simp [stageStepC, h0, hD, hR])

/-- **The stage list is computable** as a function of the stage index, via `Computable.nat_rec`
    with the computable step `stageStepC`. -/
theorem stageListC_computable {f g : ℕ → ℕ} (hfc : Computable f) (hgc : Computable g) :
    Computable (fun s => stageListC f g s) := by
  have hstep := stageStepC_computable hfc hgc
  have key : ∀ s, stageListC f g s
      = Nat.rec (motive := fun _ => List (ℕ × ℕ)) [] (fun s' ih => stageStepC f g s' ih) s := by
    intro s; induction s with
    | zero => rfl
    | succ n ih => rw [stageListC, ih]
  have hrec := Computable.nat_rec (α := ℕ) (σ := List (ℕ × ℕ))
    (f := fun s => s) (g := fun _ => ([] : List (ℕ × ℕ)))
    (h := fun (_ : ℕ) (p : ℕ × List (ℕ × ℕ)) => stageStepC f g p.1 p.2)
    Computable.id (Computable.const []) (hstep.comp Computable.snd)
  exact hrec.of_eq (fun s => (key s).symm)

/-- **Computability of the read-off** — the last obligation of `myhill_isomorphism`. Since
    `sigmaC f g n = mLookup (stageListC f g (2n+1)) n`, this is `mLookup_computable` composed with
    the computable stage list (`stageListC_computable`) at the *fixed, computable* index `2n+1`. -/
theorem sigmaC_computable {f g : ℕ → ℕ} (hfc : Computable f) (hgc : Computable g) :
    Computable (sigmaC f g) := by
  have h2n1 : Computable (fun n : ℕ => 2 * n + 1) :=
    (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)).to_comp
  exact mLookup_computable.comp ((stageListC_computable hfc hgc).comp h2n1) Computable.id


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

    **Status (Path C assembled — COMPLETE, 0-sorry / 0-axiom).** The computability gap that Path B
    left open is now closed: Section 5·C replaces the `noncomputable` `stageSeqB` with the
    computable extension-only scheduler behind `sigmaC f g`, whose read-off `sigmaC_computable`
    (`mLookup_computable ∘ stageListC_computable` at the fixed computable index `2n+1`) makes the
    permutation `Equiv.ofBijective (sigmaC f g)` a genuine `Computable` permutation. The hard
    direction below therefore discharges `e.Computable` directly — there is no remaining `sorry`.
    `#print axioms myhill_isomorphism` → `[propext, Classical.choice, Quot.sound]` only. -/
theorem myhill_isomorphism (p q : ℕ → Prop) :
    OneOneEquiv p q ↔
    ∃ e : ℕ ≃ ℕ, e.Computable ∧ ∀ n, p n ↔ q (e n) := by
  constructor
  · intro ⟨⟨f, hfc, hfi, hfpq⟩, ⟨g, hgc, hgi, hgpq⟩⟩
    -- Hard direction, via the computable extension-only scheduler (Section 5·C). The read-off
    -- `sigmaC f g` is a bijection (`sigmaC_injective` / `sigmaC_surjective`) with the correspondence
    -- `sigmaC_corr`; it is computable (`sigmaC_computable`), so the permutation
    -- `Equiv.ofBijective (sigmaC f g)` is a computable permutation
    -- (`computable_bijection_isComputablePerm`).
    have hbij : Function.Bijective (sigmaC f g) :=
      ⟨sigmaC_injective hfpq hgpq hfi hgi, sigmaC_surjective hfpq hgpq hfi hgi⟩
    exact ⟨Equiv.ofBijective (sigmaC f g) hbij,
      computable_bijection_isComputablePerm (sigmaC_computable hfc hgc) hbij,
      fun n => sigmaC_corr hfpq hgpq hfi hgi n⟩
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
