import Mathlib

/-
# Hilbert 22 — OQ-01-OQ-03: The Abstract Kobayashi Chain Pseudometric

## Research Problem: hilbert-22-oq-01-oq-03

The Kobayashi pseudometric on a complex manifold `M` is the infimum, over all
*holomorphic chains* of disks connecting two points, of the total Poincaré
length of the chain:

  d_M(p, q) = inf { Σ ρ(aᵢ, bᵢ) | chain of holomorphic maps 𝔻 → M from p to q }.

The defining structural features of this construction are entirely *order-theoretic*
and *combinatorial*: they do not depend on complex analysis at all. They are:

  1. it is a pseudometric  (reflexivity, symmetry, triangle inequality), and
  2. it is *functorial* — distance-non-increasing under maps that contract the
     underlying atomic cost (the abstract shadow of "holomorphic maps are
     distance-non-increasing", which is what makes the Kobayashi metric an
     invariant of the complex structure).

This file isolates and *fully verifies* that order-theoretic skeleton, with **no
sorries and no axioms beyond Mathlib's foundations**. We work over an arbitrary
type `X` with a symmetric "atomic cost" `c : X → X → ℝ≥0∞` vanishing on the
diagonal — the abstract stand-in for the one-step Poincaré distance ρ of a single
disk in a chain — and build

  chainDist c p q = ⨅ over finite chains p ⇝ q of the total cost,

valued in `ℝ≥0∞` (so infima are junk-free: an empty chain set gives `⊤`, never a
spurious `0`). We prove:

* `chainDist_self`     :  d(p, p) = 0
* `chainDist_comm`     :  d(p, q) = d(q, p)
* `chainDist_triangle` :  d(p, r) ≤ d(p, q) + d(q, r)
* `chainPseudoEMetricSpace` : these package into a genuine `PseudoEMetricSpace`
* `chainDist_mono`     :  functoriality — a cost-contracting map is
                          distance-non-increasing for `chainDist`.

This is exactly properties (1)–(2) of the Kobayashi pseudometric listed in the
`hilbert-22-oq-01` gallery entry, which were previously stated only informally.
The genuinely analytic ingredients (the unit-disk Poincaré metric, Schwarz–Pick
contraction, the identification `d_𝔻 = ρ`, and Picard's theorem via the modular
λ universal cover) are **not** in Mathlib and remain open; this file deliberately
does not assume them.

## Design notes

A chain from `p` to `q` is encoded by its list of *intermediate* points
`mid : List X`; the full vertex sequence is `p, mid…, q`. The cost is summed from
the front by `chainCost`, which never needs `List.head!`/`getLast!` and so keeps
every lemma free of nonemptiness side-conditions. Concatenation of chains becomes
`List.append` with a shared joining vertex, and reversal becomes `List.reverse`;
the three pseudometric axioms are then short inductions plus the standard
`ENNReal` infimum-arithmetic lemmas `ENNReal.iInf_add` / `ENNReal.add_iInf`.

Tags: complex-geometry, kobayashi-metric, hyperbolic-manifolds, pseudometric,
hilbert-problems
-/

namespace Hilbert22OQ01OQ03

open scoped ENNReal

variable {X Y : Type*}

-- ============================================================
-- Part I: Cost of a single chain
-- ============================================================

/-- `chainCost c p mid q` is the total atomic cost of the chain whose vertex
sequence is `p`, then the intermediate points `mid`, then `q`. The sum is
accumulated from the front, so no list-head/last partial functions appear. -/
noncomputable def chainCost (c : X → X → ℝ≥0∞) : X → List X → X → ℝ≥0∞
  | p, [],      q => c p q
  | p, x :: xs, q => c p x + chainCost c x xs q

@[simp] theorem chainCost_nil (c : X → X → ℝ≥0∞) (p q : X) :
    chainCost c p [] q = c p q := rfl

@[simp] theorem chainCost_cons (c : X → X → ℝ≥0∞) (p x q : X) (xs : List X) :
    chainCost c p (x :: xs) q = c p x + chainCost c x xs q := rfl

/-- **Chain concatenation.** Splicing a chain `p ⇝ q` (intermediates `m₁`) to a
chain `q ⇝ r` (intermediates `m₂`) at the shared vertex `q` adds their costs.
This is the combinatorial heart of the triangle inequality. -/
theorem chainCost_concat (c : X → X → ℝ≥0∞) (q r : X) (m₁ m₂ : List X) :
    ∀ p, chainCost c p (m₁ ++ q :: m₂) r
        = chainCost c p m₁ q + chainCost c q m₂ r := by
  induction m₁ with
  | nil => intro p; simp
  | cons x xs ih => intro p; simp [ih, add_assoc]

/-- **Chain reversal.** When the atomic cost is symmetric, reversing a chain
preserves its total cost. This is the combinatorial heart of symmetry. -/
theorem chainCost_reverse (c : X → X → ℝ≥0∞) (hc : ∀ a b, c a b = c b a) (q : X)
    (mid : List X) : ∀ p, chainCost c p mid q = chainCost c q mid.reverse p := by
  induction mid with
  | nil => intro p; simp [hc p q]
  | cons x xs ih =>
      intro p
      rw [chainCost_cons, ih x, List.reverse_cons, chainCost_concat]
      simp [hc p x, add_comm]

/-- **Functoriality at the chain level.** A map `f : X → Y` that contracts the
atomic cost (`c_Y (f a) (f b) ≤ c_X a b`) contracts the cost of every chain after
pushing the chain forward by `f`. -/
theorem chainCost_map (cX : X → X → ℝ≥0∞) (cY : Y → Y → ℝ≥0∞) (f : X → Y)
    (hf : ∀ a b, cY (f a) (f b) ≤ cX a b) (q : X) (mid : List X) :
    ∀ p, chainCost cY (f p) (mid.map f) (f q) ≤ chainCost cX p mid q := by
  induction mid with
  | nil => intro p; simpa using hf p q
  | cons x xs ih =>
      intro p
      simp only [List.map_cons, chainCost_cons]
      exact add_le_add (hf p x) (ih x)

-- ============================================================
-- Part II: The chain pseudometric  d(p,q) = ⨅ chains, cost
-- ============================================================

/-- The **abstract Kobayashi chain pseudometric**: the infimum of the cost over
all finite chains from `p` to `q`, indexed by the list of intermediate vertices.
Valued in `ℝ≥0∞`, so the infimum is always well-defined and junk-free. -/
noncomputable def chainDist (c : X → X → ℝ≥0∞) (p q : X) : ℝ≥0∞ :=
  ⨅ mid : List X, chainCost c p mid q

/-- `chainDist` is bounded above by the cost of any particular chain. -/
theorem chainDist_le (c : X → X → ℝ≥0∞) (p q : X) (mid : List X) :
    chainDist c p q ≤ chainCost c p mid q :=
  iInf_le _ mid

/-- **Reflexivity.** If the atomic cost vanishes on the diagonal, so does the
chain pseudometric: the empty chain `p ⇝ p` already has cost `0`. -/
theorem chainDist_self (c : X → X → ℝ≥0∞) (hself : ∀ a, c a a = 0) (p : X) :
    chainDist c p p = 0 :=
  le_antisymm (by simpa [hself p] using chainDist_le c p p []) (zero_le _)

/-- **Symmetry.** A symmetric atomic cost yields a symmetric chain pseudometric:
reverse every chain. -/
theorem chainDist_comm (c : X → X → ℝ≥0∞) (hsymm : ∀ a b, c a b = c b a) (p q : X) :
    chainDist c p q = chainDist c q p := by
  have key : ∀ a b, chainDist c a b ≤ chainDist c b a := by
    intro a b
    refine le_iInf fun mid => ?_
    rw [chainCost_reverse c hsymm a mid b]
    exact chainDist_le c a b mid.reverse
  exact le_antisymm (key p q) (key q p)

/-- **Triangle inequality.** Concatenating chains at `q` realises a chain from
`p` to `r`, so `chainDist` is subadditive. Uses the `ENNReal` infimum-arithmetic
lemmas to push the two infima together. -/
theorem chainDist_triangle (c : X → X → ℝ≥0∞) (p q r : X) :
    chainDist c p r ≤ chainDist c p q + chainDist c q r := by
  unfold chainDist
  rw [ENNReal.iInf_add]
  refine le_iInf fun m₁ => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun m₂ => ?_
  rw [← chainCost_concat]
  exact iInf_le _ (m₁ ++ q :: m₂)

-- ============================================================
-- Part III: Packaging as a pseudo-extended-metric space
-- ============================================================

/-- The chain construction equips `X` with a genuine `PseudoEMetricSpace`,
provided the atomic cost is symmetric and vanishes on the diagonal. This is the
abstract Kobayashi pseudometric as a first-class Mathlib structure (properties
(1)–(2) of the gallery entry). -/
noncomputable def chainPseudoEMetricSpace (c : X → X → ℝ≥0∞)
    (hsymm : ∀ a b, c a b = c b a) (hself : ∀ a, c a a = 0) :
    PseudoEMetricSpace X where
  edist := chainDist c
  edist_self := chainDist_self c hself
  edist_comm := chainDist_comm c hsymm
  edist_triangle := chainDist_triangle c

-- ============================================================
-- Part IV: Functoriality — the defining invariance property
-- ============================================================

/-- **Functoriality / distance non-increase.** If `f : X → Y` contracts the
atomic cost, then it is distance-non-increasing for the chain pseudometric:
`d_Y (f p) (f q) ≤ d_X p q`. This is the order-theoretic shadow of the
fundamental fact that holomorphic maps are non-expanding for the Kobayashi
metric — the property that makes it a holomorphic invariant. -/
theorem chainDist_mono (cX : X → X → ℝ≥0∞) (cY : Y → Y → ℝ≥0∞) (f : X → Y)
    (hf : ∀ a b, cY (f a) (f b) ≤ cX a b) (p q : X) :
    chainDist cY (f p) (f q) ≤ chainDist cX p q := by
  refine le_iInf fun mid => ?_
  calc chainDist cY (f p) (f q)
      ≤ chainCost cY (f p) (mid.map f) (f q) := chainDist_le cY (f p) (f q) _
    _ ≤ chainCost cX p mid q := chainCost_map cX cY f hf q mid p

/-- A self-map version: an atomic-cost-contracting endomorphism is
`chainDist`-non-increasing. -/
theorem chainDist_mono_self (c : X → X → ℝ≥0∞) (f : X → X)
    (hf : ∀ a b, c (f a) (f b) ≤ c a b) (p q : X) :
    chainDist c (f p) (f q) ≤ chainDist c p q :=
  chainDist_mono c c f hf p q

-- ============================================================
-- Part V: The universal property — chainDist is the pseudometric coreflection
-- ============================================================

/-- **Lower bound by the atomic cost.** The chain pseudometric never exceeds the
atomic cost itself: the single-edge chain `p ⇝ q` (empty intermediate list) is
already admissible. -/
theorem chainDist_le_atomic (c : X → X → ℝ≥0∞) (p q : X) :
    chainDist c p q ≤ c p q := by
  simpa using chainDist_le c p q []

/-- If a candidate cost `d` is dominated edge-wise by the atomic cost `c` and
satisfies the triangle inequality, then `d p q` bounds the total cost of *every*
chain from `p` to `q`. Telescoping a chain by repeated triangle steps, each edge
bounded below `c`, recovers `d p q` as a lower bound. -/
theorem le_chainCost_of_triangle (c d : X → X → ℝ≥0∞)
    (hdc : ∀ a b, d a b ≤ c a b)
    (htri : ∀ a b r, d a r ≤ d a b + d b r) (q : X) (mid : List X) :
    ∀ p, d p q ≤ chainCost c p mid q := by
  induction mid with
  | nil => intro p; simpa using hdc p q
  | cons x xs ih =>
      intro p
      calc d p q ≤ d p x + d x q := htri p x q
        _ ≤ c p x + chainCost c x xs q := add_le_add (hdc p x) (ih x)
        _ = chainCost c p (x :: xs) q := (chainCost_cons c p x q xs).symm

/-- **Universal property.** `chainDist c` is the *greatest* pseudometric dominated
by the atomic cost `c`: any `d` that lies edge-wise below `c` and obeys the
triangle inequality also lies below `chainDist c`. Together with
`chainPseudoEMetricSpace` (which makes `chainDist c` itself such a pseudometric)
and `chainDist_le_atomic` (`chainDist c ≤ c`), this characterises the chain
construction as the **pseudometric coreflection** of the atomic cost — the
canonical largest pseudometric refining `c`. It is the order-theoretic reason the
Kobayashi chain metric is the *right* definition: it is forced, not chosen. -/
theorem le_chainDist_of_triangle (c d : X → X → ℝ≥0∞)
    (hdc : ∀ a b, d a b ≤ c a b)
    (htri : ∀ a b r, d a r ≤ d a b + d b r) (p q : X) :
    d p q ≤ chainDist c p q :=
  le_iInf fun mid => le_chainCost_of_triangle c d hdc htri q mid p

/-- **Idempotence.** If the atomic cost already satisfies the triangle inequality
(i.e. it is itself a pseudometric cost), the chain construction recovers it
exactly: `chainDist c = c`. The chaining adds nothing once subadditivity already
holds. -/
theorem chainDist_eq_of_triangle (c : X → X → ℝ≥0∞)
    (htri : ∀ a b r, c a r ≤ c a b + c b r) (p q : X) :
    chainDist c p q = c p q :=
  le_antisymm (chainDist_le_atomic c p q)
    (le_chainDist_of_triangle c c (fun _ _ => le_rfl) htri p q)

/-- **`chainDist` is idempotent.** Applying the chain construction to an
already-chained cost changes nothing: `chainDist (chainDist c) = chainDist c`.
This is the closure-operator face of the coreflection — a direct corollary of
idempotence (the inner `chainDist c` is a pseudometric, hence subadditive). -/
theorem chainDist_idem (c : X → X → ℝ≥0∞) (p q : X) :
    chainDist (chainDist c) p q = chainDist c p q :=
  chainDist_eq_of_triangle (chainDist c) (chainDist_triangle c) p q

end Hilbert22OQ01OQ03
