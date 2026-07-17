/-
# Erdős Problem #666 — subgraph monotonicity of the cycle predicates

Research: erdos-666-incomplete-01

The companion `Erdos666Problem.lean` sets up the `C₂ₖ`-in-hypercube apparatus:
`HasCycle G k` (a `k`-cycle in `G`), its named cases `HasC4`, `HasC6`, `HasC2k`, the
`ε`-dense-subgraph predicate, and the refutation of Erdős's conjecture via the deep
Chung and Conder inputs (recorded as axioms).  The whole framing is about **subgraphs**
of `Qₙ` — the `DenseSubgraph` structure carries `isSubgraph : ∀ x y, graph.Adj x y →
G.Adj x y` — yet the elementary structural fact that makes "subgraph" the right notion is
missing: *cycles are monotone under subgraph inclusion.*

This file supplies it, axiom-free.  A `k`-cycle is a witness `Fin k → V` whose consecutive
images are adjacent; if `H`'s adjacency is contained in `G`'s, the very same witness is a
`k`-cycle of `G`.  Consequences:

* `hasCycle_mono` / `hasC4_mono` / `hasC6_mono` / `hasC2k_mono` — a cycle in a subgraph is a
  cycle in the ambient graph.
* `not_hasCycle_of_le` / `not_hasC6_of_le` — the contrapositive: `C₂ₖ`-freeness is
  **hereditary to subgraphs**.  This is exactly the property the Chung/Conder edge-partition
  arguments rely on — each colour class is a subgraph, so a `C₆`-free ambient graph gives
  `C₆`-free classes.
* `not_hasCycle_bot` — the empty graph has no cycle of any length, generalizing the file's
  `not_hasC6_bot` (which fixed `k = 6` and `V = Fin (2ⁿ)`) to all `k` and all `V`.
* `DenseSubgraph.not_hasC6` — the packaged application: a dense subgraph of a `C₆`-free graph
  is itself `C₆`-free.

Everything is `propext`/`Classical.choice`/`Quot.sound`-only; none of the deep Chung/Conder
axioms are invoked.
-/
import Mathlib
import Proofs.Erdos666Problem

open SimpleGraph

namespace Erdos666

variable {V : Type*}

/-! ### Subgraph monotonicity of `HasCycle` -/

unseal HasCycle in
/-- **A cycle in a subgraph is a cycle in the ambient graph.**  If every edge of `H` is an
edge of `G` (`H ≤ G` in adjacency), then any `k`-cycle witness of `H` — an injective
`Fin k → V` with adjacent consecutive images — has adjacent consecutive images in `G` too, so
it witnesses `HasCycle G k`. -/
theorem hasCycle_mono {H G : SimpleGraph V} {k : ℕ}
    (hle : ∀ x y, H.Adj x y → G.Adj x y) (h : HasCycle H k) : HasCycle G k := by
  obtain ⟨cycle, hinj, hadj, hk⟩ := h
  exact ⟨cycle, hinj, fun i => hle _ _ (hadj i), hk⟩

/-- **`C_k`-freeness is hereditary to subgraphs.**  Contrapositive of `hasCycle_mono`: if the
ambient `G` has no `k`-cycle then neither does any subgraph `H ≤ G`. -/
theorem not_hasCycle_of_le {H G : SimpleGraph V} {k : ℕ}
    (hle : ∀ x y, H.Adj x y → G.Adj x y) (h : ¬ HasCycle G k) : ¬ HasCycle H k :=
  fun hH => h (hasCycle_mono hle hH)

unseal HasCycle in
/-- **The empty graph has no cycle of any length.**  `⊥` has no edges, so the adjacency
requirement fails at the first vertex of any putative cycle (`k ≥ 3 > 0` supplies an index).
Generalizes the file's `not_hasC6_bot` from `k = 6`, `V = Fin (2ⁿ)` to arbitrary `k` and `V`. -/
theorem not_hasCycle_bot {k : ℕ} : ¬ HasCycle (⊥ : SimpleGraph V) k := by
  rintro ⟨cycle, -, hadj, hk⟩
  simpa using hadj ⟨0, by omega⟩

/-! ### The named cases `C₄`, `C₆`, `C₂ₖ` -/

unseal HasC6 in
/-- **`C₆` monotonicity:** a `C₆` in a subgraph is a `C₆` in the ambient graph. -/
theorem hasC6_mono {H G : SimpleGraph V}
    (hle : ∀ x y, H.Adj x y → G.Adj x y) (h : HasC6 H) : HasC6 G :=
  hasCycle_mono hle h

unseal HasC6 in
/-- **`C₆`-freeness is hereditary to subgraphs** — the exact property the edge-partition
refutations use (each colour class is a subgraph of `Qₙ`). -/
theorem not_hasC6_of_le {H G : SimpleGraph V}
    (hle : ∀ x y, H.Adj x y → G.Adj x y) (h : ¬ HasC6 G) : ¬ HasC6 H :=
  fun hH => h (hasC6_mono hle hH)

/-- **`C₄` monotonicity.** -/
theorem hasC4_mono {H G : SimpleGraph V}
    (hle : ∀ x y, H.Adj x y → G.Adj x y) (h : HasC4 H) : HasC4 G :=
  hasCycle_mono hle h

/-- **`C₂ₖ` monotonicity**, uniformly in `k`. -/
theorem hasC2k_mono {H G : SimpleGraph V} {k : ℕ}
    (hle : ∀ x y, H.Adj x y → G.Adj x y) (h : HasC2k H k) : HasC2k G k :=
  hasCycle_mono hle h

/-! ### Application to the dense-subgraph structure -/

/-- **A dense subgraph of a `C₆`-free graph is `C₆`-free.**  Packages `not_hasC6_of_le` with
the `DenseSubgraph.isSubgraph` field: the underlying graph of any `DenseSubgraph G m` is a
subgraph of `G`, so `C₆`-freeness of `G` transfers to it regardless of the edge count `m`. -/
theorem DenseSubgraph.not_hasC6 {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj] {m : ℕ}
    (D : DenseSubgraph G m) (hG : ¬ HasC6 G) : ¬ HasC6 D.graph :=
  not_hasC6_of_le D.isSubgraph hG

end Erdos666
