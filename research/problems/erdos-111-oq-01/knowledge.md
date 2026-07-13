# erdos-111-oq-01 — Bipartite Covers of Large-Chromatic Graphs

Parent: Erdős #111 (https://erdosproblems.com/111) — for χ(G) = ℵ₁ graphs, does h_G(n)/n → ∞?
This OQ: the dual "bipartite cover" viewpoint and its relation to chromatic number.

## Phase: ACT → COMPLETED (verified)

### Result (session 1, researcher-3, 2026-06-26)
Formalized in `proofs/Proofs/Erdos111OQ01.lean` (namespace `Erdos111OQ01`),
0 sorries, 0 axioms, built against Mathlib 4.26.0.

Core idea: a bipartite graph = a single `Bool`-valued 2-coloring (its bipartition).
A bipartite cover of G indexed by ι is `part : ι → V → Bool` with every edge
separated by some coordinate. Then:

- `BipartiteCover.coloring` : the product map `v ↦ (part i v)_i` is a proper
  `SimpleGraph.Coloring` into `ι → Bool`. Works for ARBITRARY ι.
- `bipartiteCoverOfColoring` : converse — any coloring into `ι → Bool` gives a cover.
- `colorable_of_bipartiteCover` [Fintype ι] : χ(G) ≤ 2^|ι|.
- `colorable_two_pow_iff_bipartiteCover (k)` : **G.Colorable (2^k) ↔ ∃ cover by k graphs**.
  i.e. bipartite-cover number = ⌈log₂ χ(G)⌉.  (Sharp, fully verified core.)
- `not_nonempty_bipartiteCover_of_chromaticNumber_top` : if `chromaticNumber = ⊤`
  (not finitely colorable, incl. χ = ℵ₁) then NO finite bipartite cover exists.

### Key Mathlib lemmas used
- `SimpleGraph.Coloring.mk`, `Coloring.valid`, `Coloring.colorable`
- `SimpleGraph.recolorOfEquiv`, `Colorable.chromaticNumber_le`
- `finFunctionFinEquiv : (Fin n → Fin m) ≃ Fin (m^n)`, `finTwoEquiv : Fin 2 ≃ Bool`
- `Fintype.card_fun`, `Fintype.card_bool`, `Function.ne_iff`, `WithTop.coe_lt_top`

### Gotcha
`SimpleGraph.Coloring α` is an abbrev for a `RelHom`, so dot notation
`C.bipartiteCover` resolves to `RelHom.bipartiteCover` (does not exist). Use a
plain function `bipartiteCoverOfColoring C` instead of a `Coloring.foo` method.

### Honesty scope
Mathlib `chromaticNumber : ℕ∞` collapses every uncountable cardinal to ⊤, so
"χ = ℵ₁" is represented exactly as "not finitely colorable" (= ⊤). The corollary
proves only that verifiable statement.

### Follow-up directions (NOT spawned — see depth guard; this is depth-1)
- Cardinal-valued chromatic number to state χ(G) ≤ 2^#ι for infinite ι
  (would let one prove "countable cover ⇒ χ ≤ 2^ℵ₀" exactly).
- Connect cover invariant back to EHS lower bound h_G(n) ≫ n via odd cycles.
