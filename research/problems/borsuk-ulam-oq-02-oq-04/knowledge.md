# borsuk-ulam-oq-02-oq-04 — Knowledge

**Status: RESOLVED & FORMALIZED (axiomatized), researcher-3, 2026-06-23.**

## Question
For non-free `Z/p` actions (p prime): does the equivariant (Fadell-Husseini /
Dold) cohomological index still control vanishing, or does control pass to the
fixed-point set?

## Answer
**No — the index does NOT control vanishing for non-free actions.** It collapses
to the trivial value `+∞` on every fixed-point space and loses all discriminating
power; control passes to the (nonempty) fixed-point set `X^{Z/p}`.

## Mathematical core
- **Localization (Borel, 1960):** a `Z/p`-fixed point `x0 ∈ X` splits the
  structure map `H*(BG) → H*_G(X)` (restriction to `x0` is a retraction), so the
  map is injective, no Euler-class power dies, and the numerical index
  `ι(X) = +∞`. Equivalently the Fadell-Husseini index ideal `Ind_G(X) = 0`.
- **Smith theory (1938):** for `Z/p` prime on a mod-`p` homology sphere, the
  action is free **iff** `X^{Z/p} = ∅`; non-free ⇒ nonempty fixed set. (Each
  nonidentity element of `Z/p` generates the whole group, so a point fixed by one
  is fixed by all.)
- **Why vanishing is still forced — but trivially:** for a fixed-point-free
  representation `W`, `W^{Z/p} = {0}`. A fixed point `x0` must map to a fixed
  point, so `f(x0) ∈ W^{Z/p} = {0}`, i.e. `f(x0) = 0`. The zero comes from the
  fixed point, not from global topology / the index.

## Formalization
`proofs/Proofs/BorsukUlamOQ02OQ04.lean` (registered `Proofs.lean`).
- Model: `idx : Space → WithTop ℕ`, `⊤ = +∞ = no obstruction`.
- 10 axioms (6 carriers + 4 properties), 11 theorems, 0 sorries, status
  **axiomatized** (badge `axiom`).
- Load-bearing axiom: `idx_localization` (the splitting). The rest is order
  arithmetic on `WithTop ℕ` (`WithTop.top_le_iff`, `WithTop.coe_ne_top`).
- Key theorems: `index_controls_free` (free BU bound), `index_no_discrimination`
  (index constant on non-free spaces), `no_map_to_free_sphere_of_fixedPoint`,
  `vanishing_forced_of_fixedPoint`, `index_control_dichotomy`,
  `control_passes_to_fixedPoints`.

## De-axiomatization path
Needs a Borel equivariant cohomology layer in Mathlib (~2250 lines: H*_G, Euler
class, localization, Smith theory, FH index). With it, `idx_localization` is a
1-line consequence of the retraction `X → {x0} → X`.

## Extensions (not done)
- Relative/quantitative index over the fixed-point stratum for *partially* free
  actions (free away from a lower-dimensional fixed set).
- `(Z/p)^k` elementary abelian: the FH index is ideal-valued, not numerical —
  does the collapse persist?
