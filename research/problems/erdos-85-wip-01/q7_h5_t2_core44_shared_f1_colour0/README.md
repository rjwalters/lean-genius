# Colour0 decomposition of the remaining shared-f1 case

Scope: core44, shared singleton f1, omitted empty7, no internal F-star edge, a0-f4 and b0-f2. This is the case whose earlier author traversal exhausted but independent review2050 reached its cap. That reviewer result remains UNKNOWN and was not retried. The present decomposition first names all49 vertices through colour0 slots.

The six colour0 singletons are a0,b0,f0 and three heavy-free vertices. The first two already cover colour0 through their triples; the other four induce a perfect matching. Name f0's mate gA. The unique singleton neighbour of shared f1 has colour0. It cannot be a0 (a0 requires colours3,4), b0 (B and f1 already share C), or f0 (this case has no internal F-star edge). Name it gB. It differs from gA, since otherwise F and that vertex share f0 and f1. Thus gB pairs with the third heavy-free vertex gC.

Five distinct F-star colour0 targets saturate all S0 except f0. Known targets are f0-gA, f1-gB, f2-b0, f4-a0, so f3-gC is forced. As in reviewed2053, each g has one empty neighbour, and the remaining fourteen singletons are uniquely named by their colour and their colour0 neighbour. This gives one49-vertex partial skeleton, with five unfilled colour0-empty slots: two at f0 and one at each g. The no-internal-edge hypothesis is essential when excluding f0 as f1's target.

The only differences from the shared-f2 construction are gB-f1 instead of gB-f2, and C's remaining singleton request being colour2 instead of colour1. B already covers034 at C and shared f1 supplies colour1; D/E still require colours3,4.

All60 assignments of the empty slots are considered;24 are C4-free. Exhausting the five remaining heavy requests yields256 leaves, of which100 pass the necessary degree/colour edge-domain check. Deterministic propagation rejects all100. The independent set-based trace checker verifies every one of1507 forced edges and all100 terminal contradictions. There is no remaining branching search and no cap in this decomposition.

Independent review of the naming variant, finite cover and forcing is pending. If accepted, this excludes exactly the stated shared-f1 case; the complete shared-f1 exclusion also requires the earlier reviewed sharing cover and omitted11 confirmation. No core44/global exclusion, Lean theorem, or SAT queue change is claimed.
