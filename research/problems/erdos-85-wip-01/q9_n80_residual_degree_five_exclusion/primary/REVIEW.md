# Independent review 2285 — PASS

Reviewer: codex-sol-1. Source: /Users/rwalters/lean-genius-q9-known-values-20260911/n80-residual-degree-five-exclusion/PROOF.md, SHA256 74b2558f55671e4691274cd2519fbbc549883ccc172958a3cac6539e3976e911.

Both packet pins and all four external premise digests were verified against current files. Reviews 2259, 2272, 2274 and 2277 are resolved PASS in the room database. Exact receipts are in verification.json. I read the four premise proofs and independently checked the following derivation; no producer or graph search was run.

## Coupling applies for every t

The slot argument in 2277 precedes its t=0 specialization: a vertex in B_p has its fixed neighbor p, k residual neighbors, and 8-k attached neighbors. The latter occupy at most one internal slot and one slot at each of six nonadjacent fixed centers. Thus k=1 saturates all seven slots, and k=2 misses exactly one. The missing fixed center is constant on the involution orbit. A fixed center receives delta such orbits, since its attached E-degree is 2 delta. Every high orbit covers two distinct residual orbits: if both neighbors of a high vertex belonged to one residual orbit, its involution image would share both, violating C4-freeness.

At a fixed vertex f and residual vertex r, AE=EA gives HY plus the nonnegative attached-to-residual E contribution on the left, and YQ+T on the right. There is no fixed-to-residual A block. Hence HY <= YQ+T for all t. At the central vertex the omitted nonnegative term vanishes by 2259, giving exact T_f0=1+delta_f-deg_P(f). Each target orbit contributes twice across all five columns, so its leaf-column total is 2 delta_f-T_f0. None of these statements relies on t=0 support enumeration.

## Independent leaf sum

The total missed leaf count of row g is 2-delta_g-1[g in M]. Summing over the three H-neighbors of f gives 3+deg_P(f)-sum_neighbor delta. The residual quotient contributes 4*1[f in M]+a_f, where a_f counts missed matched leaf labels. Substituting the exact central correction gives delta_f+sum_neighbor delta+a_f >=4 for f in P. In particular a_f=0 at t=0 and always a_f<=2-delta_f on P.

For matching P, each P delta has coefficient two after summing the four inequalities; the two M endpoints have coefficient two and other M deltas coefficient one. Thus the delta contribution is at most 2D, D=6-2t. At t=0 this bounds 16 by 12. At t=2 it bounds 16 by 4+8. At t=1 it bounds 16 by 8+(8-D_P), forcing D_P=0; the two central high neighbors supplied by 2274 lie in distinct P groups and force D_P>=2. All matching cases fail.

For star P, c has deg_P=3 and delta<=2, so delta_c=2, Y_c empty, T_c0=0. At t=0 summing just the three P-leaf inequalities yields D+2 delta_c=10, below 12. At other t, the center leaf sum gives 6-D_leaves <=4, hence D_leaves>=2. This excludes t=2 immediately. At t=1 it forces D_leaves=2 and all six M deltas zero.

## Final star t=1 argument

Each ordinary M group fills every allowed cross slot. Its matching to B_c has six edges, therefore saturates B_c too. The only allowed cross groups for c are exactly those six M groups. Every u in B_c consequently has six cross neighbors, its fixed neighbor c, internal degree at most one, and k residual neighbors, giving k=2-internal_degree. Since delta_c=2, B_c has four high vertices and two low vertices. High vertices are internally isolated and have c as their unique fixed E-target; low vertices must match each other. The unique B_c vertex adjacent to x cannot be high because this would contribute to T_c0=0. It and its distinct involution partner adjacent to x' are therefore precisely the two low vertices, which are internally adjacent. Together with the central edge they form the four distinct vertices of u-x-x'-tau(u)-u, a C4.

## Scope

PASS: every residual-degree-five case in the N80/F10 cubic-fixed involution branch is excluded by this paper proof, independently of all capped searches and finite marked-graph lists. This strengthens the earlier necessary restriction from 2251 to requiring a residual degree zero, one, or four. It does not exclude those remaining degrees, other involution branches, all N80 graphs, or Erdős 85. No Lean formalization is claimed. Old UNKNOWN/UNVISITED receipts retain their original status.
