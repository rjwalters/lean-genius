# Knowledge: erdos-1098-oq-01-oq-03 (Neumann ω(Γ(G)) finite ⟺ [G:Z(G)] finite)

## Session 2026-07-08 (researcher-3) — finite-group hard direction is axiom-free

File `Erdos1098OQ01OQ03.lean` is otherwise SOLVED-with-1-axiom: the forward
(easy) direction `ω ≤ [G:Z(G)]` is fully proved; the hard direction
`BoundedCliques G → (center G).index ≠ 0` is `neumann_hard_direction` (B.H. Neumann
1976, BFC/coset-covering). Prior sessions (researcher-10) LOCALIZED the axiom to the
finite-index core `H = ⋂ₐ C_G(a)` (`center_finiteIndex_iff_relIndex_core`) but could
NOT eliminate it: the Mathlib endgame `Subgroup.index_center_le_pow` needs
`Finite (commutatorSet G)`, which is itself the BFC statement = circular. Axiom stands.

New (1 thm, VERIFIED 0 sorries / axiom unchanged at 1):
- `neumann_hard_direction_of_finite [Finite G] (_ : BoundedCliques G) :`
  `(Subgroup.center G).index ≠ 0` — one-liner `Subgroup.index_ne_zero_of_finite`
  (instance `Finite (G ⧸ center G)` from `[Finite G]`). The `BoundedCliques`
  hypothesis is UNUSED — retained only so the statement is a literal drop-in for the
  axiom's signature in the finite case.

**Why (honest framing).** This is a *scoping* result, modest in size but genuine: it
proves the hard direction unconditionally and axiom-free for finite groups, showing
`neumann_hard_direction`'s content is substantive **only for infinite G**. Every finite
group satisfies it trivially (all subgroups have finite index); BFC is needed precisely
where `BoundedCliques`, not `|G|<∞`, is the sole source of finite index. Companion to the
existing `abelian_bounded_cliques` (easy direction, abelian case).

## Still open (NOT session-sized; architecturally BLOCKED)
- Eliminate `neumann_hard_direction` for infinite G. Needs bounding
  `(center G).relIndex H` = full BFC content of Neumann's theorem. Not in Mathlib;
  `index_center_le_pow` route is circular (`Finite (commutatorSet G)` ⟸ BFC).
- OQ-depth of slug = 2 (`-oq-01-oq-03`); follow-ups permitted but none strong here —
  the only open direction is the blocked BFC core.

*Build:* exit-135 SIGBUS at [3059/3059] on first fresh build (elaborated fully, crashed
on olean-write under fleet memory), plain retry `✔ Built (2.3s)`. Not a proof error.
