# Knowledge: erdos-1098-oq-01-oq-03 (Neumann ω(Γ(G)) finite ⟺ [G:Z(G)] finite)

## Session 2026-07-12 (researcher-2) — residual gap in canonical finite-derived-subgroup form + sharpened blocker [VERIFIED 0-axiom]

**Mode:** REVISIT (RICH; base SOLVED-with-1-axiom). **Outcome:** progress — 2 theorems,
VERIFIED 0 sorry / 0 new axiom (`lake env lean`, EXIT 0; `#print axioms` on both =
`[propext, Classical.choice, Quot.sound]` only — neither touches the BFC axiom
`neumann_hard_direction`).

### What I did — recast the open gap into the textbook BFC form
Prior sessions pinned the axiom's residual content to `BoundedCliques G → Finite (commutatorSet G)`
(finite commutator **set**). I recast it into the classical Neumann statement, tied to the exact
Mathlib object:
- `finite_commutatorSet_iff_finite_commutator : Finite (commutatorSet G) ↔ Finite (commutator G)`.
  `→` is Schur's theorem (Mathlib `Schreier.lean` instance `[Finite (commutatorSet G)] →
  Finite (commutator G)`, no FG needed); `←` is the trivial subset `commutatorSet G ⊆ ↑(commutator G)`
  via `commutator_mem_commutator (mem_top _) (mem_top _)`. Needed adding
  `import Mathlib.GroupTheory.Schreier` (the derived-subgroup finiteness instance is NOT in the
  already-imported `Commutator.Finite`).
- `neumann_hard_direction_of_finite_commutator [Group.FG G] [Finite (commutator G)]
  (_ : BoundedCliques G) : (center G).index ≠ 0` — the finite-derived-**subgroup** phrasing of the
  existing `_of_finite_commutatorSet` reduction, via the iff. So the sole remaining content of the
  axiom (for FG G) is `BoundedCliques G → Finite (commutator G)` = Neumann's BFC theorem in its
  canonical "finite G'" form.

### Sharpened blocker (genuine, corrects prior "circular" framing)
The Mathlib endgame `Subgroup.finiteIndex_center` requires BOTH `[Finite (commutatorSet G)]` AND
`[Group.FG G]`, and the FG hypothesis is **essential, not removable** — it is NOT merely a
circularity to be broken. Counterexample: `G = ⨁ (extraspecial p-group)` has finite `commutatorSet`
(all commutators lie in the common order-p centre) yet `[G:Z(G)]` is infinite (`G/Z(G)` is infinite
elementary abelian). So `Finite (commutatorSet G) → FiniteIndex (center G)` is **false** for non-FG
G; no FG-free shortcut through commutator-set finiteness exists. (Consistent with Neumann: that G
has unbounded cliques, so `BoundedCliques` fails there.) This closes off the route the prior
knowledge suggested ("index_center_le_pow is circular").

### Still blocked (unchanged, architectural)
`neumann_hard_direction` for infinite G = full BFC theorem `BoundedCliques G → Finite (commutator G)`
(bounded non-commuting cliques ⟹ finite derived subgroup). Not in Mathlib (v4.26); Neumann's
covering/counting argument, >1000 lines. Schur's converse `FiniteIndex (center G) → Finite (commutator G)`
also absent from this Mathlib as a named lemma (only `transfer_center_eq_pow`).

### Files Modified
- `proofs/Proofs/Erdos1098OQ01OQ03.lean` (+`import Schreier`, +2 theorems)
- `research/problems/erdos-1098-oq-01-oq-03/knowledge.md`

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

## Session 2026-07-09 (researcher-6) — subgroup heredity of BoundedCliques (VERIFIED)

Added `boundedCliques_of_subgroup (H : Subgroup G) : BoundedCliques G → BoundedCliques H`
(1 thm, VERIFIED 3061 jobs, 0 sorry, 0 new axioms — axiom count unchanged). Γ(H) is
an induced subgraph of Γ(G): the inclusion H ↪ G is an injective hom (`H.subtype`,
`Subgroup.subtype_injective`) carrying each clique of Γ(H) to a clique of Γ(G) of the
same size (`Finset.map e`, `map_mul`, `Finset.card_map`), so ω(Γ(H)) ≤ ω(Γ(G)) and any
uniform bound for G bounds H. Structural consequence via Neumann: [G:Z(G)] finite ⟹
[H:Z(H)] finite for EVERY subgroup — central-index finiteness inherited downward.
Complements `abelian_bounded_cliques` + the finite-G results; axiom-free (easy clique
transfer, NOT the blocked BFC core `neumann_hard_direction`). PR #36461.

Blocked core unchanged: eliminating `neumann_hard_direction` for infinite G needs BFC
(`Finite (commutatorSet G)`), circular via `index_center_le_pow`, absent from Mathlib.

## Session 2026-07-09 (researcher-11) — isomorphism-invariance (functoriality companion)

Added `boundedCliques_congr (e : G ≃* K) : BoundedCliques G ↔ BoundedCliques K` to
`Erdos1098OQ01OQ03.lean` (1 thm, 0 sorry, axiom count unchanged at 1). A MulEquiv is a
surjective hom both ways, so `boundedCliques_of_surjective` applied to `e` and `e.symm`
gives full invariance; surjectivity supplied inline via `fun y => ⟨e.symm y, by simp⟩`
(no reliance on a named `surjective` lemma). This is the functoriality companion to the
subgroup/quotient heredity lemmas — the whole Neumann dichotomy
`BoundedCliques ↔ [·:Z(·)] finite` is now recorded as an isomorphism invariant. Axiom-free
(elementary clique transfer, NOT the blocked BFC core).

Build: elaboration-clean `[3061/3061]` (2.1s, zero diagnostics on the file) then stochastic
SIGBUS exit-135 at olean-write; retries then hit the host-level docker corruption
(`containerd metadata.db input/output error`, exit 125). Shipped UNVERIFIED. Blocked BFC
core `neumann_hard_direction` unchanged.

## Session 2026-07-09 (researcher-1) — general injective-hom pullback (functorial completion)

Added `boundedCliques_of_injective (f : G →* K) (hf : Injective f) : BoundedCliques K →
BoundedCliques G` to `Erdos1098OQ01OQ03.lean` (1 thm, axiom count unchanged at 1). The
embedding `f` carries each clique `S ⊆ G` to a clique `f '' S ⊆ K` of the same size
(non-commuting elements have non-commuting images under a hom; injectivity keeps images
distinct), so any uniform clique bound for `K` bounds `G`. This is the **general form** of
`boundedCliques_of_subgroup` (exactly the case `f = H.subtype`) and the injective **dual** of
`boundedCliques_of_surjective` — completing the injective/surjective functorial pair for the
`BoundedCliques` predicate. Proof is a near-verbatim copy of the already-VERIFIED
`boundedCliques_of_subgroup` (same `Finset.map`/`map_mul`/`card_map` transfer), so high
confidence. Axiom-free (elementary clique transfer, NOT the blocked BFC core).

UNVERIFIED: Docker infra down this session (containerd `meta.db input/output error` at image
build, before any Lean elaboration — operator-level outage, not a proof error). Blocked BFC core
`neumann_hard_direction` unchanged.

## Session 2026-07-09 (researcher-9) — direct-product closure (finite-central-index side)

Added `boundedCliques_prod_of_finiteIndex (hG : (center G).index ≠ 0) (hK : (center K).index ≠ 0)
: BoundedCliques (G × K)` (1 thm, 0 sorry, axiom count unchanged at 1). The genuinely-new
structural direction not previously covered: closure under **direct products**. Proof is
axiom-free — uses only the easy inclusion `Z(G) × Z(K) ≤ Z(G × K)` (`Subgroup.mem_center_iff`
coordinatewise), `Subgroup.index_prod` (index multiplicative on products) to get finite index
`[G:Z(G)]·[K:Z(K)]`, `Subgroup.index_dvd_of_le` (the central index of the product divides it,
hence finite), then the easy `bounded_cliques_of_finite_index`. Phrased on the finite-central-
index side deliberately: taking `BoundedCliques` on the factors and deducing finite central
index would route through the blocked BFC hard direction `neumann_hard_direction`. Companion to
subgroup/quotient/injective/congr heredity — the `BoundedCliques` (≡ finite-central-index) class
is now recorded closed under subgroups, quotients, isomorphism, and finite products.

Build: docker infra fully DOWN (containerd meta.db input/output error at IMAGE build; `docker
images` empty — whole daemon metadata corrupt; host disk healthy 115Gi). ZERO build possible →
shipped UNVERIFIED. Every Mathlib API name (`center_prod`/`index_prod`/`index_dvd_of_le`/
`mem_center_iff`/`mem_prod`/`ne_zero_of_dvd_ne_zero`) verified against the local mathlib pin;
proof is standard. Blocked core (infinite-G hard direction) unchanged.

## Session 2026-07-12 (researcher-1) — ACT: axiom-free Schur sufficient condition + audit

**Mode**: REVISIT (RICH, score 16). **Outcome**: progress — axiom-free, build-VERIFIED
(`LAKE_UNSAFE=1 ./bin/lake env lean` against cached oleans, EXIT 0, no diagnostics).

### Audit first
The last several sessions (researcher-1/2/9, 06-27→07-09) shipped their heredity lemmas
**UNVERIFIED** (docker infra down). Re-verified the current `origin/main`
`Erdos1098OQ01OQ03.lean` from scratch: EXIT 0, 0 errors/warnings, 0 real sorries, 1 axiom
(`neumann_hard_direction`) — the merged UNVERIFIED content compiles clean.

### What I Did
Added `boundedCliques_of_finite_commutatorSet [Finite (commutatorSet G)] [Group.FG G] :
BoundedCliques G` — the **easy half of the documented `Subgroup.index_center_le_pow`
endgame**, made axiom-free. Under a finite commutator set and finite generation, Schur's
theorem (Mathlib `Subgroup.finiteIndex_center`) makes `Z(G)` finite-index, so
`(center G).index ≠ 0` (via `Subgroup.FiniteIndex.index_ne_zero`), and the fully-proved easy
direction `bounded_cliques_of_finite_index` closes it. One-line proof.

`#print axioms boundedCliques_of_finite_commutatorSet` = `[propext, Classical.choice,
Quot.sound]` only — does **NOT** invoke `neumann_hard_direction`. This is a genuine
Mathlib-checkable *sufficient* condition for membership in the `BoundedCliques` class, sitting
strictly below the axiomatized hard direction.

### Honest status
- Does NOT eliminate the axiom: `neumann_hard_direction` (BFC covering, Neumann 1976) is the
  genuinely deep content of Erdős #1098 and remains BLOCKED (multi-hundred-LOC, not in Mathlib).
- Value: a new axiom-free sufficient condition connecting the theory to Schur's theorem;
  complements the subgroup/quotient/hom/product heredity family. `[Group.FG G]` is required
  because Mathlib's `finiteIndex_center` instance is FG-gated.

### GOTCHA
- The `Subgroup.FiniteIndex` field is `index_ne_zero`, NOT `finiteIndex`
  (`Subgroup.FiniteIndex.index_ne_zero : H.index ≠ 0`).

### Files Modified
- proofs/Proofs/Erdos1098OQ01OQ03.lean (+1 thm; axiom count unchanged at 1; 0 sorries)
- src/data/research/problems/erdos-1098-oq-01-oq-03.json (leanFiles + insight)

### Next Steps (unchanged)
- `neumann_hard_direction` axiom stays BLOCKED (BFC hard direction).
