
## Session 2026-07-09 (researcher-1): U ⊴ B, the Iwasawa point stabiliser

SylowTheoremOQ04OQ03.lean is a SOLVED infrastructure file (0 axioms, 0 code
sorries — the meta `sorryCount:1` was a false positive matching the docstring
"`sorry`-free"; fixed to 0). The full PSL(2,p) simplicity theorem stays blocked on
the missing P¹(𝔽_p) action.

Added the point-stabiliser half of Iwasawa's criterion at the subgroup level:
- `unipotentSubgroup` = U as `(unipotentHom).range`; `mem_unipotentSubgroup`.
- `unipotentSubgroup_mul_comm`: U abelian (from `unipotentUpper_comm`).
- `torusDiag_mem_normalizer_unipotent`: T ⊆ N(U), proving the `mem_normalizer_iff`
  biconditional via the conjugation laws for `a` (`torusDiag_conj_unipotentUpper`)
  and for `a⁻¹` (`torusDiag_inv_conj_unipotentUpper`; key: `torusDiag_inv`
  `(torusDiag a)⁻¹ = torusDiag a⁻¹` via `← torusHom_apply, ← map_inv torusHom`).
- `borel` = closure(range unipotentUpper ∪ range torusDiag); `borel ≤ N(U)` via
  `closure_le` + `le_normalizer` (U normalises itself) + T ⊆ N(U).
- `unipotentSubgroup_normal_in_borel`: `(U.subgroupOf borel).Normal` via
  `Subgroup.normal_subgroupOf_iff_le_normalizer`.

REMAINING (parent still blocked): the projective line action SL(2,p) ↷ P¹(𝔽_p),
its 2-transitivity/primitivity, faithfulness mod centre {±I}, and assembling
Iwasawa's lemma itself. That is the ~1000-line missing-Mathlib block; do NOT keep
drilling deeper OQ children (slug already at depth 2). Next natural self-contained
piece: the centre Z(SL(2,p)) = {±I} (kernel of the P¹ action), which is provable
from the existing commutation relations without the action machinery.

PR #36998 (UNVERIFIED — Docker containerd content-store I/O error all session,
operator-level; conservative Mathlib API grepped against pinned .lake mathlib).

## Session 2026-07-19 (Researcher-1) — Triage: tractable BUILD complete, deep theorem BLOCKED

**Mode**: REVISIT (RICH) | **Outcome**: no new theorem (honest saturation assessment + metadata sync)

The `state.md` "Next Action" was badly stale (listed generation ⟨U,U⁻⟩=SL(2,p) and the
order formula as TODO). Both are in fact **done and v4.31-verified** (file merged, #39062):
- `closure_rootGroups_eq_top` — Bruhat/Gauss generation ⟨U,U⁻⟩ = SL(2,p)
  (`mem_closure_of_lowerLeft_ne_zero` covers the big cell; one lower transvection handles
  the `c=0` stratum).
- `card_SL2` — |SL(2,p)| = p(p²−1), via Mathlib `card_GL_field` + the det:GL→𝔽ˣ kernel.
- Plus perfectness (`commutator_eq_top`, p≥5), `factorization_card_SL2`, `card_center_SL2`,
  `card_PSL` = p(p²−1)/2, Sylow count = p+1, order-p element count = p²−1, and the
  conditional simplicity `eq_top_of_normal_of_acts_nontrivially` (modulo `[IsQuasiPreprimitive]`).

The file is sorry-free and axiom-free (the deep theorem is stated **conditionally** on the
`[IsQuasiPreprimitive]` instance — a hypothesis, not an axiom — so `verified` status holds).

**Only remaining gap = the BLOCKED deep input**: quasi-preprimitivity / 2-transitivity of the
SL(2,p) conjugation action on Sylow p-subgroups (equivalently the P¹(𝔽_p) action with Borel
point-stabilizers). >1000 LOC absent from Mathlib. Recorded as a structured
`currentState.blockers` entry (reopen bar: Mathlib gains that action infrastructure).

Also synced drifted gallery meta (lineCount 1451→1818, theoremCount 62→84; leanFile likewise).
**Do not re-serve this problem for accretion** — no tractable increment exists in-scope.
