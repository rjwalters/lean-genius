# Research State: sylow-theorem-oq-04-oq-03

## Current State
**Phase**: BUILD (infrastructure; deep theorem BLOCKED)
**Path**: full
**Since**: 2026-07-07
**Iteration**: 5

## Current Focus
Iwasawa/Bruhat infrastructure for PSL(2,p) simplicity, built inside `SL(2, ZMod p)`.
VERIFIED this session (researcher-2, 2026-07-08, docker-build green 7743 jobs, 436L / 20
theorems, 0 sorry / 0 axiom): three new Weyl-group ingredients completing the Bruhat
symmetry —
- `weylW_conj_lowerUnipotent`: `w·U⁻·w⁻¹ = U` (the reverse of last session's
  `weylW_conj_unipotent`), so `w` interchanges the opposite root groups `U ↔ U⁻` and
  `⟨U, U⁻⟩` is `w`-conjugation-stable.
- `val_weylW_sq`: `w² = −I` (the central scalar), so `w` has order 4 in `SL(2,p)` and
  order 2 in `PSL(2,p)` — pinning down the Weyl group `W = N(T)/T ≅ ℤ/2`.
- `weylW_pow_four`: `w⁴ = 1`.
Also synced the stale meta.json (leanFile 265→436L, 4→7 defs, 17→20 thms; added the six
Weyl/Bruhat theorems from #35236 + this session to mainTheorems). Sits on the merged
unipotent Sylow-p (#34623), torus/normalizer split (#34648), and Weyl element (#35236).

## Blockers
- **Mathematical / Mathlib**: the deep simplicity theorem for the whole family p≥5 needs the
  PSL(2,p) action on P¹(𝔽_p), 2-transitivity, Borel point-stabilizers, perfectness for p≥5,
  and the Iwasawa assembly — none of that connective infrastructure exists in Mathlib
  (>1000 lines). Mathlib has only `IwasawaStructure.isSimpleGroup` and the bare `PSL` abbrev.

## Next Action
Continue the standalone BUILD: (a) generation ⟨U, U⁻⟩ = SL(2,p) from the Weyl conjugation,
(b) |SL(2,𝔽_p)| = p(p²−1), (c) the P¹(𝔽_p) action + 2-transitivity. Keep the entry BLOCKED
for the simplicity theorem itself until that action infrastructure exists.


## Session 2026-07-08 (researcher-3) — BUILD: lower unipotents are commutators for p≥5 [VERIFIED 0/0]
Added `exists_lowerUnipotent_isCommutator (hp : 5 ≤ p) (s)`: every lower unipotent
`lowerUnipotent s` is a commutator `g*h*g⁻¹*h⁻¹`. Proof conjugates the existing
`exists_unipotent_isCommutator` (upper case) by the Weyl element `w`: since
`weylW_conj_unipotent` sends `u(-s)∈U` to `lowerUnipotent s∈U⁻`, and conjugation carries a
commutator to the commutator of the conjugates (the `group` tactic discharges the
distribution `k(ghg⁻¹h⁻¹)k⁻¹`), the lower unipotent is the commutator of `w·diag(a)·w⁻¹`
and `w·u(t)·w⁻¹`. **Both** root groups U and U⁻ now lie in the derived subgroup — the two
halves of the perfectness input to Iwasawa. Docker green (7743 jobs); 520→544 L / 0 sorry /
0 axiom; meta synced (leanFile.lineCount 520→544, meta.lineCount 265→544 stale-reconcile,
meta.theoremCount 17→18 + mainTheorems entry). PR pending.

**Still BLOCKED** (deep theorem): full perfectness needs ⟨U,U⁻⟩=SL(2,p) generation; the
simplicity theorem needs the P¹(𝔽_p) action + 2-transitivity + Iwasawa assembly (>1000 L,
absent from Mathlib). Next tractable BUILD: generation ⟨U,U⁻⟩=SL(2,p) via Bruhat/Gauss.


## Session 2026-07-09 (researcher-1) — BUILD: Bruhat generation ⟨U,U⁻⟩ = SL(2,p) [UNVERIFIED]
Closed the **generation hypothesis** of Iwasawa's criterion by proving
`closure_rootGroups_eq_top : Subgroup.closure (rootGroups) = ⊤` (rootGroups = range U ∪ range U⁻),
the concrete Bruhat/Gauss decomposition of SL(2,p) — no P¹ action needed:
- `weylW_eq_root_word`: `w = u(-1)·l(1)·u(-1)` (w is a word in the root groups);
- `torusDiag_eq_root_word`: `diag(a) = u(a)·l(-a⁻¹)·u(a)·w` (whole split torus T ⊆ ⟨U,U⁻⟩);
- `mem_closure_of_lowerLeft_ne_zero`: g with lower-left c≠0 = `u(ac⁻¹)·w·diag(c)·u(dc⁻¹)`
  (top-right closes via ad−bc=1);
- c=0 case: det=1 ⇒ g₀₀≠0, and `l(1)·g` has nonzero lower-left, so `l(-1)·(l(1)·g)` sweeps it in.
Plus helpers `lowerUnipotent_mul/_zero` and membership lemmas for U, U⁻, w, T.
Re-establishes and **completes** PR #35565's reverted rootGroups material (that had only membership
of w/T, not the full `= ⊤`). File 544→738 L, 0 sorry / 0 axiom.

**BLOCKER this session**: Docker Desktop's containerd metadata DB hit a persistent `input/output error`
(`write .../io.containerd.metadata.v1.bolt/meta.db: input/output error`), so `docker run`/image build
fails before reaching Lean — verification could NOT complete. An earlier repaired-cache build DID reach
the file and showed only tactic-automation gaps (simp only left `!![..] ⟨0,⋯⟩ j` unevaluated), which are
fixed by using full `simp [Matrix.mul_apply, Fin.sum_univ_two]` for index evaluation before
`field_simp`/`linear_combination`, plus `maxHeartbeats 800000` on the two 4-matrix-product theorems.
Work is committed+pushed on branch `research/sylow-oq0403-s1783630146`; **needs a clean Docker build to
confirm** before it can be called VERIFIED.

## Next Action
Once Docker recovers, build `Proofs.SylowTheoremOQ04OQ03`; if green, upgrade status to VERIFIED and
package perfectness `commutator (SL(2,p)) = ⊤` (p≥5) from generation + the derived-subgroup lemmas.

## Session 2026-07-09 (researcher-1) — perfectness lifted to PSL(2,p)
The prior "Next Action" is now complete on main: `commutator_eq_top : commutator (SL(2,p)) = ⊤`
(p≥5) and `card_SL2 : Nat.card (SL(2,p)) = p·(p²−1)` are both merged and axiom/sorry-free.

Added **`commutator_PSL_eq_top (hp : 5 ≤ p) : commutator (PSL(2,p)) = ⊤`** — perfectness of the
*target* group PSL(2,p) = SL(2,p)/Z, not merely its cover. Two-step transport across the surjective
central quotient `mk' : SL ↠ PSL`:
- `Subgroup.map_commutator` (map of a commutator is the commutator of the maps) turns the image of
  the derived subgroup of SL into the derived subgroup of PSL;
- `Subgroup.map_top_of_surjective` (surjective ⇒ maps ⊤ to ⊤, using `QuotientGroup.mk'_surjective`)
  collapses the maps of ⊤ back to ⊤.
Then `commutator_eq_top hp` supplies `commutator (SL) = ⊤`. This states one of the two Iwasawa
hypotheses directly for PSL(2,p) and pins the p≥5 range (PSL(2,2)≅S₃, PSL(2,3)≅A₄ are not perfect).
File 855→885 L, 0 sorry / 0 axiom. **UNVERIFIED**: Docker still down (containerd blob input/output
error, `docker images` itself fails); API for every lemma used was checked against the pinned local
Mathlib source under `proofs/.lake/packages/mathlib`.

## Next Action
Once Docker recovers, build `Proofs.SylowTheoremOQ04OQ03`. Next math step toward Iwasawa: either
`|PSL(2,p)| = p(p²−1)/2` (needs `center (SL(2,p)) = {±I}`, order 2 for odd p) or begin the PSL(2,p)
action on P¹(𝔽_p) with 2-transitivity.

## Session 2026-07-11 (researcher-10) — order of PSL(2,p): |Z|=2, |PSL|=p(p²−1)/2 [VERIFIED 0/0]
Executed the standing Next Action. Two axiom-free theorems in SylowTheoremOQ04OQ03.lean
(1030→1105), VERIFIED host lake env lean exit 0 (#print axioms both = [propext,choice,
Quot.sound]):
- `card_center_SL2 (hp : 3 ≤ p) : Nat.card (center (SL(2,ZMod p))) = 2`. Via
  SpecialLinearGroup.mem_center_iff central elements = scalar (Fin 2) r with r²=1; field
  ZMod p (odd) ⟹ r=±1 (mul_self_eq_one_iff on r*r=1), so center = {1,-1} as a Set, card 2
  via `rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset, Set.ncard_pair hne]`. 1≠-1
  because 1=-1 ⟹ (2:ZMod p)=0 ⟹ p∣2 ⟹ p≤2.
- `card_PSL2 (hp : 3 ≤ p) : Nat.card (PSL(2,ZMod p)) = p*(p²−1)/2`. PSL=SL/Z, so
  Subgroup.card_mul_index: |Z|·(Z).index=|SL|; (Z).index = Nat.card PSL by rfl (index :=
  Nat.card (G⧸H), PSL := SL⧸center); rw card_center_SL2+card_SL2 then omega.

★DRIFT NOTE: on claiming, my worktree pinned to an OLD ancestor commit still had the pre-#37588
BROKEN file (set_option-after-docstring parse errors, MulEquiv.ofInjective/MonoidHom.index_ker
renamed). PR #37588 (merged 07-11) already repaired it → `git reset --hard origin/main` HEAD
gave the clean 0-error base. ALWAYS reset worktree to current origin/main, not the auto-pinned
ancestor.
★GOTCHA: `mul_self_eq_one_iff.mp (by rw[← pow_two];exact hr)` leaves `a` a METAVARIABLE (?a*?a=1
unsolvable) — bind `have hrr : r*r=1 := by rw[← pow_two]; exact hr` FIRST to fix a:=r.
★`ZMod.natCast_zmod_eq_zero_iff_dvd` deprecated → `ZMod.natCast_eq_zero_iff`. PR #37641.

REMAINING: Next math steps toward Iwasawa simplicity — PSL(2,p) action on P¹(𝔽_p) +
2-transitivity + Borel point-stabilizers (the >1000-line Mathlib gap). Order formula now DONE.
