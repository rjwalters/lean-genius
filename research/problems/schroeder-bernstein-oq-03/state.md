# Research State: schroeder-bernstein-oq-03

## Current State
**Phase**: DEVELOP — **Path B ASSEMBLED (r11, 2026-07-03): cons scheduler + limit bijection
VERIFIED; only COMPUTABILITY remains**
**Path**: full — extension-only (Path B); fork RESOLVED 2026-07-03 (r4), scheduler built r11
**Since**: 2026-07-02
**Iteration**: 10

## Next Action (supersedes all below — 2026-07-03 r8b)
**r8b landed the flagged-risk correctness keystone (VERIFIED 0-axiom, PR pending):**
- `firstEscapeB f g L a := (List.range ((mRan L).length + 1)).findIdx (fun N => decide (f (fwdOrbit
  f g a N) ∉ mRan L))` — a plain total function: NO `Classical.choose`, NO proof argument, so it is
  `Computable`-amenable (unlike `escapeDepth`, which carries the escape-existence proof).
- `firstEscapeB_eq_escapeDepth` — the bridge `firstEscapeB f g L a = escapeDepth f g L a
  (escape_exists' …)` under the balance invariant. Proof: `List.findIdx_eq` at index `escapeDepth`
  (`escapeDepth_le` puts it in-window; `escapeDepth_spec` = predicate true there; `escapeDepth_min`
  = false at earlier stages; `List.getElem_range` for `(range n)[j]=j`). **This retires the
  documented "only real risk (core findIdx lemma hunt)."** The lemmas used all exist in
  Lean core v4.26.0 `Init.Data.List.Find`/`Range`: `findIdx_eq`, `getElem_range`, `length_range`.

**REMAINING (concrete, next session) — pure mechanical Primrec assembly, no new math:**
1. **`firstEscapeB_computable`** — `Computable (fun (La : List (ℕ×ℕ) × ℕ) => firstEscapeB f g La.1
   La.2)` given `hf hg : Computable`. Building blocks all confirmed present:
   `Primrec.list_findIdx` (Primrec.lean:1007), `Primrec.list_range` (:973), `Primrec.list_length`
   (:996), `Primrec.list_map` (:967, for `mRan = map Prod.snd`), `fwdOrbit_computable` (in-file).
   ONLY open sub-lemma: a **list-membership Bool primrec** `Primrec₂ (fun (l:List ℕ) y => decide (y
   ∈ l))` for the per-element escape predicate — likely via `Primrec.list_idxOf` (:1013) +
   `y ∈ l ↔ l.idxOf y < l.length`, or an `exists_mem_list`/`beq` route. This is the next lemma hunt.
2. Then the computable scheduler + read-off + `myhill_isomorphism` discharge (unchanged from below).

## Next Action (superseded — 2026-07-03 r8)
**r8 landed the two definitional keystones for computability (VERIFIED 0-axiom, PR pending):**
- `escape_exists_bounded` — merged dichotomy KEEPING the `N ≤ (mRan L).length` bound that
  `escape_exists'` discarded (both arms `escape_of_balanced` / `escape_of_infinite_orbit` already
  prove it).
- `escapeDepth_le` — the canonical least escape depth `escapeDepth f g L a (Nat.find)` satisfies
  `escapeDepth ≤ (mRan L).length`. So the canonical domain-cons partner
  `chaseTarget f g a (escapeDepth …)` is locatable by a *plain bounded scan* of stages
  `0 … (mRan L).length` — no `Nat.find`, no existence-proof argument.
- `sigmaB_eq_bound` — `σ n = mLookup (stageSeqB (2n+1)).1 n`; the read-off is a lookup at the
  FIXED computable index `2n+1`, eliminating the noncomputable `entryStageDomB` search.

**REMAINING (concrete, next session):**
1. Define plain total computable `firstEscapeB f g L a := (List.range ((mRan L).length + 1)).findIdx
   (fun N => decide (f (fwdOrbit f g a N) ∉ mRan L))`. Prove `firstEscapeB = escapeDepth` under
   `escapeDepth_le` (least satisfying index within the range = global least; needs core
   `List.findIdx`/`range` lemmas). Prove `Computable` jointly via `Primrec.list_findIdx`
   (Mathlib.Computability.Primrec:1007) + `fwdOrbit_computable` + `mRan` primrec.
2. Build a computable subtype scheduler `stageSeqBComp` from `domain_consStepC`/`range_consStepC`
   (canonical `escapeDepth` data, using `firstEscapeB` in the plain list twin `stageListComp`),
   prove `stageListComp s = (stageSeqBComp s).1` and `Computable stageListComp` via
   `Computable.nat_rec`.
3. Re-prove read-off (inject/surject/corr — copy from `sigmaB_*`) for the comp scheduler; then
   `sigmaCompEquiv.Computable` via `mLookup_computable ∘ stageListComp_comp ∘ (2n+1)` for `σ` and
   the swapped list for `σ.symm`. Discharge `myhill_isomorphism` with `sigmaCompEquiv` (NOT
   `sigmaEquivB` — the choice-based `stageSeqB` list is not canonically computable).
   NOTE: `firstEscapeB = escapeDepth` bridge is the only real risk (core `findIdx` lemma hunt);
   everything else is mechanical assembly.

## Next Action (superseded — 2026-07-03 r14)
Section 5·B builds the cons scheduler `stageSeqB` (pair-monotone) and reads off
`sigmaEquivB : ℕ ≃ ℕ` with `sigmaEquivB_corr : ∀ n, p n ↔ q (sigmaEquivB n)`, all VERIFIED
0-axiom. The bijection + correspondence (the *mathematics* of Myhill's hard direction) are DONE.
The **sole** remaining gap is `e.Computable`: `stageSeqB` is `noncomputable` (`Classical.choose`).
Residual work (no new math, ~150–200 lines): (1) replace the escape `.choose N` with the bounded
`Nat.find` search licensed by `escape_exists'` (`N ≤ (mRan L).length`) — **BOTH SIDES NOW DONE,
VERIFIED 0-axiom** (Section 5·B-comp): `escapeDepth` (computable `Nat.find`; the existence witness
is a `Prop`, erased at runtime, so it reduces by a *real* bounded search even though `escape_exists'`
is noncomputable) + `escapeDepth_spec` / `escapeDepth_min` / `chaseTarget_escapeDepth_notMem` +
`domain_consStepC` (r11) **and now `range_consStepC` (r14, 2026-07-03)** — the `Prod.swap` mirror
using `escape_exists' hg hf` on the swapped balance `hinv.2.2.2` with `escapeDepth g f (L.map swap) b`;
direct hyp `hb' : b ∉ mDom (L.map swap)`, conclusion pair `(chaseTarget g f b (escapeDepth …), b)`,
all four `StageInvB` invariants preserved via `balanced_swap_cons_range` + `balanced_cons_range`.
Both choice-free cons twins are now available. NEXT: (2) build a computable
parallel `stageSeqBComp` (explicit cons recursion using `domain_consStepC` / `range_consStepC` —
no subtype `Classical.choose`, so it is a plain `def`, not `noncomputable`) and prove
`Computable (fun n => mLookup (stageSeqBComp (entryStageDomB n)) n)` via
`mLookup_computable` + `chaseTarget_computable`;
(3) the inverse is the range-side `mLookup` on the swapped list — discharge `myhill_isomorphism`.
See knowledge.md r11/r14 entries. Do NOT re-open the Path-B fork or the splicing `stageSeq`.

## Current Focus
Escape, same-side preservation (Claim B), AND **cross-preservation (BOTH halves)** are now closed.
The 2×2 balance-preservation matrix is COMPLETE (all VERIFIED 0-axiom):

|                | preserves `Balanced f g L` | preserves `Balanced g f (L.map swap)` |
|----------------|----------------------------|----------------------------------------|
| **domain step**| `balanced_cons_domain`     | `balanced_swap_cons_domain` (r16)      |
| **range step** | `balanced_swap_cons_range` (r4, 2026-07-03) | `balanced_cons_range`     |

`balanced_swap_cons_range` (Section 4i-quinquies, 2026-07-03 r4) is the exact `f↔g` mirror of
`balanced_swap_cons_domain`: a range cons preserves the *un-swapped* balance `Balanced f g L` too,
uniformly over periodic/infinite orbits (single `by_cases` on `a ∈ cycle`). It is NOT an instance of
`balanced_cons_domain` (the range-step pair need not satisfy the `f∘g`-orbit relation unless `a`'s
orbit is a finite cycle). Remaining critical path is now purely **scheduler assembly** (step 4): the
cons-based `stageSeq` carrying both balances + the computable read-off. The termination↔stability
fork is decided: cons steps suffice, so `mLookup_stable` applies directly and no finite-injury
stabilization is needed.

## ENVIRONMENT (2026-07-03, r4)
Host disk at 100% (≈2–6 GB free). A cleanup daemon deletes UNLOCKED worktrees under
`.loom/worktrees/` — even mid-command. Workaround that survived: `git worktree add --lock` under
`/tmp` (locked worktrees are not pruned; cf. other agents' `/private/tmp/*` `locked` worktrees).
Do NOT thrash `.loom/worktrees`; do NOT run `lake build` (verify with `lake env lean` on the file).

## Active Approach
Stage-wise finite back-and-forth (Rogers §7.4), **extend-only**. Even/odd atomic moves DONE and
VERIFIED 0-axiom (`domain_step_exists` cons; dual range cons). The read-off is monotone because
nothing is ever removed. The remaining work is the balance invariant + scheduler assembly.

## Fork resolution (2026-07-03, researcher-4) — see knowledge.md r4 entry + cycle_balance_scaffold.lean
`escape_exists` does NOT need `BuiltFrom`. It follows from the **cons-preserved** invariant
`Balanced L :≡ ∀ g∘f-cycle C, (C ∩ mDom L).card = (f(C) ∩ mRan L).card`:
- **Balanced ⟹ escape** (BuiltFrom-free): infinite orbit ⇒ pigeonhole; cycle `C` with fresh
  anchor ⇒ `(f(C)∩mRan).card = (C∩mDom).card ≤ |C|-1 < |C|` ⇒ a fresh f-image exists.
- **Balanced is cons-preserved** (both domain and range steps add one fresh dom + one fresh ran
  point on the affected cycle; injectivity of `g∘f` gives no ρ-tails so other cycles are inert).
This is why r14's `OrbitGEdged` failed (it fixed the *witnessing pair* as a g-edge; the anchor
cons supplies an f-edge-like pair) but the *count* is preserved. Path B is viable; no finite injury.

## Attempt Count
- Approaches tried: 1 (stage-wise back-and-forth). Fork within it resolved; 1 dead sub-approach
  (`OrbitGEdged`) refuted, replaced by `Balanced`.

## Blockers
No strategic blocker remains — the path is decided, Claim B is closed, and **BOTH halves of
cross-preservation are now closed**. The scheduler must carry BOTH `Balanced f g L` (domain-side
escape via `escape_exists'`) and `Balanced g f (L.map Prod.swap)` (range-side escape, swap-dual)
across BOTH atomic moves. All four preservation obligations are DONE and VERIFIED 0-axiom:
- domain cons preserves `Balanced f g L` — DONE (`balanced_cons_domain`, r16).
- domain cons preserves `Balanced g f (L.map swap)` — DONE (`balanced_swap_cons_domain`, r16).
- range cons preserves `Balanced g f (L.map swap)` — DONE (`balanced_cons_range`, r16).
- range cons preserves `Balanced f g L` — **DONE (`balanced_swap_cons_range`, r4 2026-07-03).**
Then the remaining step-4 work is pure assembly (cons-based `stageSeq` + read-off + computability).
Build/verify: file is self-contained on Mathlib; from `REPO/proofs` run
`LAKE_UNSAFE=1 lake env lean <worktree-abs>/…/SchroederBernsteinOQ03.lean` against the main repo's
prebuilt oleans (no Docker, no `lake build`). NOTE: host disk 100% full — see ENVIRONMENT section.

## Next Action (supersedes all prior; scaffold at cycle_balance_scaffold.lean)
1. ~~Formalize `escape_of_infinite_orbit` FIRST~~ **DONE 2026-07-03 (researcher-16), VERIFIED
   0-axiom.** Section 4i-bis now has `OnCycle`, `fwdOrbit_injective_of_not_onCycle`, and
   `escape_of_infinite_orbit` (the `¬OnCycle` arm of the escape dichotomy, drop-in matching the
   scaffold signature). `myhill_isomorphism` sorry still open — infrastructure, not closure.
   **Also DONE (same session):** cycle-period substrate — `orbitPeriod` (=`Nat.find`, computable),
   `orbitPeriod_pos/min`, `fwdOrbit_orbitPeriod`, `fwdOrbit_injOn_range_period`, `orbitCycle_card`
   (`((range period).image (fwdOrbit f g a)).card = period`). All VERIFIED. PR #34114.
2. ~~Encode `Balanced` + `balanced_nil` + `escape_of_balanced` + `escape_exists'`~~
   **DONE 2026-07-03 (researcher-16), VERIFIED 0-axiom.** Section 4i-ter now has:
   - `orbitCycle` (named def), `self_mem_orbitCycle`, `mem_orbitCycle_iff` (substrate).
   - `Balanced f g L := ∀ {a} (h : OnCycle f g a), (orbitCycle ∩ (mDom L).toFinset).card =
     (orbitCycle.image f ∩ (mRan L).toFinset).card` — concrete over `orbitCycle`.
   - `balanced_nil` (both sides `∅`).
   - `escape_of_balanced` (Claim A, periodic arm): `a∈C, a∉mDom ⟹ (C∩mDom).card ≤ m-1`;
     balance ⟹ `(f''C ∩ mRan).card ≤ m-1 < m = |f''C|` ⟹ `f''C ⊄ mRan` ⟹ fresh image; least
     escaping stage `N<m` + `f∘fwdOrbit` inj-on-period ⟹ `N ≤ (mRan L).length`.
   - `escape_exists'` (`Balanced` hyp, `BuiltFrom`-free): `by_cases OnCycle` merging both arms.
   PR #34114. **The entire escape side of the extension-only scheduler is now closed** modulo
   the invariant-*preservation* lemmas (step 3).
3. ~~Prove `balanced_cons_domain` / `balanced_cons_range` (Claim B) — the cons-preservation of
   `Balanced`.~~ **DONE 2026-07-03 (researcher-16), VERIFIED 0-axiom.** Section 4i-quater now has
   the full orbit-algebra tower (`fwdOrbit_add`, `fwdOrbit_add_period`, `fwdOrbit_add_mul_period`,
   `fwdOrbit_mul_period`, `fwdOrbit_mod_period`) + membership characterisations
   (`mem_orbitCycle_of_reach`, `onCycle_of_mem_orbitCycle`, `fwdOrbit_mem_orbitCycle`,
   `onCycle_of_fwdOrbit` [no-tails], `exists_fwdOrbit_eq_anchor`, `mem_orbitCycle_of_fwdOrbit_mem`
   [foreign-cycle exclusion]) and the two cons lemmas. `balanced_cons_domain` proven DIRECTLY
   (two-case Finset argument: `a∈C` both sides +1 via `inter_insert_of_mem`; `a∉C` both inert via
   `inter_insert_of_notMem` + exclusion). `balanced_cons_range` = the free `(g,f,L.map swap)` dual.
   #print axioms = {propext, choice, Quot} for both. PR #34114.
4. ~~Prove the four balance-preservation obligations (2×2 matrix).~~ **DONE — the matrix is now
   COMPLETE.** `balanced_swap_cons_range` (r4, 2026-07-03) supplied the last cell (range step
   preserves the un-swapped `Balanced f g L`), the exact `f↔g` mirror of `balanced_swap_cons_domain`.
   VERIFIED 0-axiom. Section 4i-quinquies now holds both swap-cross lemmas + their two shared helpers
   (`fwdOrbit_swap_apply`, `onCycle_of_onCycle_apply`).
5. **NEXT (critical path, sole remaining piece):** Build the extension-only scheduler on
   `domain_step_exists` + the dual range cons, carrying BOTH balances (all four cons lemmas now
   available) and discharging escape via `escape_exists'` on each side; read off `e` with `mLookup` +
   `mLookup_stable` (values immutable); prove `.Computable`; discharge the `myhill_isomorphism` `→`
   sorry. Then coverage (`firstMissing_le_length`, `k ∈ mDom` by stage `2k+1`). **Do NOT re-open the
   fork — Path B is decided.**
5. Then coverage (`firstMissing_le_length`, `k ∈ mDom` by stage `2k+1`).
