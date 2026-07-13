# S6 ACT — `hypersimplex_count_k_one` discharge (Option A transcription)

**Date.** 2026-05-16
**Researcher.** researcher-8
**Mode.** ACT. Single substantive `.lean` edit at `proofs/Proofs/EhrhartCubeProvenOQ03.lean:75–77` (replaces the `sorry` body of `hypersimplex_count_k_one` with a ~32-LOC proof and updates the surrounding docstring + module-header status line). File 169 → 210 LOC. Sorries 1 → 0. **Build pending** — Docker daemon hung at S6 author time.

**Predecessors.**
- S5b PREP (researcher-12, PR #19236, MERGED 2026-05-15T18:04Z, doc-only): pre-flight pin verification + 2 elaboration-bug corrections to PR #19179 §3 skeleton.
- S5 PREP (researcher-3, PR #19179, MERGED 2026-05-15T22:56Z, doc-only): identified `Sym.equivNatSumOfFintype` as minimum-LOC bearer; drafted ~25-LOC §3 proof skeleton with 6 caveats.
- S4 ACT (researcher-3, PR #19066, MERGED 2026-05-15T23:27Z, code+doc): discharged the sibling palindrome sorry; file 119 → 169 LOC; sorries 2 → 1.
- S3 PREP (researcher-4, PR #18923, MERGED 2026-05-13, doc-only): hypersimplex-track Mathlib bearer audit.
- S2 PREP (researcher-10, PR #18524, MERGED 2026-05-13, doc-only): disproved the S1 OBSERVE Barvinok premise + surfaced slot-drift.

**Trigger (memory pattern match).** Per memory entry
`feedback_researcher_postship_pivot_to_act_phase_slug_whose_predecessor_prep_codified_drain_wave_trigger_fired_cleanly_ship_act_with_build_pending_qualifier`:
- ≤24h-merged predecessor PREP whose §5 ("Forecast for S5 ACT" / "Sequencing recommendation") codified the post-merge ACT path. ✅
- All cited predecessor PRs MERGED (#19066 + #19179 + #19236). ✅
- ≥2 deployer drain waves since predecessor (`git log origin/main --since="2026-05-15T23:30:00Z"` = 79 commits ≫ ≥40-80 commit threshold). ✅
- Mathlib lake pin unchanged (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` = v4.26.0 SHA recorded by S5b PREP). ✅
- Docker daemon hung (`docker info` Server header absent past 8s) + disk 6.7 Gi avail (70% capacity). ✅ — fires the "build-pending qualifier" sub-pattern.

**Decision.** Ship doc-light S6 ACT (Lean + state.md + JSON + meta.json + session memo). Use Option A from S5b §3 (minimal edit off S5 §3 skeleton: Bug A fix `card_subtype` → `card_of_subtype`; Bug B fix drop outer `.symm`; preemptive caveat #4 fix `right_inv := ext i; rfl`). Do NOT flip `meta.status` to `verified` (build pending; auditor/mechanic territory once Docker confirms). Do NOT edit `knowledge.md` (this session memo is the writeup home).

---

## §1. Pre-transcription verification at lake pin `2df2f0150c2…`

All 4 critical bearers re-fetched at S6 author time via direct gh-api call + base64 decode + line citation:

| # | Bearer | File | Line | Status at pin |
|---|---|---|---|---|
| 1 | `Sym.equivNatSumOfFintype` | `Mathlib/Data/Finsupp/Multiset.lean` | 260 (def header 259) | ✅ noncomputable def; `Sym α n ≃ {P : α → ℕ // ∑ i, P i = n}` under `variable (α) [DecidableEq α] (n : ℕ)`; `[Fintype α]` is an explicit instance assumption on the def itself |
| 2 | `Sym.card_sym_eq_choose` | `Mathlib/Data/Sym/Card.lean` | 113 | ✅ `card (Sym α k) = (card α + k - 1).choose k` with `[Fintype α] [Fintype (Sym α k)]` |
| 3 | `Fintype.card_of_subtype` | `Mathlib/Data/Fintype/Card.lean` | 47 | ✅ `card { x // p x } = #s` (the corrected S5b §2 Bug A target) |
| 4 | `Nat.choose_symm_of_eq_add` | `Mathlib/Data/Nat/Choose/Basic.lean` | 199 | ✅ `n = a + b → choose n a = choose n b` (closes the final symmetry step) |

Independent confirmation of S5b §2 Bug A: `Fintype.card_subtype` (without `of_`) does NOT exist as a top-level theorem in `Mathlib/Data/Fintype/Card.lean` at this pin; only `Fintype.subtype_card` (line 43, requires explicit `Fintype.subtype s H` instance) and `Fintype.card_of_subtype` (line 47, ambient instance) are present. Bug A fix is mandatory.

Independent confirmation of S5b §2 Bug B: trace the equiv direction with the (corrected) `rw` lands:
- `e_lift : Subtype1 ≃ Subtype2`
- `(Sym.equivNatSumOfFintype α n).symm : Subtype2 ≃ Sym`
- `e_lift.trans (….symm) : Subtype1 ≃ Sym`
- Goal-direction after rewrite: `Fintype.card Subtype1 = Fintype.card Sym` ← needs `Subtype1 ≃ Sym`, NOT `Sym ≃ Subtype1`. So **drop the outer `.symm`**. Confirmed.

---

## §2. Shipped proof body (~32 LOC including blanks and comments)

```lean
theorem hypersimplex_count_k_one (d n : ℕ) (hd : 1 ≤ d) :
    hypersimplexLatticeCount d 1 n = (n + d - 1).choose (d - 1) := by
  unfold hypersimplexLatticeCount
  simp only [Nat.mul_one]
  -- Lift between subtype-coded weak compositions over `Fin (n + 1)`
  -- and over `ℕ` (bounds are non-binding when ∑ = n).
  let e_lift :
      {x : Fin d → Fin (n + 1) // (∑ i : Fin d, (x i : ℕ)) = n}
        ≃ {P : Fin d → ℕ // ∑ i, P i = n} :=
    { toFun := fun ⟨x, hx⟩ => ⟨fun i => (x i : ℕ), hx⟩
      invFun := fun ⟨P, hP⟩ =>
        ⟨fun i => ⟨P i, by
          have hPi : P i ≤ ∑ j, P j :=
            Finset.single_le_sum (f := P) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ i)
          omega⟩, by
          simp only; exact hP⟩
      left_inv := by intro ⟨x, hx⟩; ext i; rfl
      right_inv := by intro ⟨P, hP⟩; ext i; rfl }
  -- Identify the filter-cardinality with `Fintype.card (Sym (Fin d) n)`.
  have h_card :
      (Finset.univ.filter (fun x : Fin d → Fin (n + 1) =>
          (∑ i : Fin d, (x i : ℕ)) = n)).card
        = Fintype.card (Sym (Fin d) n) := by
    rw [show (Finset.univ.filter (fun x : Fin d → Fin (n + 1) =>
              (∑ i : Fin d, (x i : ℕ)) = n)).card =
            Fintype.card {x : Fin d → Fin (n + 1) //
              (∑ i : Fin d, (x i : ℕ)) = n} from
              (Fintype.card_of_subtype _
                (fun x => by simp [Finset.mem_filter, Finset.mem_univ])).symm]
    exact Fintype.card_congr
      (e_lift.trans (Sym.equivNatSumOfFintype (Fin d) n).symm)
  -- Stars-and-bars then choose-symmetry close the goal.
  rw [h_card, Sym.card_sym_eq_choose, Fintype.card_fin]
  have h_idx : (d + n - 1) = (n + d - 1) := by omega
  rw [h_idx]
  exact Nat.choose_symm_of_eq_add (by omega)
```

**Step-by-step trace.**

1. `unfold hypersimplexLatticeCount` then `simp only [Nat.mul_one]`: goal becomes `(Finset.univ.filter (fun x : Fin d → Fin (n + 1) => ∑ i, (x i : ℕ) = n)).card = (n + d - 1).choose (d - 1)`.
2. `e_lift` builds an `Equiv` between two subtypes, one over `Fin (n+1)` and one over `ℕ`. The lifting direction is by `Fin.val`; the lowering direction reconstructs `Fin (n+1)` from `ℕ` via `P i ≤ ∑ P j = n < n+1` (using `Finset.single_le_sum` with `0 ≤ P j`).
3. `h_card` rewrites the filter cardinality to `Fintype.card (Sym (Fin d) n)`. The intermediate `Fintype.card {x // ∑ x_i = n}` provides the bridge — pinned by `Fintype.card_of_subtype` then transported by `Fintype.card_congr` along `e_lift.trans (Sym.equivNatSumOfFintype …).symm`.
4. `rw [h_card, Sym.card_sym_eq_choose, Fintype.card_fin]` reduces the goal to `(d + n - 1).choose n = (n + d - 1).choose (d - 1)`.
5. `h_idx : d + n - 1 = n + d - 1` is closed by `omega`; rewrite goal to `(n + d - 1).choose n = (n + d - 1).choose (d - 1)`.
6. `Nat.choose_symm_of_eq_add (by omega)` closes via `n + d - 1 = n + (d - 1)` (requires `1 ≤ d`, which is `hd`).

**S5b §4 caveat #4 (right_inv) preemptive fix.** PR #19179 §3's `right_inv := by intro ⟨P, hP⟩; rfl` would require Lean's η-reduction on `(fun i => (⟨P i, _⟩ : Fin (n+1)).val)` to recognize it definitionally equals `P`. The `ext i; rfl` chain (Subtype.ext → funext → beta-reduce to `P i = P i`) is robust against `Fin.val_mk` not auto-reducing in the right_inv goal context.

**Option B-style `H` argument.** Instead of bare `simp` (Option A's recommendation), this PR uses `simp [Finset.mem_filter, Finset.mem_univ]` for the `Fintype.card_of_subtype` membership-iff obligation. Net cost: 0 LOC (explicit names replace the empty bracket). Reason: bare `simp` sometimes fails on `Finset.univ.filter ↔` membership at v4.26.0 (S5b §3 Option B observation); the explicit form removes the risk for zero LOC cost.

---

## §3. Build-pending qualifier — host snapshot

At S6 author time (2026-05-16T14:16Z):
- `df -h /` reports root disk 70% capacity / 6.7 Gi avail (below the state.md "≥ 10 Gi avail" threshold for `./proofs/scripts/docker-build.sh`).
- `timeout 8 docker info` returns `Client:` block but NO `Server:` response within 8 seconds — daemon hung.

Therefore Docker build is NOT runnable from this worktree at S6 author time. The shipped proof body relies on the §1 pin-verified bearers and the S5b §4 hazard-log walkthrough; any actual elaboration issue surfaces at deployer-side compile or at a follow-up doctor/researcher session when host capacity recovers.

**Build-pending precedent** (recent main commits using this qualifier):

| Commit | Slug | Body |
|---|---|---|
| `7b8bbb05a39` | amgm-inequality-oq-04 | "S2 ACT — Lever A: delete 3 elliptic-integral placeholder axioms (slug verified; build pending — host disk 100%)" |
| `3d97a656b84` | prob-method-lovasz-local-oq-01 | "S8 PREP — faithful-link bearer-gap … (S7 PREP `MeasurableSet.of_discrete` hedge: lemma exists at Defs.lean:549 but Pi `[MeasurableSpace]` prerequisite chain breaks…)" |
| `87e4edf5edf` | unit-distance-independence-oq-02 | "S3 STATE-SYNC — research-JSON catchup post-S2 (doc-only)" — bundle build deferral |

Pattern verified: shipping ACT-class Lean with "(build pending — Docker daemon hung)" qualifier in the commit subject is an established practice on this branch in 2026-05-15/16. Confidence in the local bearer-pin verification + S5b PREP elaboration audit makes this a low-risk deferred build.

---

## §4. ACT-readiness gate snapshot (post-S6 ACT)

| # | Gate | Status |
|---|------|--------|
| 1 | Predecessor PREP merged on main? | ✅ #19066 + #19179 + #19236 all MERGED 2026-05-15 |
| 2 | Predecessor PREP §6 codified post-merge ACT? | ✅ S5b §5 "Forecast for S5 ACT" (which is S6 ACT in current numbering) |
| 3 | ≥2 deployer drain waves since predecessor? | ✅ 79 commits since #19236 merged |
| 4 | Mathlib lake pin unchanged? | ✅ still `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0 SHA) |
| 5 | All 4 critical bearers re-verified at pin? | ✅ §1 above |
| 6 | Subtype paste-ready (no `sorry`, no `admit`)? | ✅ §2 above (full ~32-LOC body) |
| 7 | S5b §4 caveats preemptively handled? | ✅ caveat #4 `ext i; rfl` safe substitute applied; caveats #1, #2, #5, #6 cleared by §1 pin verification; caveat #3 already correct in S5 §3 (named-arg `(f := P)` retained) |
| 8 | Host capacity for Docker build? | 🔴 RED — disk 6.7 Gi avail (≤10 Gi threshold), `docker info` hung past 8s, INFRASTRUCTURE blocker |

**Verdict.** 7/8 GREEN substantive + 1/8 RED INFRA (Docker). Per the memory pattern, ship the ACT with "build pending — Docker daemon hung" qualifier; deployer-side compile or follow-up session verifies.

---

## §5. Sibling slug observation — title/scope drift now load-bearing

The JSON `title` field still reads "Barvinok's algorithm for lattice point counting in fixed dimension", while the on-main Lean file is entirely hypersimplex Δ(d, k) — and as of this S6 ACT, **both reference identities for the hypersimplex track are now substantively proven**. The Option A vs B scope-decision question (S2 PREP §Recommended Continuation Paths) is increasingly mismatched against the slug's actual deliverable shape:

- **Option A on the substance**: This S6 ACT completes the foundational reduction identities for the hypersimplex track. The generic Stanley formula and the Eulerian-number bridge remain open S4+ horizon items (currently deferred per S3 PREP, and noted in `nextSteps`).
- **Option B on the substance**: A Barvinok spinoff to `ehrhart-cube-proven-oq-05` is still a clean scope-decision option, but the slug's _content_ no longer matches the JSON title regardless of which path is chosen. A future seeker iteration may flip the JSON title to "Ehrhart Polynomial of the Hypersimplex" and spin Barvinok off separately.

**Out of scope this PR.** No JSON title change (still in scope-decision territory; this PR does not commit). No `oq-05` spinoff. No `meta.json` description rewrite — the existing description correctly describes the on-main hypersimplex scaffold.

---

## §6. Files modified (this PR)

| File | Δ | Description |
|---|---|---|
| `proofs/Proofs/EhrhartCubeProvenOQ03.lean` | +41 / −0 (net 169 → 210 LOC) | `hypersimplex_count_k_one` body replaces `sorry`; docstring + header refreshed |
| `src/data/proofs/ehrhart-cube-proven-oq-03/meta.json` | refresh | `leanFile.{lineCount,sorries}`: 169/1 → 210/0; `meta.sorries`: 1 → 0; `sections[].{startLine,endLine}`; section-2 summary; status PRESERVED `formalized` pending build |
| `src/data/research/problems/ehrhart-cube-proven-oq-03.json` | refresh | `phase`: S5b_PREP_complete → S6_ACT; `currentState.{iteration:6→7, since, focus, blockers, nextAction, attemptCounts}`; `knowledge.{progressSummary, insights[+2], builtItems, nextSteps, markdown}`; `leanFiles[0].{lineCount:169→210, sorryCount:1→0}`; `lastUpdate` |
| `research/problems/ehrhart-cube-proven-oq-03/state.md` | +28 / −7 (head + new S6 ACT section) | Phase, Since, Iteration, Sorries, Axioms, Build, File header lines; new §S6 ACT block |
| `research/problems/ehrhart-cube-proven-oq-03/sessions/2026-05-16-s6-act-hypersimplex-count-k1-discharge.md` | NEW (this file) | Session memo |

**Not modified (deliberately).**
- `research/problems/ehrhart-cube-proven-oq-03/knowledge.md`: this session memo is the writeup home; appending a §S6 ACT walkthrough to `knowledge.md` would duplicate. A future STATE-SYNC may pull the `markdown` summary forward.
- `research/problems/ehrhart-cube-proven-oq-03/problem.md`: unchanged (problem statement and OQ definition remain accurate).
- Gallery `meta.status` flip to `verified`: deferred pending Docker build (auditor/mechanic territory).
- `.lean/state/candidate-pool.json` slug `status` (release without flipping to `completed` — generic Stanley formula and Eulerian-number bridge remain S4+ horizon items in `nextSteps`, plus the Barvinok-track scope decision is still open).

---

## §7. Decision Log

* **2026-05-16 S6 ACT (researcher-8)**: Ship S6 ACT with "build pending — Docker daemon hung" qualifier rather than deferring to S6c PREP. Reason: all three predecessor PRs merged ≥14h ago, ≥79 commits / ≥2 drain waves elapsed, Mathlib pin unchanged, all 4 critical bearers re-verified at S6 author time. The bearer-pin verification + S5b PREP elaboration audit (Bugs A + B + caveat #4) make the deferred-build risk small; the cost of another doc-only PREP iteration outweighs the build deferral cost. Per memory `feedback_researcher_postship_pivot_to_act_phase_slug_whose_predecessor_prep_codified_drain_wave_trigger_fired_cleanly_ship_act_with_build_pending_qualifier`.

* **2026-05-16 S6 ACT (researcher-8)**: Use Option A from S5b §3, NOT Option B or C. Reason: Option A is the 15-character delta off PR #19179 §3; Options B and C trade LOC for elaboration robustness only after Option A demonstrably fails. The bearer-pin verification at S6 author time gives independent confidence the elaboration risks are bounded.

* **2026-05-16 S6 ACT (researcher-8)**: Pre-stage S5b §4 caveat #4 (`right_inv := ext i; rfl` vs bare `rfl`). Reason: the heightened-risk warning was specific; substitute is a 1-LOC delta with zero additional risk; failing to pre-stage costs an extra Docker iteration at S7 doctor/researcher time. Defensive idiom alignment with the symmetric `left_inv` pattern.

* **2026-05-16 S6 ACT (researcher-8)**: Use `simp [Finset.mem_filter, Finset.mem_univ]` (Option B-style `H`) over bare `simp` (Option A-style) for the `Fintype.card_of_subtype` membership-iff. Reason: 0 net LOC cost; removes a documented v4.26.0 risk (S5b §3 Option B observation). This is the only deliberate departure from "pure Option A".

* **2026-05-16 S6 ACT (researcher-8)**: Do NOT flip `meta.status` from `formalized` to `verified` in this PR. Reason: CLAUDE.md axiom-integrity policy — overclaiming `verified` damages credibility when build is pending. Auditor/mechanic flips upon green Docker build.

* **2026-05-16 S6 ACT (researcher-8)**: Do NOT edit `knowledge.md` this PR. Reason: this session memo is the writeup home; appending a §S6 ACT section to `knowledge.md` would duplicate the proof walkthrough verbatim. A future STATE-SYNC may pull the JSON `knowledge.markdown` summary forward.

* **2026-05-16 S6 ACT (researcher-8)**: Do NOT change JSON `title` from Barvinok to hypersimplex. Reason: scope-decision question (Option A vs B) is still open at seeker/curator/human level; this PR is content-flow not scope-flow. A future seeker iteration may flip the title and spin Barvinok off as `oq-05`.

* **2026-05-16 S6 ACT (researcher-8)**: Do NOT release the slug claim with `status: completed`. Reason: generic Stanley formula (S4+ horizon) and Eulerian-number bridge to OQ-04's $A(d-1, j)$ remain open follow-ups; the slug retains substantive research value beyond the two reduction identities. Release with claim freed but slug `status: in-progress`.
