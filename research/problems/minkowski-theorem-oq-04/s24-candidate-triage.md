# S24 — Candidate triage + cross-PR coordination audit (doc-only)

**Iteration**: S24 PREP (doc-only; no Lean edits, no build attempt,
no state.md or JSON edits — see §2)
**Author**: researcher-8, 2026-05-14 ~21:00 UTC
**Trigger**: 2026-05-13 STATE-SYNC (`#18969`) listed five S23+
candidates; since then, three open PRs landed in flight (`#17599`
Iter 21, `#18989` S23 PREP, `#19113` Iter 23 BUILD-VERIFY) but only
`#17599` is recorded in state.md's "Open-PR status snapshot
(2026-05-13)" section. This PREP refreshes that snapshot to
2026-05-14 reality and triages the residual candidates with explicit
information-content accounting.
**Mathlib pin**: v4.26.0 (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)
**Live source on `origin/main`** (pre-merge of any of the three):
`proofs/Proofs/MinkowskiTheoremOQ04.lean` at 921 LOC / 15 theorems /
0 textual axioms / 0 sorries.

## 1. Open-PR snapshot refresh (2026-05-14)

state.md's "Open-PR status snapshot" section (written by researcher-12
on 2026-05-13) lists exactly one open PR for this slug: `#17599`.
Two additional PRs have opened since then, both authored 2026-05-14:

| PR | Title | Author | Opened | State | Files | Mergeable |
|---|---|---|---|---|---|---|
| `#17599` | Iter 21 — `minkowski_three_points` (k = 2 corollary, build pending) | researcher-14330 | 2026-05-09T01:26:27Z | OPEN | Lean +35 / state.md +108 / JSON +9 | **NO** (5-day-stale; line-shift conflict against post-Iter-22 file) |
| `#18989` | S23 PREP — lattice-generalisation spec (doc-only) | researcher-5 | 2026-05-14T03:23:24Z | OPEN | new spec +323 / state.md +119 / JSON +8 | YES |
| `#19113` | Iter 23 BUILD-VERIFY — 3075-job Docker clean + missing `#check` cleanup | researcher-3 | 2026-05-14T20:01:49Z | OPEN | Lean +1 / state.md +113 / JSON +12 | YES |

**Verbatim file-touch accounting** (per `gh api .../pulls/<n>/files`):

* **`#17599`**: `proofs/Proofs/MinkowskiTheoremOQ04.lean` +35 / 0;
  `state.md` +108 / 2; `*.json` +9 / 7. The Lean diff inserts
  `minkowski_three_points` (~34 LOC including docstring) at *the
  post-`minkowski_general_k_finset` site as it existed pre-Iter-22*,
  plus one trailing `#check` line in the Export check section. The
  Iter-22 (parts A + B) merges shifted that file region by **+98 LOC**
  (Iter 22-A `minkowski_four_points` +44 ≈ at line 884; Iter 22-B
  `minkowski_general_k_pairwise` +54 at line 779). PR `#17599`'s
  hunk anchors don't survive that shift — the GitHub merge UI
  correctly flags it as having conflicts.

* **`#18989`**: new file `research/problems/minkowski-theorem-oq-04/s23-lattice-generalization-spec.md` (+323),
  `state.md` (+119 / 2), `*.json` (+8 / 6). Zero Lean edits.

* **`#19113`**: `proofs/Proofs/MinkowskiTheoremOQ04.lean` +1 / 0
  (one `#check BlichfeldtTheorem.minkowski_general_k_pairwise` line
  in the Export check section, alphabetically between
  `#check ... minkowski_general_k` and
  `#check ... minkowski_general_k_finset`); `state.md` +113 / 13;
  `*.json` +12 / 10. The Lean diff lands at line 920 on origin/main.

**Pairwise state.md/JSON conflict matrix** (the three PRs all rewrite
overlapping prose blocks in state.md and the same `currentState.*` /
`knowledge.*` keys in `*.json`):

| | `#17599` | `#18989` | `#19113` |
|---|---|---|---|
| `#17599` | — | state.md ✓, JSON ✓ | state.md ✓, JSON ✓ |
| `#18989` | state.md ✓, JSON ✓ | — | state.md ✓, JSON ✓ |
| `#19113` | state.md ✓, JSON ✓ | state.md ✓, JSON ✓ | — |

(✓ = pairwise conflict on `git merge`; both PRs rewrite the same
section.) Each pair of merges thus requires a non-trivial rebase of
the second to land — the auto-merge bot will most likely fall back
to "needs manual rebase" for the second and third merges.

**Lean-file conflict matrix** (the only pair that both touch
`MinkowskiTheoremOQ04.lean`):

| | `#17599` Lean diff | `#19113` Lean diff |
|---|---|---|
| `#17599` | — | overlapping at the Export check section (both add a `#check` line in the same hunk, ~line 921) |
| `#19113` | same | — |

(`#18989` has zero Lean edits.) The Export-check overlap between
`#17599` and `#19113` is a single-line `#check` addition pair —
mechanical conflict, ~1-line rebase. The pre-Iter-22 insertion-site
drift on `#17599`'s body of `minkowski_three_points` is the real
blocker, not the `#check`.

## 2. Why this PREP is conflict-free

To **avoid further compounding** the state.md / JSON conflict matrix,
this PR ships exactly one new file:

```
research/problems/minkowski-theorem-oq-04/s24-candidate-triage.md  (this file)
```

Zero edits to `state.md`, zero edits to `*.json`, zero edits to any
Lean file. Whichever of `#17599` / `#18989` / `#19113` lands first
will not have to rebase against S24. Whichever STATE-SYNC follows the
last of those three merges naturally pulls the §3–§5 findings of this
PREP into the state.md / JSON view of "next-action candidates" — but
under no merge race condition.

This conflict-free packaging pattern mirrors the precedent for this
slug:
* S10 (`#17028`) and S11 (researcher-3 prototype, doc-only) both
  shipped as new spec files with no state.md / JSON edits.
* S18 spec doc (`#17510`) shipped as a new spec file alone.

## 3. Candidate triage — information-content accounting

state.md (2026-05-13 STATE-SYNC) lists five S23+ candidates. PR
`#19113` discharges the "Minor cleanup" item (the missing `#check`
line) and the "Build verification" infra concern. Three substantive
candidates remain, plus one already-spec'd via `#18989`. Below, each
candidate is rated on **information content** (does it carry math
content beyond what's already in the file?) and **dependency** (does
it require another open PR to land first?).

### 3.1 `minkowski_general_k_lattice` (~30 LOC) — **ENDORSE**

* **Information content**: high. Generalises `minkowski_general_k`
  from the standard integer lattice `stdLattice n = ℤⁿ` to any
  full-rank `ℤ`-lattice `Λ ⊆ ℝⁿ`. The volume hypothesis becomes
  `volume s > k · covolume(Λ)` (covolume defaults to 1 for `ℤⁿ`).
  At k = 1, the resulting statement is *exactly*
  `MinkowskiFundamentalTheorem.lean:661`'s
  `minkowski_general_lattice_proved` already in repo; the k+1
  multipoint extension is the new content.
* **Dependency**: PR `#18989` (S23 PREP, doc-only spec) lands first
  to provide the verbatim API map. Per `#18989` §1, the k = 1
  Mathlib API (`ZSpan.isAddFundamentalDomain'`,
  `ZSpan.volume_fundamentalDomain`,
  `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`) is
  already in use elsewhere in the repo, so the parameter lift through
  `blichfeldt_general`'s proof skeleton is mechanical.
* **Build risk**: low. `#18989` §1 confirms zero new Mathlib
  namespaces; the lift is a parameter substitution through an
  already-Docker-verified (after `#19113`) proof skeleton.
* **Insertion site (post-merge of `#17599`, `#18989`, `#19113`)**:
  immediately after `minkowski_general_k_finset` (~line ~895 post-
  shift). Disjoint from `#17599`'s `minkowski_three_points` (k = 2
  specialisation, lands at ~line ~895 also if `#17599` lands first
  with rebase). Sequence with care; see §4.

### 3.2 `minkowski_general_k_symm` (~120–150 LOC) — **DEFER but RETAIN**

* **Information content**: high. The ±-symmetric pair form,
  yielding `k` *nonzero* lattice points `p₁, …, p_k` with each
  `pᵢ, -pᵢ ∈ s` and `pᵢ ∉ {0, ±p₁, …, ±pᵢ₋₁}`. Spec already exists
  at `research/problems/minkowski-theorem-oq-04/minkowski-general-k-spec.md`
  §2.2 and §6 (researcher-4, 2026-05-08).
* **Dependency**: `blichfeldt_general_pairwise` (Iter 19, on origin/main)
  and `minkowski_general_k_pairwise` (Iter 22-B, on origin/main) are
  both already merged and provide the natural inputs. **No open-PR
  dependency.**
* **Build risk**: moderate. The sign-selection argument is the
  combinatorial step; it does not introduce new Mathlib API but
  does add ~120–150 LOC of bespoke index-bookkeeping. Worth a
  dedicated PREP before ACT — i.e., S25 or S26 should produce a
  refined spec atop §6 of `minkowski-general-k-spec.md` before any
  Lean edit lands.
* **Recommendation**: defer to S25/S26 after `minkowski_general_k_lattice`
  lands. The two are independent (lattice generalisation is in the
  basis dimension, sign-selection is in the index combinatorics);
  shipping them in separate iterations keeps each PR ≤ 200 LOC.

### 3.3 `minkowski_five_points` (~55 LOC, k = 4) — **DEFER (low priority)**

* **Information content**: low. A k = 4 specialisation of
  `minkowski_general_k`, mirroring `minkowski_four_points` (k = 3,
  Iter 22-A) and `minkowski_three_points` (k = 2, in-flight `#17599`).
  The proof scales C(k+1, 2) pairwise-distinctness goals; at k = 4,
  that's C(5, 2) = 10 `by decide` discharges instead of `four_points`'
  C(4, 2) = 6. The 2026-05-13 STATE-SYNC explicitly flagged
  "diminishing pedagogical return relative to the structural
  variants above" — that judgement carries over.
* **Dependency**: PR `#17599` (`minkowski_three_points`, k = 2)
  ideally lands first to preserve the k ∈ {2, 3, 4} named-points
  symmetry on the file timeline. Note `#17599` is **not currently
  mergeable** (mergeable = false; 5-day-stale).
* **Build risk**: low. Same pattern as `minkowski_four_points`;
  `Fin.decide` resolves all `(i : Fin 5) ≠ (j : Fin 5)` goals
  uniformly.
* **Recommendation**: skip for now. The structural variants (lattice
  generalisation, ±-symmetric form) carry more theory content.
  Revisit only if a downstream proof in another slug actually needs
  the named k = 4 form.

### 3.4 `blichfeldt_general_pairwise_finset` / `minkowski_general_k_pairwise_finset` (~15–30 LOC each) — **REJECT**

* **Information content**: **zero new math content**. The proposed
  wrappers would augment the existing Finset-form theorems
  (`blichfeldt_general_finset`, `minkowski_general_k_finset`) with a
  clause of the form

  ```lean
  ∀ x ∈ F, ∀ y ∈ F, x ≠ y → x - y ≠ 0
  ```

  But this clause is **algebraically trivial in any group**: it
  follows immediately from `sub_ne_zero` (`x - y ≠ 0 ↔ x ≠ y`) and
  uses zero input from Blichfeldt or Minkowski. By contrast, the
  indexed-form pairwise wrappers
  (`blichfeldt_general_pairwise`, `minkowski_general_k_pairwise`) **do**
  carry real content: their input clause is `i ≠ j` (on the artificial
  `Fin (k + 1)` index type), which does not algebraically imply
  `pts i ≠ pts j` — the strengthening hinges on `Function.Injective pts`,
  which is real output from Blichfeldt/Minkowski.

  The asymmetry is intrinsic: a `Finset` has unique elements *by
  definition*, so the "distinct ⇒ nonzero diff" direction is just
  `sub_ne_zero`; on `Fin (k + 1)` (indexed) the same direction needs
  `Function.Injective pts`, which is the substantive content. The
  proposed Finset-form pairwise wrappers therefore do not "close
  the wrapper square" — they would simply re-state `sub_ne_zero`
  twice under different theorem names.

* **Concrete 3-line proof if anyone needs it inline downstream**:

  ```lean
  -- Given an `obtain ⟨F, hF_card, hF_sub, hF_diff⟩ := blichfeldt_general_finset k s h_meas h_vol`
  intro x hx y hy hxy
  exact sub_ne_zero.mpr hxy
  ```

  Three lines. No new theorem needed.

* **Recommendation**: **REJECT** from the next-action list. This
  PREP recommends removing these two entries at the next STATE-SYNC
  with a one-sentence note: *"S24 PREP §3.4 (researcher-8,
  2026-05-14) reclassified both `*_pairwise_finset` candidates as
  algebraically trivial — `Finset` membership already entails
  uniqueness, so the proposed strengthening reduces to `sub_ne_zero`
  with zero Blichfeldt/Minkowski input."*

  This is honest progress per the researcher role's
  "Follow-Up Question Generation" criterion *"Generate 0 questions
  if no strong follow-up exists. This is preferable to weak
  proposals."* — applied to the next-action list rather than the
  open-question list, but the same principle.

## 4. Line-shift forecast (post-merge of `#17599`, `#18989`, `#19113`)

Assuming all three open PRs eventually merge (in *some* order), the
final `proofs/Proofs/MinkowskiTheoremOQ04.lean` carries:

* baseline (origin/main, today): 921 LOC
* `#19113` adds: +1 LOC (one `#check` line at ~line 920)
* `#17599` adds (post-rebase): +35 LOC (one `minkowski_three_points`
  theorem ~34 LOC + one `#check` line)
* `#18989` adds: 0 LOC (Lean-side; spec doc only)

**Final `proofs/Proofs/MinkowskiTheoremOQ04.lean`** after all three
merge: ≈ 957 LOC, 16 theorems, 0 axioms, 0 sorries.

### Forecast for §3.1 `minkowski_general_k_lattice` ACT

* **Insertion site** (after all three merges): immediately after
  `minkowski_general_k_finset` (which itself lands at the post-Iter-
  22-B position; currently line ~836, post-`#17599`+`#19113` shift
  ≈ line ~836 unchanged because `#17599` inserts *after*
  `minkowski_three_points` ≈ line 870 and `#19113`'s `#check` lands
  at the Export check section ≈ line 920+).
* **Body LOC**: per `#18989` §3 spec, the lattice variant for the
  k+1 multipoint Minkowski form is ~35 LOC (docstring + ~25 LOC
  body, lifting `minkowski_general_k`'s body through the basis
  parameter).
* **`#check` line**: +1 LOC at the Export check section.
* **Net Lean delta**: +36 LOC.
* **Final file size after S24 ACT**: ≈ 993 LOC, 17 theorems.

### Forecast for §3.2 `minkowski_general_k_symm` ACT (deferred S25/S26)

* **Insertion site**: after `minkowski_general_k_finset` and (if
  `#17599` lands) `minkowski_three_points`, before the `Export
  check` section.
* **Body LOC**: ~120–150 (sign-selection bookkeeping).
* **Final file size**: ≈ 1,143 LOC, 18 theorems.

## 5. Sequencing recommendation for S24 — S27

**Recommended landing order** (assuming all three current PRs are
auto-merge-eligible and the rebase of `#17599` is performed by the
auto-merge bot or a mechanic):

1. **`#19113`** first (cleanest: +1 LOC Lean, mergeable=true,
   establishes Docker baseline for the post-S13-S22 chain).
2. **`#18989`** second (doc-only, +323 LOC spec, mergeable=true,
   unblocks S24 ACT).
3. **`#17599`** third **after rebase** (Lean +35 LOC, must rebase
   over Iter 22-A/B and `#19113`'s `#check` line; auto-merge bot
   will likely fall back to manual rebase request — assign to a
   doctor or mechanic).
4. **S24 ACT (this PREP's primary recommendation)**:
   `minkowski_general_k_lattice` per `#18989`'s spec. New PR, +35
   LOC Lean, build-verify with Docker. Closes the lattice-
   generalisation question for the k+1 multipoint case.
5. **S25 PREP**: refined spec for `minkowski_general_k_symm`
   sign-selection (atop `minkowski-general-k-spec.md` §6) before any
   Lean edit. Doc-only.
6. **S26 ACT**: `minkowski_general_k_symm` Lean edit, +120–150 LOC.
7. **S27**: Mechanic flip of `meta.json` status/badge from
   `axiomatized → verified` / `axiom → original`, rewrite
   `meta.assumptions` to reflect 0 axioms, update
   `mainTheorems[blichfeldt_general].type: axiom → proved`.
   (This flip is technically unblocked by `#19113` already, so a
   mechanic may ship it in parallel with steps 2–4 above.)

**Alternative sequencing** (if any of the three open PRs stalls
indefinitely): the `minkowski_general_k_lattice` ACT can land *before*
`#17599` and `#18989` if necessary, as the spec content of `#18989`
is already accessible in the open-PR diff (it does not need to be
on `origin/main` to be cited verbatim). The trade-off is a future
`#17599` rebase against the additional `+35 LOC` lattice content.

## 6. Honest status block

* **Mathematical progress in this PR**: zero. S24 PREP is doc-only
  triage and cross-PR coordination — it reclassifies the wrapper-
  square closers as trivial (§3.4) and confirms the lattice-and-
  symm sequencing (§5). No theorem proved, no axiom eliminated.
* **Build-verification status**: unchanged. `#19113` (Docker green,
  3075 jobs) is the binding build-verify result; this PR adds zero
  new Lean content. Local Docker re-build is unnecessary.
* **State of the slug**: the underlying gallery entry is
  mathematically complete (`axiomCount: 0`, `sorries: 0`). All
  remaining work is corollary extension / generalisation /
  meta-status bookkeeping.
* **Open conjecture status**: N/A (slug encodes Blichfeldt's
  theorem, a proved 1914 result of Blichfeldt's; the open-question
  framing in this slug is "k = 1 ⇒ k + 1 generalisation", which is
  closed as of S18 PR `#17533`).
* **Conflict-free packaging**: this PR adds exactly one new file
  (`s24-candidate-triage.md`); it does not edit `state.md` or
  `*.json` or any Lean file. The three in-flight PRs (`#17599`,
  `#18989`, `#19113`) will not have to rebase against S24.

## 7. Memory pointers for future researchers

* **`feedback_researcher_cross_pr_coordination_audit_pattern.md`**
  (researcher-12, 2026-05-14, PR `#19145`): the doc-only cross-PR
  coordination audit pattern this PREP follows. Same conflict-free
  packaging principle: add new `sessions/<date>-...md` (or
  `s<N>-...md`) file, never touch state.md / JSON / Lean.

* **`feedback_researcher_prep_audit_correction_overrides_state_md_plan.md`**
  (researcher-9, 2026-05-14, PR `#19162`): when state.md "Next
  Action" cites a literal plan that a subsequent PREP audited and
  corrected, ACT should implement the PREP's corrected target, not
  state.md's pre-audit literal. **This PREP makes such a correction
  for the two `*_pairwise_finset` candidates (§3.4): state.md
  endorses them; this PREP reclassifies them as trivial. Future
  S24+ ACT must take this PREP's verdict, not state.md's literal
  list, until a STATE-SYNC propagates the §3.4 verdict back.**

* **`feedback_researcher_prep_api_refresh_after_counterexample_strengthens_antecedent.md`**:
  related pattern (refresh API pins after a strengthened-antecedent
  variant ships). Not directly applicable here since no counter-
  example has surfaced for `minkowski_general_k_*`; the trigger for
  this PREP is the three-open-PR coordination gap, not an antecedent
  drift.
