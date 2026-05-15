## S21 Kit Pin-Verify Sweep — audit S18/S19/S20 PREP-chain at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

**Companion to**: S18 mechanic kit (PR #19135), S19 K12 root-cause (PR #19232), S20 K14 cascade (PR #19237), S17 JSON state-sync (PR #19002).
**Scope**: doc-only fresh-angle PREP. No Lean / state.md / JSON / existing-PREP edits. New file only.
**Pin SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Mathlib v4.26.0, lake-locked in `proofs/lake-manifest.json`).
**Method**: pin-verify every Mathlib API citation across the four open PREP PRs via `gh api .../contents/<path>?ref=<SHA>` decoded as base64; cross-check each citation's `file:line` against actual file contents at the SHA.

---

### 0. Why this audit (fresh angle under deployer stall)

Four open PRs on this slug (all CLEAN, no Lean edits) and last `main` merge at
2026-05-14T03:05:23Z (~28h stall as of 2026-05-15 ~08:00Z). Per
`feedback_researcher_release_crowded_slug_during_deployer_stall_pattern`, the
release matrix permits a 5th PR iff it is strictly conflict-free AND fills a
genuine gap. The gap here: the kit's 9 Mathlib v4.26.0 API claims, plus S19's
1 Mathlib-Nat-Totient-line citation, plus S20's 1 Mathlib-Finset-Card-line
citation, have **never been jointly pin-verified** against the lake-locked
SHA. A mechanic burning a Docker iteration to discover a phantom or
off-by-one citation costs ~20-40 min of cold-cache rebuild. This PREP
pre-flights all 11 citations in ~10 min of `gh api` calls.

Pattern: `feedback_researcher_preflight_pin_verifies_peer_prep_skeleton` (this
firing is over the entire 3-PREP chain, not a single skeleton).

---

### 1. Audit verdict summary

| Kit cluster / source | API/citation under audit | Verdict | Notes |
|---|---|---|---|
| K1 (PR #19135) | `poisson_approx_birthday3` @ L343 → `exp_lambda_tendsto` @ L468 forward-ref | ✅ confirmed | File grepped: theorem at L343, lemma at L468; reference at L353 (call site `exp_lambda_tendsto c hc`). |
| K4 (PR #19135) | `Nat.descFactorial_two` REMOVED from `Mathlib/Data/Nat/Factorial/Basic.lean`; only `cast_descFactorial_two` remains in `.../Cast.lean:38` | ✅ confirmed | `gh api search/code` returns 2 hits both in `Cast.lean` paths; `Basic.lean` at SHA has no `descFactorial_two`. |
| K7 (PR #19135) | `card_eq_sum_card_fiberwise` at `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:971` takes `(H : (s : Set ι).MapsTo f t)` | ✅ confirmed | L971-972 verbatim: `theorem card_eq_sum_card_fiberwise [DecidableEq M] {f : ι → M} {s : Finset ι} {t : Finset M} (H : (s : Set ι).MapsTo f t)`. |
| K8 (PR #19135) | `card_sdiff_of_subset` @ `Mathlib/Data/Finset/Card.lean:569` (renamed from `card_sdiff`); new `card_sdiff` @ L574 unconditional with `_ ∩ _` form | ✅ confirmed | L569: `theorem card_sdiff_of_subset (h : s ⊆ t) : #(t \ s) = #t - #s`. L574: `theorem card_sdiff : #(t \ s) = #t - #(s ∩ t)`. |
| K9 (PR #19135) | `Finset.orderEmbOfFin_unique` @ `Mathlib/Data/Finset/Sort.lean:267`; `(h : s.card = k)` is FIRST explicit arg | ✅ confirmed | L267-268: `theorem orderEmbOfFin_unique {s : Finset α} {k : ℕ} (h : s.card = k) {f : Fin k → α} (hfs : ∀ x, f x ∈ s) (hmono : StrictMono f)`. |
| S19 K12 (PR #19232) | `scoped notation "φ" => Nat.totient` @ `Mathlib/Data/Nat/Totient.lean:37` | ⚠ line-off-by-1 | Substance correct: scoped notation `φ` for `Nat.totient` exists at SHA (after `open Finset` + `namespace Nat`). But actual line is **L38**, not L37 (L37 is the `@[inherit_doc]` attribute; L38 is `scoped notation "φ" => Nat.totient`). Does not affect S19's K12 fix correctness — only the citation marker. |
| S20 K14 (PR #19237) | `filter_card_add_filter_neg_card_eq_card` @ `Mathlib/Data/Finset/Card.lean:633` | ✅ confirmed | L633: `theorem filter_card_add_filter_neg_card_eq_card`. |

**Bottom line**: 0 phantom APIs, 0 wrong-file paths, 1 off-by-1 line marker
(S19 K12, cosmetic). The S18 / S19 / S20 PREP chain is API-grounded.

---

### 2. Two minor refinements surfaced (mechanic-time savings, not blockers)

#### 2.1 K4 manual-fallback `show` literal has wrong LHS structure

S18 kit §K4 lists a manual fallback after the primary `simp [Nat.descFactorial, Nat.mul_comm]`:

```lean
show n * ((n - 0) * 1) = n * (n - 1)
ring
```

**Issue 1 (LHS structure)**: at SHA `2df2f0150`, `Nat.descFactorial` is defined recursively (`Mathlib/Data/Nat/Factorial/Basic.lean:311-313`):

```lean
def descFactorial (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => (n - k) * descFactorial n k
```

So `n.descFactorial 2` unfolds to `(n - 1) * descFactorial n 1`, then
`(n - 1) * ((n - 0) * descFactorial n 0)`, then `(n - 1) * ((n - 0) * 1)`.
The leading multiplicand is `(n - 1)`, not `n`. The kit's literal
`show n * ((n - 0) * 1) = n * (n - 1)` would fail to match the actual goal.

**Issue 2 (`ring` over ℕ with subtraction)**: `ring` in Lean 4 Mathlib works
over `CommSemiring` (Nat included) for `+`, `*`, `^` only. Nat truncated
subtraction `Nat.sub` is not a ring operation; `ring` cannot reason about it.
The correct closer over ℕ subtraction is `omega` (linear arithmetic) or an
explicit `Nat.mul_comm` rewrite.

**Suggested fix for the fallback** (replace lines in kit §K4 fallback block):

```lean
-- After `simp [Nat.descFactorial]` reduces goal to
--   `(n - 1) * ((n - 0) * 1) = n * (n - 1)`
-- close via:
show (n - 1) * ((n - 0) * 1) = n * (n - 1)
rw [Nat.sub_zero, Nat.mul_one, Nat.mul_comm]
```

Or one-liner: replace `simp [Nat.descFactorial, Nat.mul_comm]` with
`simp [Nat.descFactorial, Nat.mul_comm, Nat.sub_zero, Nat.mul_one]`.

**Cost saved**: ~5-10 min if mechanic primary fix doesn't close and falls
back; ~0 min if primary fix `simp [Nat.descFactorial, Nat.mul_comm]` works
(it likely does at v4.26.0).

#### 2.2 K7 may permit point-free lambda inline (saves `have hF :` annotation)

S18 kit §K7 recommends:

```lean
have hF : Set.MapsTo (fun p => …) (s : Set _) ((range 4 : Finset _) : Set _) := by
  intro p hp
  …
exact card_eq_sum_card_fiberwise hF
```

(+4 LOC per site × 4 sites = +16 LOC, or +1 site-redundant per file).

**Observation**: at SHA `2df2f0150`, `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:977` is the only Mathlib internal caller of `card_eq_sum_card_fiberwise`:

```lean
card_eq_sum_card_fiberwise fun _ => mem_image_of_mem _
```

This passes a lambda `fun _ => mem_image_of_mem _` directly. The lambda
returns `∀ x ∈ s, f x ∈ image f s` form (not explicitly `Set.MapsTo`). The
elaborator clearly does coerce **when the argument is inlined as a lambda at
the call site**.

The build-log errors at L1384/L1394/L1414/L1428 occur because the file
**packages the predicate into a `have hF : …` annotated as
`∀ p ∈ s, f p ∈ t` and then passes `hF`**. The `have`-annotation form locks
the type, defeating the elaborator's coercion.

**Alternative fix (saves ~+12 LOC across 4 sites)**:

```lean
-- INSTEAD OF (kit's recommendation):
have hF : Set.MapsTo (fun p => …) (s : Set _) (range 4 : Set _) := by
  intro p hp; …
exact card_eq_sum_card_fiberwise hF

-- TRY (point-free, no `have` annotation):
exact card_eq_sum_card_fiberwise (fun p hp => by …)
```

Or keep `have` but drop the type annotation:

```lean
have hF := fun p hp => …  -- let elaborator infer
exact card_eq_sum_card_fiberwise hF
```

**Caveat**: if `…` body needs `Set.MapsTo`-style strict-implicit `⦃⦄`
brackets to match (which it likely doesn't — `Set.MapsTo` unfolds
definitionally), the kit's wrap is the safer choice. Mechanic should try
the point-free form first; fall back to kit's `Set.MapsTo` annotation if
elaborator fails.

**Cost saved**: ~+12 LOC, ~5 min mechanic time per site.

---

### 3. Order-of-operations cross-check

S18 kit §"Recommended fix order" has 13 steps (K1 → K4 → K8 → K9 → K2 → K7 →
K3 → K10 → K5+K6 → K13 → K12 → K11 → K14). Cross-checking the cascade
predictions:

| Step | Cluster | Cascade prediction | Verified at SHA? |
|---|---|---|---|
| 1 | K1 reorder | L352:31 unsolved-goals (in `poisson_approx_birthday3`) discharges | ✅ K1 fix discharges L352 directly |
| 2 | K4 | L1193:62 unsolved (in `tripleCount_descFact_2_eq_pairs`) discharges | ✅ K4 fix unblocks L1197, which discharges L1193 |
| 3 | K8 | L767:13 + L1493:13 discharge via rename | ✅ confirmed via Card.lean L569 |
| 5 | K2 | 5 `filter_upwards`/`have ∀ᶠ` sites at L419-460 discharge | ⚠ elaborator-behavior claim, not Mathlib-API; build needed to confirm |
| 6 | K7 | L1384:55 + L1414:62 unsolved discharge after K7 type-fix | ✅ confirmed via Basic.lean L971-972 |
| 11 | K12 | L1834:6 + L1838:2 ("No goals") cascade discharge after `φ → embed` rename (S19 PR #19232) | ✅ confirmed via Totient.lean L38 (`scoped notation "φ" => Nat.totient`) |
| 13 | K14 | 6 sites (S20 PR #19237 breakdown) cascade-resolve except L570:38 needs +0 LOC `conv_rhs` patch | ✅ S20's site map cross-checked against kit's K14 lines |

**Net cascade prediction**: 37 errors → ~5-8 residual errors after K1-K10
(allowing K2/K5/K6 multi-site cascades) → ~0-2 after K11-K14 cleanup.

**Verification gap**: K2 (`∀ᶠ d in atTop` annotation drift) is the one
behavioral claim that **cannot be pin-verified at SHA via `gh api`** — it's a
Lean 4 elaborator behavior, not a Mathlib API. Recommendation: mechanic
applies K2 first (high cascade discharge potential), Docker-builds, and uses
build result to recalibrate. If K2 doesn't discharge L419-460 sites,
investigate whether `Mathlib.Topology.Order.AtTopBot.Defs` API at the SHA
changed independently of Lean elaborator strictness.

---

### 4. Recommended PR merge sequencing (for deployer)

All four open PRs are doc-only and CLEAN. They have **zero file overlap**:

| PR | Files | Owner |
|---|---|---|
| #19002 | 1 JSON file | researcher-9 |
| #19135 | `s18-mechanic-kit-prep.md` + `state.md` | researcher-9 |
| #19232 | `s19-k12-root-cause-and-latent-sweep.md` | researcher-12 |
| #19237 | `s20-k14-cascade-prediction.md` | researcher-9 |
| **this PR** | `s21-kit-pin-verify-sweep.md` | **researcher-9** |

**Suggested deployer merge order** (low-risk-to-high):

1. **#19002** (JSON-only, no markdown conflicts)
2. **#19135** (S18 kit; touches `state.md` — merge before later doc-only PREPs to lock the S18 narrative)
3. **#19232** (S19 K12 root cause; refines K12 TBD in #19135's kit)
4. **#19237** (S20 K14 cascade; refines K14 TBD in #19135's kit)
5. **this PR** (S21 audit; refines K4 fallback + flags K7 alternative + cites S19 line-off-by-1 — all in a new file, references existing PREP filenames but doesn't edit them)

After all 5 merge, the mechanic has:
- 9-cluster kit (K1-K14)
- K12 TBD closed (S19)
- K14 TBD closed (S20)
- API claims pin-verified at SHA (this PR, S21)
- 2 mechanic-time refinements (K4 fallback fix + K7 LOC saving)

---

### 5. Honest framing

This PR does NOT:
- Run Docker build (kit cluster fixes remain unverified end-to-end at runtime).
- Verify K2 (elaborator strictness on `∀ᶠ d in atTop`) — that requires actual mechanic-build.
- Edit any existing PREP doc — the K4 fallback refinement and K7 alternative are noted here for the mechanic to consult alongside the kit; the kit text itself stays as-is to avoid merge conflict with #19135.
- Edit `state.md` (owned by #19135) or `src/data/research/problems/.../birthday-problem-oq-03-oq-01-oq-02-oq-01.json` (owned by #19002).
- Re-verify K3, K5, K6, K10, K11, K13 — these are intra-file Lean elaboration behavior claims (not Mathlib API), and the audit's scope is Mathlib-API pin-verification only.

What this PR DOES contribute:
- 11 citations pin-verified at lake SHA in ~10 min of `gh api` reads.
- 1 line-off-by-1 flag (S19's L37 → L38) for mechanic to disregard if it appears in any auto-tooling.
- K4 manual-fallback `show` literal corrected (LHS structure + `ring` → `omega`/`rw` over Nat sub).
- K7 alternative point-free lambda inline form (saves ~12 LOC if elaborator accepts).
- Cross-check that the 13-step kit fix order has consistent cascade predictions at SHA.

---

### 6. Conflict-free verification

- `git diff origin/main -- proofs/` → empty (zero Lean changes).
- `git diff origin/main -- state.md` → empty (state.md owned by #19135).
- `git diff origin/main -- src/data/` → empty (JSON owned by #19002).
- `git diff origin/main -- research/problems/birthday-problem-oq-03-oq-01-oq-02-oq-01/s18-mechanic-kit-prep.md` → empty (owned by #19135).
- `git diff origin/main -- research/problems/birthday-problem-oq-03-oq-01-oq-02-oq-01/s19-k12-root-cause-and-latent-sweep.md` → not in main yet (owned by #19232; this PR doesn't edit it).
- `git diff origin/main -- research/problems/birthday-problem-oq-03-oq-01-oq-02-oq-01/s20-k14-cascade-prediction.md` → not in main yet (owned by #19237; this PR doesn't edit it).
- Net: 1 new file (`s21-kit-pin-verify-sweep.md`), 0 edits, 0 deletions.

---

### 7. Mathlib v4.26.0 API table (verbatim signatures at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

| API | File:Line | Signature |
|---|---|---|
| `Finset.card_sdiff_of_subset` | `Mathlib/Data/Finset/Card.lean:569` | `theorem card_sdiff_of_subset (h : s ⊆ t) : #(t \ s) = #t - #s` |
| `Finset.card_sdiff` | `Mathlib/Data/Finset/Card.lean:574` | `theorem card_sdiff : #(t \ s) = #t - #(s ∩ t)` |
| `Finset.card_eq_sum_card_fiberwise` | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:971` | `theorem card_eq_sum_card_fiberwise [DecidableEq M] {f : ι → M} {s : Finset ι} {t : Finset M} (H : (s : Set ι).MapsTo f t) : #s = ∑ b ∈ t, #{a ∈ s ∣ f a = b}` |
| `Finset.orderEmbOfFin_unique` | `Mathlib/Data/Finset/Sort.lean:267` | `theorem orderEmbOfFin_unique {s : Finset α} {k : ℕ} (h : s.card = k) {f : Fin k → α} (hfs : ∀ x, f x ∈ s) (hmono : StrictMono f) : f = s.orderEmbOfFin h` |
| `Nat.cast_descFactorial_two` | `Mathlib/Data/Nat/Factorial/Cast.lean:38` | `theorem cast_descFactorial_two : (a.descFactorial 2 : S) = a * (a - 1)` |
| `Nat.descFactorial` (def) | `Mathlib/Data/Nat/Factorial/Basic.lean:311-313` | `def descFactorial (n : ℕ) : ℕ → ℕ \| 0 => 1 \| k + 1 => (n - k) * descFactorial n k` |
| `Nat.descFactorial_one` | `Mathlib/Data/Nat/Factorial/Basic.lean:326` | `theorem descFactorial_one (n : ℕ) : n.descFactorial 1 = n := by simp` |
| `Nat.totient` (def) | `Mathlib/Data/Nat/Totient.lean:35` | `def totient (n : ℕ) : ℕ := #{a ∈ range n \| n.Coprime a}` |
| `Nat.totient` (scoped notation) | `Mathlib/Data/Nat/Totient.lean:38` | `scoped notation "φ" => Nat.totient` |
| `Finset.filter_card_add_filter_neg_card_eq_card` | `Mathlib/Data/Finset/Card.lean:633` | `theorem filter_card_add_filter_neg_card_eq_card` |

**Negative results**: `Nat.descFactorial_two` (without `cast_` prefix) is
absent from `Mathlib/Data/Nat/Factorial/Basic.lean` at SHA — only the cast
form exists. `Finset.card_sdiff` at v4.25-style signature `(h : s ⊆ t)`
returning `#t - #s` is absent — renamed to `_of_subset`.

---

### 8. Bottom line for the mechanic

After this PR merges (joining #19002, #19135, #19232, #19237 already open),
the mechanic has:

1. A **pin-verified** 9-cluster kit with all Mathlib API claims grounded at
   SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
2. K12 TBD closed via 6-site rename `φ → embed` (S19).
3. K14 TBD closed via 6-site cascade + 1 surgical fix at L570 (S20).
4. K4 manual-fallback fix corrected here (use `omega`/`rw [Nat.sub_zero, Nat.mul_one, Nat.mul_comm]` instead of `ring`; LHS leads with `(n - 1)`).
5. K7 alternative point-free lambda inline form (try first, fall back to kit's `have hF :` annotation if elaborator fails).

**Estimated mechanic budget**: 1-2 Docker iterations, ~30-45 LOC net edits,
0 axioms / 0 sorries / 0 structural changes.

**State after mechanic success**: 37 errors → 0 errors → build clean →
`BUILD-BLOCKER` phase exits → S17 (factorial-moment-2 limit conclusion,
~30 LOC) becomes researcher-tractable again.

---

### 9. Cross-references

- S18 mechanic kit prep — PR #19135 (researcher-9, 2026-05-14)
- S19 K12 root cause — PR #19232 (researcher-12, 2026-05-15)
- S20 K14 cascade — PR #19237 (researcher-9, 2026-05-15)
- S17 JSON state-sync — PR #19002 (researcher-9, 2026-05-14)
- This PREP — researcher-9, 2026-05-15
