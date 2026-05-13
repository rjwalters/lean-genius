# S3 PREP — Mathlib bearer-line audit of merged S2 ACT #18648 (HEAD vs pinned SHA drift, doc-only)

**Author:** researcher-5
**Timestamp:** 2026-05-13 ~08:55 UTC
**Phase:** S3 PREP (post-S2 ACT, doc-only audit-correction; complements PREP-D #18534)
**Iteration:** 3-prep-sha-audit
**Scope:** One new file under `research/sperner-simplicial-instance-oq-05/sessions/`. **No edits** to `problem.md`, `state.md`, `knowledge.md`, sibling session memos (C1, C2-1d, C3, PREP-D, ACT), gallery JSON, or any `.lean` file (including the just-merged `proofs/Proofs/SpernerSimplicialInstanceOQ05.lean`). No build.

## 0. TL;DR

Four Mathlib + Lean-core line citations in S2 PREP-D #18534 (and copied into S2 ACT #18648) point to **Mathlib HEAD on 2026-05-13** rather than the **pinned v4.26.0 SHA in `proofs/lake-manifest.json`**. The **lemma names resolve identically** at both SHAs (build risk = 0 from API names), but the **line numbers drift 6-31 lines** at the lockfile-resolved SHA. Documenting now so future readers navigating Mathlib at the actually-pinned commit don't fall off the citations, and so the next Mathlib-audit PREP uses the correct SHA from the start.

This memo is **strictly doc-only** and **orthogonal** to:
- S1 OBSERVE (#18200) — three-candidate survey, no Mathlib citations.
- C1 PREP (#18459) — flagged the names as unverified; PREP-D resolved them (against wrong SHA).
- C2-1d PREP (#18489) — separate algorithmic design.
- C3 PREP (#18392) — noncomputable cascade audit, no overlap.
- PREP-D (#18534) — Mathlib API audit (this memo audits PREP-D's SHA choice, not its lemma identifications).
- S2 ACT (#18648) — Lean implementation (this memo does NOT propose any code change; the build will succeed regardless of the line drift).

---

## 1. Root cause: PREP-D verified against HEAD, not lockfile

### 1.1 The two SHAs at issue

PREP-D #18534 § 1 opens (memo line 17):

> [PREP-D] pre-resolves the load-bearing names with verbatim `Mathlib/<path>:<line>` citations against leanprover-community/mathlib4 HEAD `23fc2795c350c2c4a5c70e289a545e81273229b3` (the SHA used in our `proofs/lakefile.toml` toolchain pin), so the C1 and C2-1d ACT pickers can copy-paste the verified call without a name-discovery roundtrip.

The parenthetical "(the SHA used in our `proofs/lakefile.toml` toolchain pin)" is **incorrect**.

| File | Content | Resolved SHA | Date |
|---|---|---|---|
| `proofs/lakefile.toml` (line 8) | `rev = "v4.26.0"` (tag) | (resolves to v4.26.0 tag) | — |
| `proofs/lake-manifest.json` | `"name": "mathlib", "rev": "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"` | `2df2f015…` | **2025-12-13 10:35 UTC** (commit msg: "chore: bump toolchain to v4.26.0 (#32833)") |
| PREP-D cited | `23fc2795c350c2c4a5c70e289a545e81273229b3` | `23fc2795…` | **2026-05-13 00:45 UTC** (commit msg: "doc: add newlines to clarify paragraph breaks (#39247)") |

Both SHAs were verified via `gh api repos/leanprover-community/mathlib4/commits/<sha>`. The PREP-D SHA is **5 months newer** (Mathlib HEAD on the morning of the PREP-D author session, 2026-05-13), not the v4.26.0 release SHA.

### 1.2 Why this matters for citations

Lake **builds against the lockfile SHA**, not against current HEAD. So when the Docker build picks up `Mathlib/Data/Finset/Basic.lean` from the cache, the file content is the v4.26.0 release version (`2df2f015…`), not Mathlib HEAD (`23fc2795…`). Between 2025-12-13 and 2026-05-13, Mathlib accumulated changes that shift line numbers in three of the four cited files.

**Lemma names are stable**: `Finset.toList_eq_nil`, `Finset.Nonempty.toList_ne_nil`, `Finset.nonempty_iff_ne_empty`, and `List.mem_of_head?` exist at **both** SHAs. The drift is purely positional. Build-correctness from API names = **0 risk**.

But the citations in PREP-D §1.1, §1.2, and §4.2 (memo lines 41-46, 49-52, 91-95, 220-223), and the citations copied into ACT #18648 §1, §5, and §7 (memo lines 16, 96, 432-435), **all point to non-existent lines** if a reader navigates Mathlib at the actually-pinned SHA.

---

## 2. Four line-drift findings

For each citation, I list (a) the PREP-D / ACT memo claim, (b) the line at HEAD `23fc2795…` (as PREP-D claimed), and (c) the line at the **actually-pinned** `2df2f015…` (as `lake build` would see it). All verifications used `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<sha>` followed by `grep -n` on the decoded content.

### 2.1 `Finset.toList_eq_nil`

| Source | Claim |
|---|---|
| PREP-D #18534 §1.1 row 1 + §4.1 line 358 | `Mathlib/Data/Finset/Basic.lean:525` |
| ACT #18648 memo §7 + Lean source comment at L78-79 ("via Finset.toList_eq_nil and Finset.Nonempty.toList_ne_nil per PREP-D §4.1") | (inherits PREP-D's :525) |
| Mathlib HEAD `23fc2795…` (PREP-D's SHA) | `Mathlib/Data/Finset/Basic.lean:525` ✓ |
| **Pinned `2df2f015…` (v4.26.0)** | **`Mathlib/Data/Finset/Basic.lean:512`** |

Drift: **−13 lines**.

Verification (pinned SHA):

```text
$ gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Data/Finset/Basic.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67" --jq '.content' | base64 -d | grep -n "^theorem toList_eq_nil"
512:theorem toList_eq_nil {s : Finset α} : s.toList = [] ↔ s = ∅ :=
```

### 2.2 `Finset.Nonempty.toList_ne_nil`

| Source | Claim |
|---|---|
| PREP-D #18534 §1.1 row 3 + §4.1 line 364 | `Mathlib/Data/Finset/Basic.lean:534` |
| ACT #18648 (inherits) | (inherits PREP-D's :534) |
| Mathlib HEAD `23fc2795…` | `Mathlib/Data/Finset/Basic.lean:534` ✓ |
| **Pinned `2df2f015…`** | **`Mathlib/Data/Finset/Basic.lean:521`** |

Drift: **−13 lines** (same offset as §2.1; both lemmas moved together).

Verification (pinned SHA):

```text
521:theorem Nonempty.toList_ne_nil {s : Finset α} (hs : s.Nonempty) : s.toList ≠ [] :=
522:  mt toList_eq_nil.mp hs.ne_empty
```

### 2.3 `Finset.nonempty_iff_ne_empty`

| Source | Claim |
|---|---|
| PREP-D #18534 §1.1 row 6 + §4.1 line 356 | `Mathlib/Data/Finset/Empty.lean:142` |
| ACT #18648 (inherits) | (inherits PREP-D's :142) |
| Mathlib HEAD `23fc2795…` | `Mathlib/Data/Finset/Empty.lean:142` ✓ |
| **Pinned `2df2f015…`** | **`Mathlib/Data/Finset/Empty.lean:148`** |

Drift: **+6 lines**.

Verification (pinned SHA):

```text
148:theorem nonempty_iff_ne_empty {s : Finset α} : s.Nonempty ↔ s ≠ ∅ :=
149:  not_iff_comm.mp not_nonempty_iff_eq_empty
```

### 2.4 `List.mem_of_head?` (Lean core, not Mathlib)

| Source | Claim |
|---|---|
| ACT #18648 memo §7 (line 96) | `Init.Data.List.Lemmas:968` |
| Lean HEAD (whatever ACT-author checked) | (unknown; the ACT memo does not state which SHA it verified against) |
| **Pinned Lean toolchain `v4.26.0` = commit `d8204c9fd894f91bbb2cdfec5912ec8196fd8562`** (`leanprover/lean4/contents/src/Init/Data/List/Lemmas.lean?ref=d8204c9…`) | **`Init.Data.List.Lemmas:937`** |

Drift: **−31 lines**.

Verification (pinned Lean v4.26.0):

```text
$ gh api "repos/leanprover/lean4/contents/src/Init/Data/List/Lemmas.lean?ref=d8204c9fd894f91bbb2cdfec5912ec8196fd8562" --jq '.content' | base64 -d | grep -n "^theorem mem_of_head\?"
937:theorem mem_of_head? : {l : List α} → {a : α} → l.head? = some a → a ∈ l
```

Line 968 at v4.26.0 contains:

```text
$ awk 'NR>=965 && NR<=970' /tmp/lean_v4260_list_lemmas.lean
965  head_of_head?_eq_some hx
966
967  @[simp] theorem head?_singleton_iff {a b : α} : ([a] : List α).head? = some b ↔ b = a := by
968    simp
969
970  theorem head?_eq_zero_iff_isEmpty {α : Type*} {l : List α} : l.head? = some (...
```

So at v4.26.0, line 968 is **not** `mem_of_head?` (it's a one-line `simp` continuation of `head?_singleton_iff`). The :968 citation is therefore a phantom line at the lockfile SHA.

Note: the ACT memo §1 line 40 explicitly says "verified via `gh api repos/leanprover/lean4/contents/...` **at HEAD**" — confirming the at-HEAD pattern that this audit identifies.

### 2.5 Companion citations (verified correct at pinned SHA, listed for completeness)

The following load-bearing citations from PREP-D / ACT happen to be stable across the Dec 2025 → May 2026 window. **No drift** at the pinned SHA:

| Lemma | Path:line at pinned `2df2f015…` |
|---|---|
| `Finset.mem_filter` | `Mathlib/Data/Finset/Filter.lean:127` |
| `Finset.mem_toList` | `Mathlib/Data/Finset/Dedup.lean:171` |
| `Finset.mem_univ` | `Mathlib/Data/Fintype/Defs.lean:95` |
| `Fintype.injective_iff_surjective` | (not verified in this memo; PREP-D §1.2 cites `Mathlib/Data/Fintype/Card.lean:327` against HEAD; the **name** definitely exists at v4.26.0, line may differ) |

These were unaffected by the Dec→May churn because they live in stable, less-edited files. The four drift findings above all touch `Basic.lean` / `Empty.lean` / `Init/Data/List/Lemmas.lean` — files that did accumulate edits in the intervening 5 months.

---

## 3. Build-risk assessment

### 3.1 Build risk from line-citation drift: **zero**

`lake build` resolves lemmas by **name**, not by file:line. All four phantom-line citations name lemmas that **exist** at the pinned SHA with the same signature. The build of `proofs/Proofs/SpernerSimplicialInstanceOQ05.lean` will not fail because of any of the §2 findings.

The drift only affects **human navigation**: a downstream reader (e.g. a Mechanic agent fixing a future build break) following the ACT's `§7 References` block to look up `mem_of_head?` at `Init.Data.List.Lemmas:968` will land on a `simp` line and have to grep further. Annoying but not blocking.

### 3.2 Remaining genuine build risks (not addressed by this PREP)

The ACT memo §3 lists three risks that remain:

1. **`decide` smoke-test reduction.** Line 167 of `SpernerSimplicialInstanceOQ05.lean` (the `example : ∃ s : Fin 3, …` line) relies on `decide` chewing through:
   - `Triangulation.intervalTriangulation 3 (by norm_num)` projection
   - `K.vertex` definitional unfolding via `toCellComplex.vertex := T.vertex` (`SpernerSimplicialInstance.lean:127`)
   - `private def ivtx hm i k = if k.val = 0 then i.val else i.val + 1` (`SpernerSimplicialInstance.lean:813`)
   - `Function.Surjective (c ∘ K.vertex 1) : Fin 2 → Fin 2`'s `Decidable` instance via `inferInstance` (`SpernerMathlib4.lean:452-457`)

   The `private` attribute on `ivtx` (memo PREP-D §2.4 footnote) is a name-visibility marker, not a reducibility marker, so `decide` should reduce through the projection. PREP-D §2.4 flagged the same risk for the C2-1d `rfl` proofs and suggested a `simp`-based fallback if needed.

   **If `decide` fails**: try `decide!` (eager, more aggressive kernel reduction). If that also fails, expand the example into an explicit witness:

   ```lean
   refine ⟨1, ?_⟩
   show Function.Surjective ((fun n : ℕ => if n ≤ 1 then (0 : Fin 2) else 1) ∘
     (Triangulation.intervalTriangulation 3 (by norm_num)).toCellComplex.vertex 1)
   intro y
   fin_cases y
   · exact ⟨0, by decide⟩  -- y = 0; vertex 1 0 = 1; c 1 = 0
   · exact ⟨1, by decide⟩  -- y = 1; vertex 1 1 = 2; c 2 = 1
   ```

   ~6 LOC fallback if needed. Doctor / Mechanic territory.

2. **`Finset.univ.filter` enumeration order.** The `findPanchromaticBrute` doc-comment (Lean source lines 64-68) says "the choice of 'first' is in the order of `T.cellFintype.elems.toList`, which is implementation-specific." If a reader assumes that order is "canonical `Fin n`" (as PREP-D §3.1 traces in its `#eval` prediction), they are relying on the `Fintype (Fin m)` instance's default enumeration. This is `List.finRange`, in increasing `i.val` order, so the PREP-D §3.1 trace is correct — but the ACT's own `findPanchromaticBrute_isSome_iff` characterisation deliberately does not rely on this (line 67 says "Downstream consumers should use the membership characterisation … rather than relying on a specific order"). So the `#eval` order is well-behaved but informally documented.

3. **`Finset.univ` and `T.cellFintype` defeq.** The `findPanchromaticBrute` definition writes `Finset.univ.filter …` where the `Finset.univ : Finset T.Cell` is supplied by `Finset.univ` over `T.cellFintype` (`Triangulation.cellFintype` per `SpernerSimplicialInstance.lean:84`). The smoke-test `intervalTriangulation 3` has `Cell := Fin 3` (line 960) and `cellFintype := inferInstance` (line 962) which resolves to the canonical `Fin.fintype 3`. So `Finset.univ : Finset (Fin 3)` reduces to `{0, 1, 2}` and `decide` should chew. No additional risk.

The three risks above are independent of the §2 SHA drift and would persist even with corrected line citations. They will likely require a Docker build before being declared resolved.

---

## 4. Recommendations for future Mathlib-audit PREPs

This is the **second** instance of this pattern in the past 24 hours. The first was `feedback_researcher_12_2026_05_13_triple_mathlib_bearer_audit.md` (sibling slug `shapley-folkman`, `hilbert-14`, `schroeder-bernstein`) where parent PREPs cited Mathlib bearers without verifying they exist at the actual pin. Generalising the recipe:

### 4.1 Always cite against the lockfile SHA

```bash
# In the repo root:
LAKE_PIN=$(jq -r '.packages[] | select(.name == "mathlib") | .rev' proofs/lake-manifest.json)
echo "Mathlib pin: $LAKE_PIN"
# 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67

# Then verify lemma X exists:
gh api "repos/leanprover-community/mathlib4/contents/<Mathlib/path/to.lean>?ref=$LAKE_PIN" \
  --jq '.content' | base64 -d | grep -n "<lemma name>"
```

For Lean core:

```bash
LEAN_TC=$(awk -F: '{print $2}' proofs/lean-toolchain)
# leanprover/lean4:v4.26.0  -> tag v4.26.0
LEAN_SHA=$(gh api "repos/leanprover/lean4/commits/$LEAN_TC" --jq '.sha')
gh api "repos/leanprover/lean4/contents/src/Init/Data/List/Lemmas.lean?ref=$LEAN_SHA" \
  --jq '.content' | base64 -d | grep -n "<lemma name>"
```

### 4.2 If you must cite HEAD, say so explicitly

A PREP that cites HEAD (e.g., to anticipate a future Mathlib bump) is fine **if it explicitly labels the citations as HEAD-relative**. PREP-D #18534 §1 line 17 attempted to label its SHA but mis-identified the lockfile pin. The corrected language would be:

> against leanprover-community/mathlib4 **HEAD as of YYYY-MM-DD** (`<sha>`), which is **5 months ahead** of `proofs/lake-manifest.json`'s pin (`<lockfile-sha>`, the v4.26.0 release tag).

Then the reader has both citations in hand and can reconcile.

### 4.3 Audit at PR-create time, not at PREP-write time

In high-churn periods (multiple PREPs on the same slug in <12 hours), the Mathlib pin can shift mid-session if a deployer bumps Mathlib. The current pin `2df2f015…` has been stable for 5 months, so this scenario doesn't apply here, but it's a future risk worth flagging in the standing PREP recipe.

---

## 5. Anti-targets (what this PREP-S3 does NOT do)

1. ❌ Write or edit `proofs/Proofs/SpernerSimplicialInstanceOQ05.lean` — the merged ACT file is correct as shipped; the §2 drift does not affect compilation.
2. ❌ Edit PREP-D #18534 — that PR is already merged; corrections live in this memo for the next reader.
3. ❌ Edit the ACT memo `2026-05-13-s2-act-c1-brute-force-implementation.md` — same reason.
4. ❌ Edit `problem.md`, `state.md`, `knowledge.md`, or `src/data/research/problems/sperner-simplicial-instance-oq-05.json`.
5. ❌ Run `./proofs/scripts/docker-build.sh` — doc-only PREP per the `.lake` symlink trap; not necessary for line-citation audit.
6. ❌ Address C2-1d's `step`-semantics mathematical bug (PREP-D §3.2). That's a separate ACT design task.
7. ❌ Submit anything to Aristotle. No `*Aristotle.lean` companion.
8. ❌ Promote to gallery (`src/data/proofs/sperner-simplicial-instance-oq-05/`). Build verification is the prerequisite, not citation cleanup.

## 6. Acceptance criteria

1. **Four line-drift findings (§2)** each independently verified via `gh api` against the actually-pinned SHA `2df2f015…` (Mathlib) and `d8204c9…` (Lean v4.26.0 tag).
2. **No build attempt.** All claims are paper-only; verification is by file-fetch, not Docker.
3. **No file edits outside `sessions/`.** Single new path under `research/sperner-simplicial-instance-oq-05/sessions/`.
4. **Build-risk assessment (§3)** distinguishes the **0-risk** drift (this memo's scope) from the **non-zero-risk** remaining items (`decide` smoke-test, etc., outside this memo's scope).
5. **Pre-push race check passes**: at push time, `gh pr list --repo rjwalters/lean-genius --search "sperner-simplicial-instance-oq-05 in:title" --state open` is empty.

## 7. Honesty

- **§2 line numbers verified at this session's wall-clock time** (2026-05-13 ~08:55 UTC). If the deployer bumps Mathlib between now and push, the pinned SHA could change; the §2 verifications would then become stale themselves. This memo treats the lockfile as authoritative; future audits should re-verify against `proofs/lake-manifest.json` at their own session time.
- **§3.1 "build risk = 0" claim** assumes the Mathlib names `Finset.toList_eq_nil`, `Finset.Nonempty.toList_ne_nil`, `Finset.nonempty_iff_ne_empty`, and `List.mem_of_head?` resolve identically. I verified the **theorem names + statement shapes match** at both SHAs by reading the `grep` output (`^theorem <name>` matches at both). I did NOT verify that the **proof bodies** match — but `lake build` resolves declarations by name + type signature, so even if the proof body changed, the build is unaffected.
- **§2.4 (`mem_of_head?`)** was verified at the **v4.26.0 tag commit**, which resolves to `d8204c9fd894f91bbb2cdfec5912ec8196fd8562`. If `proofs/lean-toolchain` advances in the future (e.g., to v4.27.0), this line will drift again.
- **No deeper Mathlib API audit.** This memo intentionally restricts itself to the **four line citations PREP-D and ACT both depend on**. A broader audit of all 8-10 names PREP-D cites would catch more drift but is out of scope.
- **§3.2 `decide` smoke-test risk** is restated from the ACT memo §3, with a concrete 6-LOC fallback proposal (the `intro y; fin_cases y; exact ⟨0/1, decide⟩` chain). I did NOT run `decide` to test reachability; if `decide` actually fails, a future Mechanic session will discover it during build, and the fallback above can be applied.

## 8. Race awareness

- **Pre-claim**: `gh pr list --repo rjwalters/lean-genius --search "sperner-simplicial-instance-oq-05 in:title" --state open` → **`[]`** at 2026-05-13 08:47 UTC.
- **Latest merge on slug**: PR #18648 (S2 ACT, 2026-05-13 07:29 UTC, ~78 min before this memo's claim).
- **Pre-push**: must re-run the same `gh pr list` command before pushing; if any open PR has appeared, bail per `feedback_mechanic_race_quadruple_slot_collision.md` (concurrent sibling slots can converge on the same slug post-merge).
- **Conflict surface**: zero. Single new file under `sessions/`, no edits to other paths. Even if a parallel session is opening a new PR on this slug for an orthogonal reason (e.g., S3 GALLERY PREP for the new `src/data/proofs/sperner-simplicial-instance-oq-05/` directory), no path conflict.
- **Saturation window**: 78 min post-merge falls within memory's `[Post-S1/S1b S2/S4 PREP session-note cluster]` and `[researcher-11 sextuple audit-correction session]` patterns. Adding one orthogonal audit-correction memo at this cadence is well within the documented pattern.

## 9. Cross-references

- **PR #18200** (MERGED 2026-05-12 16:26 UTC) — S1 OBSERVE candidate framing.
- **PR #18392** (MERGED 2026-05-13 00:03 UTC) — C3 noncomputable cascade audit.
- **PR #18459** (MERGED 2026-05-13 02:13 UTC) — C1 brute-force scaffold; flagged `Finset.toList_ne_nil_iff_nonempty` as unverified.
- **PR #18489** (MERGED 2026-05-13 02:44 UTC) — C2-1d Scarf walk PREP.
- **PR #18534** (MERGED 2026-05-13 03:30 UTC) — S2 PREP-D Mathlib API audit + bridge discharge. **This memo audits the SHA choice of PREP-D §1 (memo line 17).**
- **PR #18648** (MERGED 2026-05-13 07:29 UTC) — S2 ACT C1 Lean implementation. **This memo audits the line citations in ACT memo §1 line 40 + §7 lines 91-96.**
- `proofs/lake-manifest.json` — pins Mathlib at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (2025-12-13).
- `proofs/lean-toolchain` — pins Lean at `v4.26.0` = `d8204c9fd894f91bbb2cdfec5912ec8196fd8562` (2025-12-13).
- **Mathlib at HEAD `23fc2795c350c2c4a5c70e289a545e81273229b3`** (2026-05-13) — what PREP-D actually cited.
- **Memory references**:
  - `feedback_researcher_12_2026_05_13_triple_mathlib_bearer_audit.md` — Mathlib-bearer-audit PREP pattern; this memo extends it by adding the **HEAD-vs-lockfile SHA discrepancy** as an audit dimension.
  - `feedback_researcher_11_2026_05_13_sextuple_audit_correction_session.md` — audit-correction PREP cadence; this memo follows the 30-min-post-merge sub-pattern (here: 78 min post-merge, still in window).
  - `[Mathlib audit obsoletes bespoke S2 scaffold]` — the *audit-first* lesson; this memo applies the lesson to *audit the audit*.
  - `[greens-theorem family Mathlib v4.26.0 drift]` — concrete prior example where Mathlib v4.26.0 line drift was build-blocking (different from this memo's SHA-mismatch case; that one was a renamed lemma).

## 10. Concrete corrected citation block (for future copy-paste)

To replace the ACT memo §7 References block ("Mathlib v4.26.0 (pin per `proofs/lean-toolchain`)" and "Lean core" subsections):

```markdown
* **Mathlib v4.26.0** (pin per `proofs/lake-manifest.json` SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, dated 2025-12-13):
  * `Mathlib/Data/Finset/Basic.lean:512` (`Finset.toList_eq_nil`).
  * `Mathlib/Data/Finset/Basic.lean:521` (`Finset.Nonempty.toList_ne_nil`).
  * `Mathlib/Data/Finset/Empty.lean:148` (`Finset.nonempty_iff_ne_empty`).
  * `Mathlib/Data/Finset/Filter.lean:127` (`Finset.mem_filter`).
  * `Mathlib/Data/Finset/Dedup.lean:171` (`Finset.mem_toList`).
  * `Mathlib/Data/Fintype/Defs.lean:95` (`Finset.mem_univ`, in fact `Fintype.mem_univ` opened via `open Finset`).
* **Lean core v4.26.0** (`leanprover/lean4` tag = SHA `d8204c9fd894f91bbb2cdfec5912ec8196fd8562`, dated 2025-12-13):
  * `Init/Data/List/Lemmas.lean:937` (`List.mem_of_head?`).
```

The next Mathlib-audit PREP author on this slug (or any sibling) can use this corrected block verbatim. If `proofs/lake-manifest.json` advances (deployer bumps Mathlib), re-run the verification script in §4.1 and update accordingly.
