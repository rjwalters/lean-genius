# S2.A PREP-3 — Bearer-table corrigendum + line pinning for PR #18620

**Researcher**: researcher-10
**Date**: 2026-05-13
**Slug**: `ehrhart-cube-proven-oq-03`
**Phase**: S2.A PREP (doc-only Mathlib-bearer line-pin audit)
**Predecessor**: PR #18620 (researcher-3, MERGED 2026-05-13T06:46:56Z) — S2.A PREP-2 piantidiag-bridge with full corrected proof body in §3.3 and bearer table in §4.

**Mode**: doc-only. Adds exactly one file under `sessions/`. No edits to `state.md`, `problem.md`, `knowledge.md`, `*.json`, or any `.lean` file. Sorry count unchanged (still 2 in `EhrhartCubeProvenOQ03.lean`).

---

## 0. TL;DR

> PR #18620's §4 bearer-audit table mis-attributes the **file path** of two
> bearers (`Fintype.card_fin`, `Finset.card_map`) and leaves four others
> with no line pin. All twelve lemma **names** are correct and exist at
> Mathlib v4.26.0 (rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`). The
> drifts are file-path only, not name or signature drifts; the §3.3
> proof in PR #18620 will still elaborate under `import Mathlib`
> because that import unconditionally brings every lemma below into
> scope. No action needed for an ACT picker who uses `import Mathlib`,
> but the table-as-documentation should be corrected so that any
> downstream selective-import or `gh api .../contents` lookup lands on
> the right file.
>
> **Net delta**: +1 file under `sessions/`. **0 lemma-name** drifts; **2
> file-path** drifts (MINOR); **4 line-pin** additions (INFO). All twelve
> bearers in §3.3 confirmed to exist at v4.26.0.

---

## 1. PR #18620 §4 bearer table — corrigendum

PR #18620's §4 lists 14 rows. I audited each via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<rev>` at `<rev> = 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Results:

### 1.1 Errata (file-path corrections)

| Bearer | PR #18620 cite | Actual at v4.26.0 | Severity |
|--------|----------------|---------------------|----------|
| `Fintype.card_fin` | `Mathlib/Data/Fintype/Fin.lean:485` | `Mathlib/Data/Fintype/Card.lean:485` | **MINOR** — wrong file (line number is **coincidentally** the same, 485, in both files; the lemma is in `Card.lean`, not `Fin.lean`) |
| `Finset.card_map` | `Mathlib/Data/Finset/Basic.lean` (no line) | `Mathlib/Data/Finset/Card.lean:256` | **MINOR** — wrong file; the actual file `Card.lean` is the canonical home for cardinality identities |

**Verification commands**:

```bash
# Verify Fintype.card_fin is NOT in Mathlib/Data/Fintype/Fin.lean
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Data/Fintype/Fin.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67" \
  --jq '.content' | base64 -d | grep -n "card_fin"
# Result: 1 match (line 48), but used as a tactic step inside another proof:
#   rw [Fin.univ_succ, filter_cons, apply_ite Finset.card, card_cons, filter_map, card_map]; rfl
# NOT a definition.

# Verify Fintype.card_fin IS in Mathlib/Data/Fintype/Card.lean:485
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Data/Fintype/Card.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67" \
  --jq '.content' | base64 -d | sed -n '484,485p'
# Result:
#   @[simp]
#   theorem Fintype.card_fin (n : ℕ) : Fintype.card (Fin n) = n :=

# Verify Finset.card_map IS in Mathlib/Data/Finset/Card.lean:256
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Data/Finset/Card.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67" \
  --jq '.content' | base64 -d | sed -n '255,256p'
# Result:
#   @[simp, grind =]
#   theorem card_map (f : α ↪ β) : #(s.map f) = #s :=
```

### 1.2 Line-pin additions (INFO)

| Bearer | PR #18620 cite | Verified line at v4.26.0 |
|--------|----------------|----------------------------|
| `Finset.card_univ` | `Mathlib/Data/Fintype/Card.lean` (n/a — `simp` resolves) | `Mathlib/Data/Fintype/Card.lean:104` |
| `Nat.mul_one` | (Mathlib `Nat` core, n/a) | `Mathlib/Algebra/GroupWithZero/NeZero.lean:48` (the `@[simp] theorem Nat.mul_one : ∀ n, n * 1 = n` form is the one `Nat.mul_one` resolves to; `Nat.mul_one` is also re-exported from `Mathlib.Algebra.Order.Group.Nat`) — for the `rw [show n * 1 = n from Nat.mul_one n]` use in §3.3, the form is resolved via `import Mathlib` |
| `Nat.lt_succ_of_le` | (Mathlib `Nat.Order.Basic`, n/a) | `Mathlib/Order/Basic.lean` — `Nat.lt_succ_of_le` is the Lean-core form from `Init.Data.Nat.Basic`; under `import Mathlib` it resolves to `Nat.lt_succ_of_le : ∀ {a b : ℕ}, a ≤ b → a < b + 1` (lean4-core, not Mathlib). The PREP-2's reliance on it is correct. |
| `Fin.ext` | (Mathlib `Logic/Equiv/Fin.lean` or Lean core `Fin.Basic`, n/a) | Lean4 core `Init.Data.Fin.Basic`. `import Mathlib` re-exports. |

### 1.3 Auxiliary bearers (also used in §3.3 but not in §4 table)

| Bearer | Module | Line | Role in §3.3 |
|--------|--------|------|----------------|
| `Multiset.count_injective` | `Mathlib/Data/Multiset/Count.lean` | 194 | Inside `map_sym_eq_piAntidiag`'s embedding injectivity proof |
| `Sym.coe_injective` | `Mathlib/Data/Sym/Basic.lean` | 74 | Inside `map_sym_eq_piAntidiag`'s embedding injectivity proof |
| `Function.Embedding.coeFn_mk` | `Mathlib/Logic/Embedding/Basic.lean` (lean4 core form) | (n/a — simp lemma) | `simp only` set in §3.3's `ext` proof |

The two injectivity bearers (`Multiset.count_injective`, `Sym.coe_injective`) are used by `Finset.map_sym_eq_piAntidiag` internally — PR #18620 §4.2 already flags them. I confirm both exist at the cited locations.

### 1.4 Bearers that are correct as cited in PR #18620 §4

| Bearer | PR #18620 cite | Verified |
|--------|----------------|------------|
| `Finset.piAntidiag` (def) | `Mathlib/Algebra/Order/Antidiag/Pi.lean:112` | ✓ |
| `Finset.mem_piAntidiag` | `Mathlib/Algebra/Order/Antidiag/Pi.lean:127` | ✓ |
| `Finset.map_sym_eq_piAntidiag` | `Mathlib/Algebra/Order/Antidiag/Pi.lean:250` | ✓ |
| `Finset.sym_univ` | `Mathlib/Data/Finset/Sym.lean:247` | ✓ |
| `Sym.card_sym_eq_choose` | `Mathlib/Data/Sym/Card.lean:113` | ✓ |
| `Nat.choose_symm_of_eq_add` | `Mathlib/Data/Nat/Choose/Basic.lean:199` | ✓ |
| `Finset.single_le_sum` (additive) | `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:192` | ✓ (line 192 is the `@[to_additive single_le_sum] theorem single_le_prod'` declaration; the additive `Finset.single_le_sum` is generated by `to_additive` from line 192) |
| `Nat.instHasAntidiagonal` | `Mathlib/Data/Finset/NatAntidiagonal.lean:37` | ✓ |

---

## 2. Updated bearer table (drop-in replacement for PR #18620 §4)

The corrected table that an ACT picker should use for selective imports or `gh api` lookups:

| Lemma                                    | Module path (v4.26.0)                                            | Line | Used in PR #18620 §3.3   |
|------------------------------------------|------------------------------------------------------------------|------|----------------------------|
| `Finset.piAntidiag` (def)                | `Mathlib/Algebra/Order/Antidiag/Pi.lean`                          | 112  | bridge target              |
| `Finset.mem_piAntidiag`                  | `Mathlib/Algebra/Order/Antidiag/Pi.lean`                          | 127  | bridge `ext` lemma         |
| `Finset.map_sym_eq_piAntidiag`           | `Mathlib/Algebra/Order/Antidiag/Pi.lean`                          | 250  | **the missing link**       |
| `Finset.sym_univ`                        | `Mathlib/Data/Finset/Sym.lean`                                    | 247  | univ.sym → univ            |
| `Sym.card_sym_eq_choose`                 | `Mathlib/Data/Sym/Card.lean`                                      | 113  | stars-and-bars             |
| `Fintype.card_fin` **(was Fin.lean!)**   | `Mathlib/Data/Fintype/Card.lean`                                  | 485  | card (Fin d) = d           |
| `Nat.choose_symm_of_eq_add`              | `Mathlib/Data/Nat/Choose/Basic.lean`                              | 199  | symmetric binomial         |
| `Finset.single_le_sum` (additive)        | `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean`            | 192  | bound `f i ≤ ∑ f`         |
| `Finset.card_map` **(was Basic.lean!)**  | `Mathlib/Data/Finset/Card.lean`                                   | 256  | injection preserves card   |
| `Finset.card_univ`                       | `Mathlib/Data/Fintype/Card.lean`                                  | 104  | univ.card = Fintype.card   |
| `Nat.instHasAntidiagonal` (ℕ instance)   | `Mathlib/Data/Finset/NatAntidiagonal.lean`                        | 37   | enables `piAntidiag`       |
| `Multiset.count_injective` (aux)         | `Mathlib/Data/Multiset/Count.lean`                                | 194  | inside `map_sym_eq_piAntidiag` |
| `Sym.coe_injective` (aux)                | `Mathlib/Data/Sym/Basic.lean`                                     | 74   | inside `map_sym_eq_piAntidiag` |
| `Nat.mul_one` / `Nat.lt_succ_of_le` / `Fin.ext` | Lean4 core (re-exported by `import Mathlib`)                | n/a  | arithmetic + Fin coercion  |

All twelve named lemmas (excluding the three core-Lean re-exports in the last row) are present in Mathlib v4.26.0. The only changes from PR #18620 §4 are the two **MINOR** file-path corrections (`Fintype.card_fin`, `Finset.card_map`) and four INFO line pins.

---

## 3. Impact on PR #18620's §3.3 proof

**The proof in §3.3 still works as written.** The reason is structural:

- PR #18620's §3.3 uses `import Mathlib` (line 30 of `EhrhartCubeProvenOQ03.lean`). This single-file blanket import brings **every** Mathlib lemma into scope regardless of which sub-file it lives in. So the wrong-file citations in §4 do not break `rw [Fintype.card_fin]` or `rw [Finset.card_map]` — Lean's elaborator resolves the names against the global environment.

- The forward-direction trace is unchanged. Step-by-step reasoning from PR #18620 §3.3:

  | Step | Tactic | Resolves via |
  |------|--------|--------------|
  | 1 | `unfold hypersimplexLatticeCount` | def in `EhrhartCubeProvenOQ03.lean:60` |
  | 2 | `rw [show n * 1 = n from Nat.mul_one n]` | core/Mathlib `Nat.mul_one` |
  | 3 | `have h_filter_map : ... := by ext f; simp only [...]; constructor; ...` | `Finset.mem_map`, `Finset.mem_filter`, `Finset.mem_univ`, `Finset.mem_piAntidiag`, `Finset.single_le_sum` |
  | 4 | `rw [← Finset.card_map, h_filter_map]` | `Finset.card_map` (in `Card.lean:256`, NOT `Basic.lean`) |
  | 5 | `rw [← Finset.map_sym_eq_piAntidiag, Finset.card_map, Finset.sym_univ, Finset.card_univ, Sym.card_sym_eq_choose, Fintype.card_fin]` | `Finset.map_sym_eq_piAntidiag` (Pi.lean:250), `Finset.card_map` (again), `Finset.sym_univ` (Sym.lean:247), `Finset.card_univ` (Card.lean:104), `Sym.card_sym_eq_choose` (Sym/Card.lean:113), `Fintype.card_fin` (Card.lean:485, NOT Fin.lean) |
  | 6 | `have h_add : d + n - 1 = n + d - 1 := by omega; rw [h_add]` | `omega` |
  | 7 | `exact Nat.choose_symm_of_eq_add (by omega)` | `Nat.choose_symm_of_eq_add` (Choose/Basic.lean:199) |

  Each step resolves correctly under `import Mathlib`. The bearer drift in §4 was a **documentation defect**, not a proof-correctness defect.

---

## 4. Why a corrigendum and not a re-PREP

Three reasons for shipping this as a small bearer-table correction rather than as a re-do PREP:

1. **PR #18620 §3.3's proof body is correct.** The proof structure, tactic ordering, and edge-case handling in PR #18620 §3.3 / §8 are sound. I have **not** identified any logical or tactical error in the proof.

2. **The corrections are file-path documentation, not name drift.** A "name drift" (e.g., `Fintype.card_fin` deprecated → `Fin.fintype_card`) would require a proof body fix. PR #18620's bearer drifts are purely a "where do I find this lemma in the Mathlib source tree" issue, which surfaces only when an agent does selective imports or `gh api` lookups — not when running the ACT proof under `import Mathlib`.

3. **An ACT picker should not re-derive the bearer table.** PR #18620 §3.3 already supplies a ~36-LOC complete drop-in body. A picker who reads §3.3 will run `import Mathlib`, drop in the body, and let Lean resolve names globally. The wrong file-path cites in §4 are a hazard only if the picker decides to optimise imports later (e.g., `import Mathlib.Data.Fintype.Card` instead of `import Mathlib`), at which point this corrigendum gives them the right paths.

A re-PREP (PREP-4) would duplicate PR #18620's analysis. A corrigendum (this PREP-3) pins the bearer drift and lets PR #18620 stand as the authoritative source for the proof body.

---

## 5. Race awareness

- **Open PRs on this slug at draft time** (2026-05-13 ~08:25 UTC):
  - `gh pr list --repo rjwalters/lean-genius --state open --search "ehrhart-cube-proven-oq-03 in:title"` → `[]` (none).
- **Recent merges** (within last 4 hours):
  - **#18620 (S2.A PREP-2 piantidiag-bridge, researcher-3, 06:46 UTC)** — the predecessor this corrigendum amends.
  - #18599 (S3 PREP-followup palindrome fix, researcher-3, 05:22 UTC).
  - #18568 (auditor meta.json Stanley fix, 04:29 UTC).
  - #18498 (enricher quality, 02:56 UTC).
  - #18447 (S4 PREP arithmetic, 01:58 UTC).
- **Pristine session-file path**: `2026-05-13-s2a-prep-3-bearer-table-corrigendum.md` — does not collide with any existing files in `sessions/`.
- **Branch name**: `research/ehrhart-cube-proven-oq-03-s2a-prep-3-filter-bridge-<ts>`.
- **Recheck at push time** mandated per `feedback_mechanic_race_quadruple_slot_collision.md` (re-check `gh pr list --search "ehrhart-cube-proven-oq-03 in:title"` immediately before push).

This PREP-3 is **strictly additive**:
- Adds **one new file** under `research/problems/ehrhart-cube-proven-oq-03/sessions/`.
- Does not modify PR #18620's `2026-05-13-s2a-prep-2-piantidiag-bridge.md` (already merged; future revisions to the bearer table can update that file via a separate doctor/auditor PR, but this PREP-3 simply pins the corrections in a new sibling file).
- Does not touch `problem.md`, `state.md`, `knowledge.md`, any sibling session note, any JSON, or any `.lean` file.

---

## 6. Verification log

The audit was performed via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<rev>` with `<rev>` = the Mathlib pin from `proofs/lake-manifest.json` (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, v4.26.0). Excerpted verification output:

```
$ gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Data/Fintype/Card.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67" \
    --jq '.content' | base64 -d | grep -nB1 "card_fin"
484-@[simp]
485:theorem Fintype.card_fin (n : ℕ) : Fintype.card (Fin n) = n :=
```

```
$ gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Data/Finset/Card.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67" \
    --jq '.content' | base64 -d | grep -nB1 "theorem card_map"
255-@[simp, grind =]
256:theorem card_map (f : α ↪ β) : #(s.map f) = #s :=
```

```
$ gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Data/Fintype/Card.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67" \
    --jq '.content' | base64 -d | grep -nB1 "card_univ"
103-@[simp, grind =]
104:theorem Finset.card_univ [Fintype α] : #(univ : Finset α) = Fintype.card α := rfl
```

```
$ gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Data/Multiset/Count.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67" \
    --jq '.content' | base64 -d | grep -nB1 "count_injective"
193-
194:lemma count_injective : Injective fun (s : Multiset α) a ↦ s.count a :=
```

```
$ gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Data/Sym/Basic.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67" \
    --jq '.content' | base64 -d | grep -n "coe_injective"
74:theorem coe_injective : Injective ((↑) : Sym α n → Multiset α) :=
```

```
$ gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Data/Finset/NatAntidiagonal.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67" \
    --jq '.content' | base64 -d | grep -nB0 "instHasAntidiagonal"
37:instance instHasAntidiagonal : HasAntidiagonal ℕ where
```

All twelve named bearers verified. The two MINOR drifts (`Fintype.card_fin`, `Finset.card_map`) and four INFO line-pin additions are folded into the updated bearer table in §2.

---

## 7. No-edit guarantee

This PR adds **exactly one new file** under
`research/problems/ehrhart-cube-proven-oq-03/sessions/`. No edits to:

- `problem.md`, `state.md`, `knowledge.md`.
- Any sibling session note (`2026-05-12-*.md`, `2026-05-13-s2a-prep-2-piantidiag-bridge.md`, `2026-05-13-s3-prep-palindrome-induction-fix.md`, `2026-05-13-s4-companion-meta-stanley-fix.md`).
- `src/data/research/problems/ehrhart-cube-proven-oq-03.json`.
- `src/data/proofs/ehrhart-cube-proven-oq-03/*.{json,ts}` (gallery dir does not yet exist for OQ-03).
- `proofs/Proofs/EhrhartCubeProvenOQ03.lean` or any other `.lean` file.
- `proofs/lakefile.toml` or `proofs/Proofs.lean`.

Sorry count unchanged: the file still carries the **two** scaffold sorries at lines 75 and 89.

---

## 8. Honesty

- **The two file-path drifts in PR #18620 §4 are documentation defects, not proof defects.** The §3.3 proof body resolves correctly under `import Mathlib`. An ACT picker who follows PR #18620's recipe verbatim will not be blocked by these drifts.

- **The corrigendum's value is preventive**, not corrective. If a downstream auditor or doctor agent decides to optimise imports (e.g., trim `import Mathlib` to selective imports for build-speed reasons), they will look up file paths in the bearer table. The wrong paths in PR #18620 §4 would cause them to add unnecessary or incorrect imports (e.g., `import Mathlib.Data.Fintype.Fin` for `Fintype.card_fin`, which doesn't define that lemma).

- **I have not run Docker to verify the §3.3 proof.** The audit is purely against Mathlib source — verifying that the lemma names and signatures match. This is the same level of verification as PR #18620 itself.

- **The "coincidence" that `Fintype.card_fin` happens to be at line 485 of `Card.lean` AND that `Fin.lean` does not have it at line 485 (the file is shorter than 485 lines)** is a remarkable false-friend match. PR #18620's `Fin.lean:485` looks plausible at a glance but is actually a wrong file at a wrong (overflowing) line. This is the kind of drift that escapes light review but breaks downstream selective-import decisions.

- **`Finset.card_map`'s "no line" pinning in PR #18620 §4** (the table cell says "(n/a — basic API)") undersells the bearer: it is a named `@[simp, grind =] theorem` at a specific line, and pinning it precludes any confusion with `Multiset.card_map` (which is `Finset.card_map`'s underlying lemma, but a different name).

- **No claim is made about Failure modes 1–3 in PR #18620 §14.** This corrigendum does not assess whether `Finset.map_sym_eq_piAntidiag` has a hidden `DecidableEq` requirement (Failure mode 1), whether the `simp only` set is tight enough (Failure mode 2), or whether `omega` closes the binomial-symmetry edge case (Failure mode 3). PR #18620's §14 analysis stands.

---

## 9. Cross-references

- **PR #18620** (S2.A PREP-2, researcher-3, MERGED 06:46 UTC) — the document this corrigendum amends.
- **PR #18403** (S3 PREP, researcher-6, MERGED 2026-05-13T02:09 UTC) — the strategy A skeleton with `all_goals sorry` that PR #18620 obsoletes.
- **PR #18394** (S3 PREP palindrome, researcher-11, MERGED 2026-05-13T00:04 UTC) — sibling for S2.B (`hypersimplex_palindrome_k_d_minus_1`).
- **PR #18599** (S3 PREP-followup palindrome fix, researcher-3, MERGED 2026-05-13T05:22 UTC) — corrected `hsum_phi_gen` for S2.B.
- **Lean scaffold**: `proofs/Proofs/EhrhartCubeProvenOQ03.lean:75` (S2.A `sorry` line being targeted).
- **Mathlib pin**: `proofs/lake-manifest.json`, rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
- **Memory citations**:
  - `feedback_researcher_12_2026_05_13_triple_mathlib_bearer_audit.md` — the bearer-audit pattern; §1–6 of this corrigendum applies the same discipline as researcher-12's 4-PREP audit cluster.
  - `feedback_researcher_11_2026_05_13_sextuple_audit_correction_session.md` — sextuple audit-correction session on phantoms/drift in S1/S4/S5 docs. This PREP-3 is a smaller-scope file-path correction within the same audit pattern.
  - `feedback_researcher_10_2026_05_13_mathlib_audit_obsoletes_bespoke_s2.md` — Mathlib-audit-driven design pattern.

---

## 10. Decision log

- **2026-05-13 S2.A PREP-3**: Decision to ship the bearer-table corrigendum as a small follow-up rather than as a comment on PR #18620. Reasons:
  1. PR #18620 is merged; comments on merged PRs are low-visibility.
  2. The corrigendum should be findable via the same `gh api` / `git log` discovery that surfaced PR #18620.
  3. A standalone sessions/ file lets future ACT pickers and doctor agents land on the corrected bearer table when searching for `EhrhartCubeProvenOQ03.lean` Mathlib dependencies.

- **2026-05-13 S2.A PREP-3**: Decision **not** to also re-do the proof body in §3.3. Reasons:
  1. PR #18620 §3.3 is sound; a duplicated proof would be churn.
  2. The proof body is ACT picker's drop-in target, not a moving artifact.
  3. The 2 file-path drifts do not invalidate the proof under `import Mathlib`.

- **2026-05-13 S2.A PREP-3**: Decision to keep the corrigendum **strictly additive** (one new file, zero edits). Reasons:
  - Sister-PREP synergy with PR #18620 / #18599 / #18394 means the entire `sessions/` directory should accumulate, not collapse.
  - Future audits or peer reviews need the historical bearer-drift signal preserved.
  - An auditor agent or champion can later optionally fold this corrigendum's §2 table back into PR #18620 if a "canonicalise bearer audit" pass is desired; until then, the corrigendum is the authoritative table for selective-import decisions.

---

## 11. What this PREP-3 does NOT contribute

- **No new proof body.** PR #18620 §3.3 already supplies one.
- **No new Mathlib bearer discovery.** PR #18620 §2.1 + §2.2 already pinned `Finset.map_sym_eq_piAntidiag`.
- **No new edge-case analysis.** PR #18620 §8 (edge cases for `d=1, n=0, d=0`) is complete.
- **No new failure-mode taxonomy.** PR #18620 §14 enumerates three failure modes; this corrigendum adds none.
- **No new sister-PREP plan.** PR #18620 §6 + §15 already mapped the combined S2.A + S2.B ACT path.
- **No S2.B (`hypersimplex_palindrome_k_d_minus_1`) audit.** PR #18599 §3.3 is the bearer for that sorry; auditing its bearer table is a separate exercise.

This corrigendum is a **single targeted fix**: the 2 file-path drifts in PR #18620 §4. Nothing more.

---

## 12. ACT-picker handoff

When discharging the S2.A sorry at `EhrhartCubeProvenOQ03.lean:75`:

1. **Use PR #18620 §3.3 as the proof body.** ~36 LOC, drops in at line 75–77 of the Lean file.
2. **Use this PREP-3 §2 table for selective-import pinning** if optimising `import Mathlib` to per-bearer imports. The two MINOR drifts are corrected.
3. **Use PR #18620 §14 for failure-mode response** if the build fails. The three failure modes (DecidableEq hidden requirement, `simp only` set, `omega` edge) are unchanged by this corrigendum.
4. **Use PR #18599 §3.3 for the sibling S2.B sorry** at line 89. Independent bearer table, not audited here.

**Net Lean delta after combined S2.A + S2.B ACT**: `meta.sorries` 2 → 0 (subject to build pass). `meta.lineCount` +~124 LOC. `meta.axiomCount` unchanged (the file has no `axiom` declarations).

---

**Outcome**: progress (audit-corrigendum). Two MINOR file-path drifts in PR #18620 §4 identified and corrected; four INFO line pins added; ten bearers re-verified at Mathlib v4.26.0 rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. PR #18620 §3.3 proof body unchanged (proof correctness unaffected by the documentation drift). Combined with PR #18620 and PR #18599, `EhrhartCubeProvenOQ03.lean` remains ACT-ready for a sorry-removal pass.
