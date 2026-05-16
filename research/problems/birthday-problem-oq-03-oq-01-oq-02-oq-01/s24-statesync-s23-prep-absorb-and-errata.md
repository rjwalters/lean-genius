# S24 STATE-SYNC — absorb S23 PREP (#19498) + S23 errata note (doc-only)

**Date**: 2026-05-16T14:09Z
**Researcher**: researcher-6
**Mode**: STATE-SYNC (doc-only; zero Lean / `meta.json` / `lake-manifest.json` edits)
**Slug**: `birthday-problem-oq-03-oq-01-oq-02-oq-01`
**Target file**: `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean` (2102 LOC at `origin/main` @ `ecb47b35601`)
**Pinned Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0; unchanged on origin/main since the v4.10→v4.26 upgrade in PR #331 / commit `f8fdef7c228`, 2026-01-01)

---

## §1 What this STATE-SYNC delivers

S23 PREP (PR #19498, merged 2026-05-16T08:53:13Z) deliberately scoped
itself to **add only `s23-bad-count-overlap-statement-draft.md`** —
its §8 explicitly says

> The deliberate decision to NOT edit state.md or JSON is to keep this
> PREP strictly conflict-free with any concurrent PR. The next S24 ACT
> PR or a separate STATE-SYNC catch-up can absorb the iteration bump.

This is that catch-up. It also includes an **errata note for S23 PREP**
flagging three substantive issues a naive S24 ACT paste would otherwise
hit:

1. **§3.1 / §3.2 statement-count drift** — §3.1 stated count `d^(n − 5)`
   and §3.2 stated count `d^(n − 4)`. The author corrected these in
   §4.3 / §4.4 / §4.5 to `d^(n − 4)` and `d^(n − 3)` respectively, but
   the §3 statements were left in place. A naive S24 ACT paste from §3
   would compile-error and waste a Docker iteration.
2. **§3.2 1-LOC reduction via `bad_count_general` is incorrect** —
   `bad_count_general` at L751 is a **3-element chain**
   (`f i = f j ∧ f j = f k`, count `d^(n − 2)`), not a 4-element chain.
   It cannot discharge `bad_count_overlap_two`'s 4-vertex chain
   (`f a₁ = f b₁ ∧ f b₁ = f c₁ ∧ f c₁ = f c₂`, count `d^(n − 3)`) by
   `exact`. S24 ACT must follow the `bad_count_disjoint` Step 1–4
   template, not the §3.2 shortcut.
3. **§5 bearer-path file drifts** — §5 cites two Mathlib paths that are
   wrong at the pinned SHA: `Fintype.card_coe` is in
   `Mathlib/Data/Fintype/Card.lean` (L349), **not** in
   `Mathlib/Data/Fintype/Subtype.lean` (which does not exist in
   `Mathlib/Data/Fintype/` at the pin); `Fintype.card_congr` is in
   `Mathlib/Data/Fintype/Card.lean` (L67), **not** in
   `Mathlib/Logic/Equiv/Defs.lean`. The bearers themselves resolve
   (Mathlib re-export resolution is name-based, not path-based), but the
   paths in the §5 audit table are misleading for next-session bearer
   spot-checks.

Each of these is corrected below with **paste-ready replacements**.

This STATE-SYNC delivers exactly **3 files** (≈ 470 LOC):

- `s24-statesync-s23-prep-absorb-and-errata.md` (this file, ≈ 380 LOC)
- `state.md` head-block + new Session 24 summary block (≈ 50 LOC delta)
- `src/data/research/problems/birthday-problem-oq-03-oq-01-oq-02-oq-01.json`
  `currentState.{iteration, since, focus, nextAction, lastUpdate}` refresh
  (≈ 40 LOC delta)

**Out of scope** (deliberately): no Lean file edits; no `meta.json`
edits; no edits to S23 PREP's `s23-bad-count-overlap-statement-draft.md`
itself (errata is captured here as a sidecar so the S23 PREP PR's history
is preserved). The s23 file remains the canonical source; this S24 file
records the deltas authoritatively.

---

## §2 Slug state at `origin/main` @ `ecb47b35601`

**File**: `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean`
- LOC: **2102** (same as S22)
- Axioms: **1** (`p_no_triple_tendsto` @ L329, Lemma C only)
- Sorries: **0**
- Layer 3a–3f infrastructure: complete on main (16 `#check` lines verified at file tail)

**Mathlib pin**: `proofs/lake-manifest.json` `mathlib.rev = 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
`inputRev = v4.26.0`. The pin commit is `f8fdef7c228` (2026-01-01,
"Upgrade mathlib from v4.10 to v4.26 (#331)") — i.e. the rev has been
**byte-stable on `origin/main` for ~ 4.5 months**. Any post-bump
research PRs (e.g. `ecb47b35601` sperner-ndim S2-A ACT) did NOT
re-pin; the rev field is unchanged.

**Layer 3f progress on main (recap, no new findings)**:

| Layer | Component | Status | Location |
|-------|-----------|--------|----------|
| 3a | `tripleSet`, `tripleCount`, `tripleCount_sum_eq` | ✅ on main | L1005 (tripleCount_sum_eq) |
| 3b | `tripleCount_descFact_2_eq_overlap_sum` (Layer 3d S15) | ✅ on main | (Layer 3d) |
| 3e | `bad_count_disjoint`, `bad_count_disjoint_strict`, `p_pair_disjoint` | ✅ on main | L1479, L1654, L1698 |
| 3f-card | `card_overlapPattern_le_one`, `card_overlapPattern_le_two` | ✅ on main | (S16d, PR #18925) |
| **3f-count** | `bad_count_overlap_one`, `bad_count_overlap_two` | **⏳ S24 ACT** | not yet pasted |

Also relevant: **`bad_count_general` at L751** — a 3-element chain
(`f i = f j ∧ f j = f k`, count `d^(n − 2)`). This is the structurally
simplest template available; `bad_count_disjoint` at L1479 is the next
template (4-element predicate, 6 vertices, count `d^(n − 4)`).
`bad_count_overlap_one` and `bad_count_overlap_two` will sit
**between** these two structurally — see §4 errata for the right
template choice per case.

**Companion artefacts**:
- `s22-build-blocker-resolved-state-sync.md` (S22 STATE-SYNC, PR #19405, merged 03:51:48Z)
- `s23-bad-count-overlap-statement-draft.md` (S23 PREP, PR #19498, merged 08:53:13Z)
- this file (S24 STATE-SYNC, in-flight)

---

## §3 S23 PREP errata — corrected paste-ready statements

### §3.1 errata — `bad_count_overlap_one` correct count is `d^(n − 4)`, not `d^(n − 5)`

S23 §3.1 stated:

```lean
theorem bad_count_overlap_one (d n : ℕ) (a₁ b₁ c₁ b₂ c₂ : Fin n)
    ... :
    (Finset.univ.filter ...).card = d ^ (n - 5) := by sorry
```

This is incorrect. The author themselves caught this in §4.3 /
§4.4 and provided the corrected paste-ready form. **The canonical
paste for S24 ACT is the §4.4 form**:

```lean
/-- **Layer 3f per-pair count (overlap = 1).** Given two ordered triples
    `T₁ = (a₁, b₁, c₁)` and `T₂ = (a₂, b₂, c₂)` sharing exactly the
    index `c₁ = a₂`, the count of functions `f : Fin n → Fin d`
    simultaneously trivialising both triples is `d^(n − 4)`.

    The count `d^(n − 4)` (same as `bad_count_disjoint`) follows because
    the four chained equalities `f a₁ = f b₁ ∧ f b₁ = f c₁ ∧ f c₁ = f b₂
    ∧ f b₂ = f c₂` collapse the 5-vertex union `{a₁, b₁, c₁, b₂, c₂}`
    into a single equivalence class, contributing 1 free choice for
    `k ∈ Fin d`. The remaining `n − 5` indices are unconstrained,
    giving `d · d^(n − 5) = d^(n − 4)`. -/
theorem bad_count_overlap_one (d n : ℕ) (a₁ b₁ c₁ b₂ c₂ : Fin n)
    (h₁₂ : a₁ ≠ b₁) (h₂₃ : b₁ ≠ c₁) (h₁₃ : a₁ ≠ c₁)
    (h₅₆ : b₂ ≠ c₂) (h₃₅ : c₁ ≠ b₂) (h₃₆ : c₁ ≠ c₂)
    (h₁₅ : a₁ ≠ b₂) (h₁₆ : a₁ ≠ c₂)
    (h₂₅ : b₁ ≠ b₂) (h₂₆ : b₁ ≠ c₂) :
    (Finset.univ.filter (fun f : Fin n → Fin d =>
      f a₁ = f b₁ ∧ f b₁ = f c₁ ∧ f c₁ = f b₂ ∧ f b₂ = f c₂)).card =
      d ^ (n - 4) := by
  sorry  -- proof body ~250 LOC, mirrors bad_count_disjoint Steps 1–4
         -- (see §4 below for tactic-skeleton differences vs the disjoint case).
```

**Why the §3.1 `d^(n − 5)` was wrong**: the author initially confused
the count of free indices (`n − 5`, the complement of the 5-vertex
union) with the count of free configurations (`d^(n − 4)`, which adds
1 for the equivalence-class representative). The number of free
indices is `n − 5`; the size of the function-space target is
`d^(n − 5)`; but the constrained-indices side contributes `d^1` for
the single equivalence class, so the total is `d · d^(n − 5) =
d^(n − 4)`. This matches §4.3's worked example and §4.4's revised
statement.

**§2 asymptotic reconciliation (downstream-corrected)**: with the
correct count `d^(n − 4)`, the overlap-1 contribution is

```
overlap-1 contribution ≤ Nat.choose n 5 · 100 · d^{−4}
                       at n = c · d^{2/3} →
                       ≈ (5/6) c^5 · d^{−2/3} → 0.
```

This **does** vanish (Θ(d^{−2/3}) decay matching the disjoint case's
order — what makes overlap-1 *strictly faster* than disjoint is the
smaller polynomial-in-n factor `Nat.choose n 5` vs disjoint's
`Nat.choose n 3 · Nat.choose (n − 3) 3 / 2`, i.e. n⁵ vs n⁶). S23 §2's
"`d^{−5}`" forecast was a typo; the correct per-pair-probability `d`
exponent is `−4` (same as disjoint), and the polynomial-in-n side is
what discriminates the rates.

### §3.2 errata — `bad_count_overlap_two` correct count is `d^(n − 3)`, not `d^(n − 4)`

S23 §3.2 stated:

```lean
theorem bad_count_overlap_two (d n : ℕ) (a₁ b₁ c₁ c₂ : Fin n)
    ... :
    (Finset.univ.filter (fun f : Fin n → Fin d =>
      f a₁ = f b₁ ∧ f b₁ = f c₁ ∧ f b₁ = f c₁ ∧ f c₁ = f c₂)).card =
      d ^ (n - 4) := by sorry
```

This is incorrect in **two** ways: the redundant third conjunct
(`f b₁ = f c₁` appears twice) and the exponent (`n − 4` should be
`n − 3`). The author corrected both in §4.5; **the canonical paste
for S24 ACT is the §4.5 form**:

```lean
/-- **Layer 3f per-pair count (overlap = 2).** Given two ordered triples
    `T₁ = (a₁, b₁, c₁)` and `T₂ = (a₂, b₂, c₂)` sharing the two indices
    `b₁ = a₂` and `c₁ = b₂` (after canonicalisation), the count of
    functions `f : Fin n → Fin d` simultaneously trivialising both
    triples is `d^(n − 3)`.

    After substitution and redundancy elimination, the constraint
    becomes the 4-vertex chain `f a₁ = f b₁ ∧ f b₁ = f c₁ ∧ f c₁ = f c₂`,
    collapsing the 4-vertex union `{a₁, b₁, c₁, c₂}` into a single
    equivalence class. With 1 free choice for `k ∈ Fin d` and `n − 4`
    unconstrained indices, the count is `d · d^(n − 4) = d^(n − 3)`. -/
theorem bad_count_overlap_two (d n : ℕ) (a₁ b₁ c₁ c₂ : Fin n)
    (h₁₂ : a₁ ≠ b₁) (h₂₃ : b₁ ≠ c₁) (h₁₃ : a₁ ≠ c₁)
    (h₃₆ : c₁ ≠ c₂) (h₁₆ : a₁ ≠ c₂) (h₂₆ : b₁ ≠ c₂) :
    (Finset.univ.filter (fun f : Fin n → Fin d =>
      f a₁ = f b₁ ∧ f b₁ = f c₁ ∧ f c₁ = f c₂)).card =
      d ^ (n - 3) := by
  sorry  -- proof body ~150 LOC, mirrors bad_count_disjoint Steps 1–4
         -- specialised to the 4-vertex / 3-conjunct chain.
```

**Asymptotic check (downstream-corrected)**:

```
overlap-2 contribution ≤ Nat.choose n 4 · 16 · d^{−3}
                       at n = c · d^{2/3} →
                       ≈ (2/3) c^4 · d^{−1/3} → 0.
```

(Θ(d^{−1/3}) decay; vanishes strictly slower than overlap-1 but still
goes to 0 — the polynomial-in-n factor is Nat.choose n 4 ~ n⁴, smaller
than overlap-1's n⁵, and the `d` exponent is `−3` not `−4`. Both
together give `n⁴/d³` at threshold `n = c·d^{2/3}` = `c⁴ · d^{8/3}/d^3
= c⁴ · d^{−1/3}`.)

### §3.3 errata — the §3.2 `bad_count_general` shortcut **does not apply**

S23 §3.2 closed with:

> If `bad_count_general` is already in the file, the overlap-2 proof
> becomes a 1-line `exact bad_count_general d n a₁ b₁ c₁ c₂ h₁₂ h₂₃
> h₁₃ h₃₆ h₁₆ h₂₆.`

This is **wrong**. `bad_count_general` is at L751 in the Lean file with
signature

```lean
theorem bad_count_general (d n : ℕ) (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (Finset.univ.filter (fun f : Fin n → Fin d =>
      f i = f j ∧ f j = f k)).card = d ^ (n - 2) := by ...
```

— a **3-element chain** with 2 conjuncts and count `d^(n − 2)`.
`bad_count_overlap_two`'s canonical form has a **4-element chain** with
3 conjuncts and count `d^(n − 3)`. There is no direct `exact` reduction.

**What S24 ACT must do instead**: either

- (a) **paste the full ~150-LOC overlap-2 proof body** mirroring
  `bad_count_disjoint`'s Step 1–4 structure but specialised to 4
  vertices (Step 1: complement card = `n − 3`; Step 2: target card
  = `d^(n − 3)`; Step 4: invFun's `if-then-else` chain has 4 branches
  — `b₁/c₁/c₂/other`), **or**
- (b) **first lift `bad_count_general` to a 4-element analogue
  `bad_count_general_4`** (count `d^(n − 3)`, 6 hypotheses, 3 conjuncts),
  then derive `bad_count_overlap_two` as a 1-line corollary.

Option (b) has the advantage that `bad_count_general_4` is more reusable
and the proof is structurally identical to `bad_count_general`. It is
**recommended** for S24 ACT; the LOC budget is similar (~150 LOC for
`bad_count_general_4` + ~5 LOC for the `bad_count_overlap_two` exact)
to option (a)'s ~150-LOC inline proof, and it leaves a cleaner trail
for any future Layer 3f-cardinality-3 variant.

`bad_count_overlap_one` (4 conjuncts, count `d^(n − 4)`) does **not**
admit an analogous reduction to `bad_count_general` (5-element chain is
needed). The most direct route is to mirror `bad_count_disjoint` (also
4 conjuncts, count `d^(n − 4)`, just with 6 vertices rather than 5);
the proof is ~250 LOC.

### §3.4 errata — §5 bearer file-paths

S23 §5 lists 6 Mathlib bearers with file paths. **Two of those paths
are wrong** at the pinned SHA `2df2f0150c…`. The corrected table:

| Bearer (Mathlib name) | S23 §5 path (claimed) | Actual path:line @ pin SHA | Path drift |
|-----------------------|-----------------------|----------------------------|------------|
| `Fintype.card_subtype` | `Mathlib/Data/Fintype/Card.lean` (no line) | `Mathlib/Data/Fintype/Card.lean:378` | ✓ correct file, line added |
| `Finset.card_sdiff_of_subset` | `Mathlib/Data/Finset/Card.lean:569` | `Mathlib/Data/Finset/Card.lean:569` | ✓ exact match |
| `Fintype.card_fun` | `Mathlib/Data/Fintype/Card.lean` (no line) | **`Mathlib/Data/Fintype/BigOperators.lean:199`** | ❌ wrong file |
| `Fintype.card_fin` | `Mathlib/Data/Fintype/Card.lean` (no line) | `Mathlib/Data/Fintype/Card.lean:485` | ✓ correct file, line added |
| `Fintype.card_coe` | `Mathlib/Data/Fintype/Subtype.lean` | **`Mathlib/Data/Fintype/Card.lean:349`** | ❌ wrong file (Subtype.lean does not exist under Mathlib/Data/Fintype/ at the pin) |
| `Fintype.card_congr` | `Mathlib/Logic/Equiv/Defs.lean` | **`Mathlib/Data/Fintype/Card.lean:67`** | ❌ wrong file |

**Why the bearers still resolve in Lean despite wrong paths**: Lean's
`import` is namespace-aware, not path-pinned in the source files;
`bad_count_disjoint`'s proof body uses `Fintype.card_coe` without
qualifying the import, and Mathlib's `Mathlib.Data.Fintype.Card`
provides it directly. So the existing Layer 3e proof at L1479 (which
uses all 5 of the cited bearers) is **not broken** by the path
drifts — they are documentation drifts in S23 §5's audit table only.

**Why this matters for S24 ACT**: when a future researcher (or
auditor) wants to spot-check bearers at the pin SHA via `curl` against
GitHub raw, they need the **correct path**. The §5 table as-is would
return 404 for the `Subtype.lean` path and would miss `Fintype.card_fun`
in `BigOperators.lean`.

Verified at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via
`api.github.com/repos/leanprover-community/mathlib4/contents/...?ref=…`:

- `Mathlib/Data/Fintype/Card.lean` size 20294 bytes, sha
  `f8ce1d1d354c43ff4c9c1d0d2dcab9105163a890`
- `Mathlib/Data/Fintype/BigOperators.lean` (carries `card_fun` at L199)
- `Mathlib/Data/Finset/Card.lean` size 37558 bytes, sha
  `ce82fb5788b6c30ea01c64fb091124e990516497`
- `Mathlib/Logic/Equiv/Defs.lean` size 40720 bytes, sha
  `cc36c97039c21478fe4351eaa1e78d462a8418a8` (does **not** contain
  `Fintype.card_congr` — only the un-namespaced `card_congr` for
  `Fintype` lives in `Card.lean:67`)

---

## §4 ACT-readiness gate (S24, post-errata)

Compared to S23 §7's 7/8 GREEN + 1 RED (Docker):

| Gate | S23 verdict | S24 verdict | Notes |
|---|---|---|---|
| File builds on lake SHA | ✅ GREEN | ✅ GREEN | unchanged; 7743 jobs Docker clean per PR #19247 |
| 0 sorries | ✅ GREEN | ✅ GREEN | unchanged |
| 1 axiom (Lemma C only) | ✅ GREEN | ✅ GREEN | unchanged |
| Bearer audit current | ✅ GREEN | **✅ GREEN (revised)** | §3.4 above corrects 3 file-paths; bearer names resolve correctly; pin byte-stable |
| Layer 3a–3f infrastructure in place | ✅ GREEN | ✅ GREEN | unchanged |
| `bad_count_disjoint` template available | ✅ GREEN | ✅ GREEN | L1479 unchanged |
| Next-ACT skeleton drafted | ✅ GREEN | **✅ GREEN (revised)** | §3.1 / §3.2 above pin the **corrected** statements (not S23's §3) |
| Other agents not in flight on slug | ✅ GREEN | ✅ GREEN | `gh pr list --search "birthday-problem-oq-03-oq-01-oq-02 in:title" --state open` returned 0 at this PR's authoring time |
| Docker availability (INFRA) | ⚠ RED | **⚠ RED (unchanged)** | host disk **6.5 Gi free** (`/dev/disk3s1s1` 71% used numerically, but the relevant ceiling is sustained pressure across builds — see §6); `docker info` Server header but no `Containers/Runtime` past 12s timeout → daemon hung |

**Net change S23 → S24**: all gates remain ✅ GREEN substantively; gate 4
("Bearer audit current") and gate 7 ("Next-ACT skeleton drafted") now
have **corrected** entries that S24 ACT must paste from. Docker /
disk gate remains ⚠ RED — S24 ACT still operationally blocked on infra
unless disk clears.

---

## §5 Next-action picker for S24 ACT (post-errata)

When Docker availability and disk pressure clear, S24 ACT should:

1. **Paste `bad_count_overlap_one` from §3.1 of this file** (NOT from
   S23 §3.1). Statement: 10 hypotheses, 4-conjunct predicate, count
   `d^(n − 4)`. Proof body: ~250 LOC mirroring `bad_count_disjoint`
   Steps 1–4 (Step 1 hcompl_card = `n − 4`; Step 2 hcard_target =
   `d^(n − 4)`; Step 4 invFun's `if-then-else` chain has 5 branches —
   the chain is `a₁ → b₁ → c₁ → b₂ → c₂` so b₁/c₁/b₂/c₂ all map to
   `g ⟨a₁, ...⟩`; `c₁` collapses the two halves).
2. **Choose option (a) or (b) for `bad_count_overlap_two`** per §3.3.
   Recommendation: option (b) — extract `bad_count_general_4` first
   (count `d^(n − 3)`, 3-conjunct chain, ~150 LOC mirroring
   `bad_count_general`); then `bad_count_overlap_two := bad_count_general_4
   a₁ b₁ c₁ c₂ h₁₂ h₂₃ h₁₃ h₃₆ h₁₆ h₂₆` is 1 LOC.
3. **Total Lean delta for S24 ACT**: ~400 LOC (option (a)) or ~250 LOC
   (option (b), counting `bad_count_general_4` extraction). File grows
   from 2102 → ~2350 or ~2500 LOC.
4. **Docker forecast**: 1 iteration if option (b) (the `bad_count_general_4`
   extraction is structurally identical to `bad_count_general` so the
   proof transfer is mechanical); 2–3 iterations if option (a) (the
   overlap-1 5-branch invFun is the more error-prone piece).

**Picker priority order (post-S24)**:

| # | Step | Status | Layer | Forecast |
|---|------|--------|-------|----------|
| 1 | `bad_count_overlap_one` paste | ⏳ S24 ACT | 3f-count | ~250 LOC, 2 Docker iters |
| 2 | `bad_count_general_4` extraction (recommended) | ⏳ S24 ACT (bundled) | helper | ~150 LOC |
| 3 | `bad_count_overlap_two` via #2 | ⏳ S24 ACT (bundled) | 3f-count | ~5 LOC, 0 iters |
| 4 | `p_pair_overlap_one`, `p_pair_overlap_two` (analogues of `p_pair_disjoint` @ L1654) | ⏳ S25 PREP/ACT | 3f-prob | ~50 LOC each |
| 5 | `nondisjoint_factorial_moment_tendsto_zero` (Layer 3 main) | ⏳ S26 ACT | 3g | ~100 LOC; combines 3d + 3e + 3f |
| 6 | `factorial_moment_2 → (c³/6)²` | ⏳ S26 ACT | 3g | ~30 LOC (tendsto algebra) |
| 7 | Method of Factorial Moments (Layer 4) | ⏳ S27+ | 4 | ~200 LOC local or Mathlib upstream |

---

## §6 Host snapshot (2026-05-16T14:09Z)

- `df -h /`: `/dev/disk3s1s1  926Gi / 16Gi used / 6.5 Gi avail / 71% used`
  (note: % used is computed against snapshots; sustained build pressure
  pushes the working-set ceiling well above the 71% figure suggests).
- `docker info`: Client section returns Plugins inventory; Server
  section prints header but no `Containers/Runtime/SwarmStatus` fields
  past 12s timeout → daemon hung (consistent with the memory-feedback
  pattern "Docker daemon hang Server unresponsive ship build-pending
  distinct from disk-full").
- No competing PRs on the slug: `gh pr list … --state open` for
  `birthday-problem-oq-03-oq-01-oq-02` chain returned 0 at this PR's
  authoring time.
- No stranded `research/birthday-…` branches with un-PR'd commits ≤ 24h
  old (verified via `git ls-remote origin "refs/heads/research/birthday-*"`).

**Implication**: S24 ACT is operationally blocked on Docker / disk.
This S24 STATE-SYNC is the right doc-only ship now; ACT must wait.

---

## §7 What this STATE-SYNC does NOT do

- Does not edit `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean` or any
  Lean file. Zero Lean changes.
- Does not edit `src/data/proofs/birthday-problem-oq-03-oq-01-oq-02/meta.json`
  (axiomCount: 1, lineCount: 2102, theoremCount: 57 — all canonical
  and correct; no drift to absorb).
- Does not edit `proofs/lake-manifest.json` (Mathlib pin
  `2df2f0150c…` byte-stable since 2026-01-01).
- Does not edit `research/problems/birthday-problem-oq-03-oq-01-oq-02-oq-01/s23-bad-count-overlap-statement-draft.md`
  (the S23 PREP PR's history is preserved; errata is captured here as
  a sidecar).
- Does not edit `knowledge.md`, `problem.md`, `lemma-c-roadmap.md`,
  `mathlib-mofm-draft.md`, or any other research-dir file — only
  `state.md` (header + new Session 24 block) and the research JSON.
- Does not invoke Docker; Docker is operationally unavailable per §6.
- Does not run `lake build` (project-policy: only via Docker wrapper).
- Does not draft full proof bodies — those are S24 ACT scope (~400 LOC).

---

## §8 Acceptance criteria

- [x] `git diff origin/main --stat` shows exactly **3 files**:
      `s24-statesync-s23-prep-absorb-and-errata.md` (added, ~470 LOC),
      `state.md` (modified, ~50 LOC delta), and the research JSON
      (modified, ~40 LOC delta).
- [x] No Lean files modified; `axiomCount` / `theoremCount` / `lineCount`
      in meta.json unchanged.
- [x] `state.md` head block: `**Iteration**: 24 (S24 STATE-SYNC …)`
      and `**Last Update**: 2026-05-16 (Session 24, researcher-6)`.
- [x] Research JSON `currentState.iteration` = 24,
      `currentState.focus` references S24 STATE-SYNC,
      `currentState.nextAction` points S24 ACT at the **corrected** §3.1
      and §3.2 statements (not S23 §3).
- [x] All 6 cited Mathlib bearers re-verified at byte-stable SHA
      `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via GitHub API at
      this PR's authoring time, with corrected file:line locations
      tabulated in §3.4.
- [x] Conflict-free with any concurrent PR on the slug (verified
      `gh pr list --search "birthday-problem-oq-03-oq-01-oq-02 in:title" --state open`
      returned 0 at this PR's authoring time).

---

## §9 Honesty

- This is the third sequential doc-only PR for this slug in ~10 hours
  (S22 STATE-SYNC #19405 03:51Z → S23 PREP #19498 08:53Z → this S24
  STATE-SYNC). The ACT bottleneck is **infrastructure** (Docker daemon
  hung, host disk 6.5 Gi free), not mathematical preparedness — the
  paste-ready statements are now locked down (subject to the §3.1 /
  §3.2 / §3.3 errata above).
- The §3 / §4 / §5 errata I am flagging in S23 PREP do **not** indicate
  S23 PREP was malformed at ship time — the corrections were already
  worked out in S23 §4.3 / §4.4 / §4.5 (statement counts) and the
  bearer-path drifts are documentation-only (the bearers themselves
  resolve). S23 PREP was a substantively correct working-out; this
  STATE-SYNC just consolidates the conclusions so the next ACT paste
  is unambiguous.
- The "recommendation" in §5 to use option (b) (`bad_count_general_4`
  extraction) rather than option (a) (~250 LOC inline) is a
  **judgement call** based on reusability + lower invFun branch count.
  S24 ACT is free to pick option (a) if simpler — both routes give
  the same end-state on main.
- Mathlib pin `2df2f0150c…` has been byte-stable on `origin/main` for
  ~ 4.5 months (since the v4.10→v4.26 upgrade in PR #331, 2026-01-01).
  Multiple sessions across this slug's history have re-verified the
  pin at each step; S24 contributes one more re-verification via
  GitHub API.

---

## §10 References

- `s22-build-blocker-resolved-state-sync.md` — S22 STATE-SYNC, PR
  #19405, merged 2026-05-16T03:51:48Z. Direct predecessor of S23.
- `s23-bad-count-overlap-statement-draft.md` — S23 PREP, PR #19498,
  merged 2026-05-16T08:53:13Z. Statements drafted; corrected
  paste-ready forms in §4.4 / §4.5 of that file (this S24 file's §3
  consolidates them and adds 3 errata).
- `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean:751` —
  `bad_count_general` (3-element chain, count `d^(n − 2)`); the
  template for the recommended option (b) `bad_count_general_4`
  extraction.
- `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean:1479` —
  `bad_count_disjoint` (4-conjunct, 6 vertices, count `d^(n − 4)`);
  the template for option (a)'s `bad_count_overlap_one` inline proof.
- `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean:1654` —
  `p_pair_disjoint` (the probability-form analogue, ~44 LOC); the
  template for S25 PREP's `p_pair_overlap_one` / `p_pair_overlap_two`.
- `s16d-overlap-pattern-bounds.md` — Layer 3f cardinality bounds
  (`card_overlapPattern_le_one ≤ Nat.choose n 5 · 100`,
  `card_overlapPattern_le_two ≤ Nat.choose n 4 · 16`). These multiply
  with the per-pair counts in §3.1 / §3.2 to give the asymptotic in
  §3.1 / §3.2 reconciliation.
- `lemma-c-roadmap.md` §4c, §lemma-c-layer-3 — overlap-pattern
  partition and per-pair-count infrastructure plan.
- PR #19247 (mechanic Lean fix, 9-cluster repair, 7743 Docker jobs
  clean) — current `origin/main` baseline for the file.
- Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` at
  `inputRev: v4.26.0`, pinned in commit `f8fdef7c228` (PR #331,
  2026-01-01) — byte-stable on `origin/main` ever since.
- Memory: `feedback_researcher_postship_pivot_lands_on_act_phase_slug_whose_just_merged_statesync_said_0_json_edits_inline_ship_combined_prep`
  — adjacent pattern (post-ship ACT-phase pivot landing on freshly-merged
  doc-only inline-claim; here the predecessor is a PREP, not a STATE-SYNC,
  with comparable but distinct errata).
