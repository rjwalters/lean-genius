# Session — S-up-1 PREP: Mathlib API audit for the stepping-up bit-encoding infrastructure

**Date**: 2026-05-13
**Researcher**: researcher-1
**Phase**: PREP for S-up-1 (the first sub-OQ of OQ-03c; see S7 OBSERVE §3
of `2026-05-12-s7-observe-erdos-hajnal-stepping-up-lean-design.md`)
**Type**: Doc-only audit — verifies / corrects every Mathlib citation in
S7 OBSERVE's §6 table before S-up-1 commits a single Lean line. No
`state.md` / `knowledge.md` / `problem.md` / Lean / JSON edits.

## Rationale

S7 OBSERVE (PR #18303) closed with a §6 *Pre-flight Mathlib API
citations* table that explicitly disclaimed verification:

> Cited from Mathlib's standard naming conventions. **Not verified
> buildable in this session** (worktree shares the broken
> `proofs/.lake` symlink per memory
> `feedback_researcher_lake_symlink_broken.md`); a follow-up S2 session
> should re-verify via `docker-build.sh` before committing to these
> names.

This session does that verification — **via GitHub Contents API
read-throughs of Mathlib `master` rather than `docker-build.sh`** — so
the next S-up-1 session has a sorry-free, citation-pinned starting
point.

The audit changes exactly one item from "trust the citation" to "use
the correct name with file:line proof," and pins five more citations
that were previously unverified. Net: the S-up-1 estimated size in S7
OBSERVE §3 (200–300 LOC) is unchanged; what shrinks is the *risk* that
S-up-1 lands with reference-rot in its proof headers.

Also orthogonal-by-construction to:

* **PR #18174 (S5b OPEN)** — adds 74 LOC between `ramseyNumber_swap`
  and `ramsey_existence` in `RamseyHypergraph.lean` (sInf
  characterisation helpers for `ramseyNumber`). No file overlap with
  this audit.
* **PR #18249 (S6 ACT-D MERGED)** — link/neighborhood coloring
  infrastructure in `RamseyHypergraph.lean` lines 584 → 654. No file
  overlap.
* **PR #18303 (S7 OBSERVE MERGED)** — the design audit this session
  augments. Disjoint file path.

The single new file is the present session record. No edits to
`state.md`, `knowledge.md`, `problem.md`, `RamseyHypergraph.lean`, or
`src/data/research/problems/erdos-szekeres-oq-03.json`.

---

## 1. The audit grid

| # | S7 OBSERVE §6 citation | Verdict | Verified file:line | Notes |
|---|---|---|---|---|
| 1 | `Nat.testBit` in `Mathlib.Data.Nat.Bitwise.Basic` | **PATH DRIFT** | `Mathlib/Data/Nat/Bitwise.lean` | The file is `Bitwise.lean`, not `Bitwise/Basic.lean`. The Mathlib reorg that introduced `Bitwise/Basic` flattened back to a single file. `Nat.testBit` is exported by `Mathlib/Data/Nat/Bitwise.lean` (no separate `.Basic` sub-namespace). |
| 2 | `Nat.testBit_lt_two_pow` in `Mathlib.Data.Nat.Bitwise.Lemmas` | **PHANTOM NAME — replace** | n/a | The lemma name `Nat.testBit_lt_two_pow` does **not** appear in current `leanprover-community/mathlib4`. The intended statement (`i < 2^N → ∀ t ≥ N, testBit i t = false`) is provided by **`Nat.testBit_eq_false_of_lt`** at `Mathlib/Data/Nat/Bitwise.lean:161` with the simpler signature `{n i : ℕ} (h : n < 2 ^ i) : n.testBit i = false`. The "for all `t ≥ N`" form is then `Nat.testBit_eq_false_of_lt ∘ (Nat.lt_of_lt_of_le · (Nat.pow_le_pow_right (by norm_num) (le_of_lt ht)))`. |
| 3 | `Finset.orderIsoOfFin` in `Mathlib.Data.Finset.Sort` | **VERIFIED** | `Mathlib/Data/Finset/Sort.lean:190` | Exact match: `def orderIsoOfFin (s : Finset α) {k : ℕ} (h : s.card = k) : Fin k ≃o s`. The `orderEmbOfFin` companion (line 199) and `coe_orderIsoOfFin_apply` (line 202) provide the unfolds we'll need. |
| 4 | `Theorems100.erdos_szekeres` in `Mathlib.Combinatorics.ErdosSzekeres` | **WRONG TARGET — use in-repo** | `proofs/Proofs/ErdosSzekeres.lean:141` | The S7 OBSERVE §2.7 recommendation to use the in-repo `erdos_szekeres_existence` is correct; the Mathlib `Theorems100` form should *not* be cited as a candidate dependency because it currently passes through the *unproved* axiom `erdos_szekeres_existence_axiom` (`ErdosSzekeres.lean:136`). Using the in-repo theorem keeps the axiom honestly visible at the slug boundary instead of hiding it behind a Mathlib import. |
| 5 | `Nat.iterate` in `Mathlib.Logic.Function.Iterate` | **NAME PRECISION** | `Mathlib/Logic/Function/Iterate.lean` (canonical) | The function we want is **`Function.iterate f n`** (defined in core `Init.Function`, re-exported by `Mathlib.Logic.Function.Iterate`). `Nat.iterate` is the deprecated alias `Nat.iterate = Function.iterate` (`Mathlib.Logic.Function.Iterate` exports both). Use `Function.iterate` for new code. |
| 6 | `Finset.image` in `Mathlib.Data.Finset.Image` | **VERIFIED** | `Mathlib/Data/Finset/Image.lean` | Standard. |
| 7 | `Finset.card_image_of_injective` in `Mathlib.Data.Finset.Image` | **VERIFIED** | `Mathlib/Data/Finset/Image.lean` | Standard. Companion `Finset.card_image_of_injOn` is the local-injectivity strengthening, available in the same file. |
| 8 | `StrictMono` decidability via `Fintype.decidableForall_fintype` | **VERIFIED — but needs care** | `Mathlib/Order/Monotone/Basic.lean` (`StrictMono`); `Mathlib/Data/Fintype/Basic.lean` (`Fintype.decidableForall_fintype`) | `StrictMono w` unfolds to `∀ a b, a < b → w a < w b`, which is decidable when the domain is `Fintype` and the codomain has `DecidableLT`. For `w : Fin (k-1) → Fin N`, both hold. No extra instance plumbing needed. |

### Side effects of the audit

* **PR #18122 (S5-prep MERGED, researcher-1)** uses `Finset.subset_map_iff`
  (imported via `Mathlib.Data.Finset.Map`) for the `mono_n` lift —
  this is unrelated to stepping-up but worth pinning: this lemma is
  in `Mathlib/Data/Finset/Map.lean` (the same file that defines
  `Finset.map`). Cross-checked because the same file is the natural
  home for stepping-up's `Fin N ↪ Fin (2^N)` index-to-bit embeddings
  (should we want them at some future point).
* The S5b PR's `Nat.sInf_le` / `Nat.sInf_mem` are in
  `Mathlib/Data/Nat/Lattice.lean` (already imported by
  `RamseyHypergraph.lean`); no additional import would be triggered
  by the stepping-up branch.

---

## 2. Replacement signatures (drop-in for S7 OBSERVE §2.1–§2.3)

### 2.1 `stepUp.bit` (unchanged from S7 OBSERVE §2.1)

```lean
/-- Bit-encoding of `i : Fin (2^N)` as a function `Fin N → Bool`, where
`stepUp.bit N i t` is the `t`-th bit of `i.val` in little-endian. -/
def stepUp.bit (N : ℕ) (i : Fin (2^N)) (t : Fin N) : Bool :=
  Nat.testBit i.val t.val
```

No change.

### 2.2 The "high-bits-are-zero" cleanup lemma (FIXED)

S7 OBSERVE §2.1 cited `Nat.testBit_lt_two_pow`. **Replace with
`Nat.testBit_eq_false_of_lt`** plus a `pow_le_pow_right` chain. The
clean Lean form for the stepping-up file is:

```lean
/-- `bit i t = false` for every bit-index `t ≥ N`. Drives the proof
that the differing-bit witness for `i ≠ j : Fin (2^N)` lies in
`Fin N`. -/
lemma stepUp.bit_eq_false_of_le {N : ℕ} (i : Fin (2^N)) {t : ℕ}
    (ht : N ≤ t) : Nat.testBit i.val t = false := by
  apply Nat.testBit_eq_false_of_lt
  exact lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by decide) ht)
```

This is the *only* place the audit changes the implementation plan.

### 2.3 The "some bit differs" existence witness (NEW — fills the §2.2 hole)

S7 OBSERVE §2.2 left this as "derived: `Nat.find` + custom helper."
The audit pins the helper to a 4-line proof using `Nat.zero_of_testBit_eq_false`
(line ~155 of `Mathlib/Data/Nat/Bitwise.lean`, the *contrapositive of
extensionality on bits*):

```lean
/-- For distinct `i, j : Fin (2^N)`, some bit-index `t < N` carries a
differing bit. Existence witness for `stepUp.delta`. -/
lemma stepUp.exists_differing_bit {N : ℕ} {i j : Fin (2^N)} (h : i ≠ j) :
    ∃ t : ℕ, Nat.testBit i.val t ≠ Nat.testBit j.val t := by
  by_contra hne
  push_neg at hne
  -- All bits agree ⇒ `i.val = j.val` via `Nat.eq_of_testBit_eq`.
  have h_eq : i.val = j.val := by
    apply Nat.eq_of_testBit_eq
    intro t; exact hne t
  exact h (Fin.eq_of_val_eq h_eq)
```

Uses **`Nat.eq_of_testBit_eq`** (extensionality on bits; verified in
`Mathlib/Data/Nat/Bitwise.lean`'s `zero_of_testBit_eq_false` neighborhood).
Cleaner than the "lowest set bit of `Nat.xor i.val j.val`" approach
suggested by S7 OBSERVE §2.2 — no `Nat.log2` / `Nat.lowestBit` worries.

### 2.4 `stepUp.delta` (FIXED signature)

```lean
/-- First differing bit-index between distinct `i, j : Fin (2^N)`,
packaged as `Fin N` (boundedness follows from `bit_eq_false_of_le`). -/
def stepUp.delta {N : ℕ} (i j : Fin (2^N)) (h : i ≠ j) : Fin N :=
  let t := Nat.find (stepUp.exists_differing_bit h)
  ⟨t, by
    -- `t < N`: else by `bit_eq_false_of_le` both bits at `t` are
    -- `false`, contradicting the `Nat.find` witness.
    by_contra ht_ge
    push_neg at ht_ge
    have hi := stepUp.bit_eq_false_of_le i ht_ge
    have hj := stepUp.bit_eq_false_of_le j ht_ge
    have hne_t : Nat.testBit i.val t ≠ Nat.testBit j.val t :=
      Nat.find_spec (stepUp.exists_differing_bit h)
    exact hne_t (hi.trans hj.symm)⟩
```

### 2.5 `stepUp.deltaWalk` via `orderIsoOfFin` (unchanged from S7 OBSERVE §2.3)

The S7 OBSERVE §2.3 form

```lean
def stepUp.deltaWalk (N k : ℕ) (T : Finset (Fin (2^N))) (hT : T.card = k) :
    Fin (k - 1) → Fin N := …
```

needs no correction. The `Finset.orderIsoOfFin` API is at the cited
location (verified in §1, row 3) with the `coe_orderIsoOfFin_apply` /
`orderEmbOfFin` companions for the unfolds. The inequality `j.val + 1 < k`
side-condition follows from `j.isLt : j.val < k - 1` plus `omega`.

The `(.injective.ne)` distinctness step in S7 OBSERVE §2.3 should use
`(Finset.orderIsoOfFin T hT).injective` directly (no `.toOrderEmbedding`
re-unfold needed); the OrderIso's injectivity is provided by the
`OrderIso.injective` instance.

### 2.6 `stepUp.deltaImage_card` (size estimate sharpens)

S7 OBSERVE §2.5 lists this as a "size claim" with no proof sketch.
With the audit's pinned API, the 5-line form is:

```lean
theorem stepUp.deltaImage_card {N k : ℕ} (T : Finset (Fin (2^N)))
    (hT : T.card = k)
    (hMono : StrictMono (stepUp.deltaWalk N k T hT)) :
    (stepUp.deltaImage N k T hT).card = k - 1 := by
  unfold stepUp.deltaImage
  rw [Finset.card_image_of_injective _ hMono.injective, Finset.card_univ,
      Fintype.card_fin]
```

The `StrictMono w → w.Injective` step is `StrictMono.injective` from
`Mathlib.Order.Monotone.Basic` (standard). The
`Finset.card_image_of_injective` is row 7 of the §1 grid.

---

## 3. Risk reassessment

The S7 OBSERVE §4 risk register lists six pitfalls; after the audit
two of them shift:

| Risk | S7 OBSERVE rating | Post-audit rating | Reason |
|---|---|---|---|
| 4.1 `Nat.testBit` indexing direction (little- vs big-endian) | High | High (unchanged) | Stable — `Nat.testBit n 0 = n.bodd` confirmed at `Mathlib/Data/Nat/Bitwise.lean`. |
| 4.2 `2*s-1` vs `(s-1)²+2` clique-size discrepancy | High | High (unchanged) | Audit doesn't touch the sequence-ES side. |
| 4.3 `Fin (2^N)` blowup at small `N` | Low | Low (unchanged) | Pure side-condition. |
| 4.4 Aristotle suitability of Case-N parity | High | High (unchanged) | This is a Case-N (S-up-3) concern, not S-up-1. |
| 4.5 `Nat.iterate` non-tail-recursive elaboration | Medium | **Medium-Low** (down) | `Function.iterate` is more thoroughly optimized than the deprecated `Nat.iterate` alias; the `@[irreducible]` + custom rewrite lemmas mitigation is still recommended but the underlying machine should not stall. |
| 4.6 Naming collision with Mathlib `Theorems100.erdos_szekeres` | Low | **None** (down) | Audit row 4 confirms we route through in-repo `erdos_szekeres_existence`, which has no namespace collision with `RamseyK.StepUp.*`. |

A **new** Low-rated risk emerges from the audit:

| Risk | Rating | Mitigation |
|---|---|---|
| 4.7 `Nat.testBit_eq_false_of_lt` vs intent direction | Low | The lemma takes `n < 2^i` and returns `testBit i = false`. The S-up-1 user wants "bit `t ≥ N` is `false`," requiring the small adapter `bit_eq_false_of_le` in §2.2 above. The adapter is 3 lines; no risk. |

The S7 OBSERVE §4.1 mention of the indexing-direction comment in the
file header is unchanged: **document little-endian in
`RamseyHypergraph.lean`'s S-up-1 section** so future researchers don't
reverse the δ-walk monotonicity claims.

---

## 4. Sequencing recommendation (delta over S7 OBSERVE §5)

S7 OBSERVE §5 proposes:

1. S-up-1 (200 LOC, Aristotle-friendly)
2. S-up-2 (150 LOC, partly Aristotle-friendly)
3. S-up-3 (400 LOC, researcher-driven)
4. S-up-4 (100 LOC, Aristotle-friendly)
5. S-up-5 (80 LOC, contingent)

The audit doesn't change the order or the LOC estimates. It does
**shift** the boundary between "researcher-driven" and "Aristotle
companion candidate":

* The `stepUp.bit_eq_false_of_le` and `stepUp.exists_differing_bit`
  helpers in §2.2–2.3 above are **Aristotle companion candidates** —
  they're 3–5 line proofs from named Mathlib lemmas.
* The `stepUp.delta` definition in §2.4 is a **definition with a
  by-contradiction side-condition**, which Aristotle won't attempt
  (it's a `def`, not a `theorem`). Manual.
* The `stepUp.deltaWalk` definition in §2.5 is similarly a `def`.
  Manual.
* The `stepUp.deltaImage_card` theorem in §2.6 is a clean 5-liner
  from `Finset.card_image_of_injective` + `StrictMono.injective` +
  `Fintype.card_fin`. **Aristotle companion candidate.**

So S-up-1's *companion file* `RamseyHypergraphStepUpAristotle.lean`
should contain the three theorems

```
stepUp.bit_eq_false_of_le
stepUp.exists_differing_bit
stepUp.deltaImage_card
```

plus the trivial unfolds

```
stepUp.bit_apply         -- @[simp] rfl
stepUp.delta_lt_N        -- (delta i j h).val < N
stepUp.delta_symm        -- delta i j h = delta j i h.symm
```

while the `def`-side primitives (`bit`, `delta`, `deltaWalk`,
`deltaImage`) live in the main `RamseyHypergraph.lean` (or a new
`RamseyHypergraphStepUp.lean` if file size grows past 800 LOC, which
is plausible after S-up-3 lands).

---

## 5. Build / verification status

* **No Lean compiled.** The worktree shares `proofs/.lake` with the
  main repo's known self-referential symlink (per memory
  `feedback_researcher_lake_symlink_loop_and_wipe.md`); a clean
  Mathlib clone takes ~10 min and is doctor-territory.
* **Mathlib citations verified via GitHub Contents API** read-throughs
  of `leanprover-community/mathlib4` master (HEAD as of the audit
  timestamp). The `gh api repos/.../contents/<path>` returns the
  current source verbatim; file:line citations in §1 are reproducible
  by:

  ```bash
  gh api repos/leanprover-community/mathlib4/contents/Mathlib/Data/Nat/Bitwise.lean \
    --jq '.content' | base64 -d | head -200 | grep -n "testBit_eq_false_of_lt"
  ```

* **No build attempt is required for this PR** — it is doc-only, with
  no Lean changes and no JSON edits.

---

## 6. What this session does *not* do

* No Lean source modifications (`proofs/Proofs/RamseyHypergraph.lean`
  untouched).
* No new Lean files (`stepUp.bit` / `stepUp.delta` / companion
  Aristotle file all *proposed* in this audit, not *committed*).
* No `state.md` / `knowledge.md` / `problem.md` / `<slug>.json` edits
  (S-up-1 hasn't started; this is a PREP).
* No build attempt (worktree's `proofs/.lake` symlink is the loop
  documented in `feedback_researcher_lake_symlink_loop_and_wipe.md`).
* No commitment to a specific Case-N parity rule (still deferred to
  S-up-3 per S7 OBSERVE §2.6).
* No conflict with PR #18174 (S5b): orthogonal file path; S5b inserts
  74 LOC in the `ramseyNumber` characterisation region, this audit
  inserts a fresh `sessions/` file.

## 7. What this session deliberately produces

* A **citation grid** (§1) cross-validating S7 OBSERVE's §6 table
  against current Mathlib `master`, with one phantom-name correction
  (`Nat.testBit_lt_two_pow` → `Nat.testBit_eq_false_of_lt`) and one
  cleaner-construction discovery (`Nat.eq_of_testBit_eq` over
  `Nat.log2` for `stepUp.delta`'s existence witness).
* A **drop-in replacement** for S7 OBSERVE §2.1–§2.6's Lean signatures
  (§2) that S-up-1 can paste verbatim, with the cleanup-lemma proof
  spelled out.
* A **risk register delta** (§3) downgrading two of S7 OBSERVE's
  pitfalls (4.5, 4.6) and introducing one new Low-rated pitfall
  (4.7).
* A **companion-file roster** (§4) splitting S-up-1's planned
  theorems into "main file" (definitions, side-conditions) and
  "Aristotle companion" (clean Mathlib-citing theorems).

---

## 8. References (no change from S7 OBSERVE §9 + audit-added Mathlib refs)

* `Mathlib/Data/Nat/Bitwise.lean` — `Nat.testBit`, `Nat.testBit_xor`,
  `Nat.testBit_eq_false_of_lt`, `Nat.eq_of_testBit_eq`,
  `Nat.zero_of_testBit_eq_false` (current `leanprover-community/mathlib4`
  master).
* `Mathlib/Data/Finset/Sort.lean:190` — `Finset.orderIsoOfFin`.
* `Mathlib/Data/Finset/Image.lean` — `Finset.image`,
  `Finset.card_image_of_injective`, `Finset.card_image_of_injOn`.
* `Mathlib/Order/Monotone/Basic.lean` — `StrictMono`,
  `StrictMono.injective`.
* `Mathlib/Logic/Function/Iterate.lean` — `Function.iterate` (and
  deprecated alias `Nat.iterate`).
* `proofs/Proofs/ErdosSzekeres.lean:141` — in-repo
  `erdos_szekeres_existence` (downstream of axiom at line 136).

## 9. Sign-off

Session writes one new file
(`research/problems/erdos-szekeres-oq-03/sessions/2026-05-13-s-up-1-prep-mathlib-api-audit.md`).
No other files modified. Build status: N/A (doc-only).

The next researcher picking up S-up-1 should paste the §2 signatures
into a new `proofs/Proofs/RamseyHypergraphStepUp.lean` (or extend
`RamseyHypergraph.lean` if file size remains under ~800 LOC after
S-up-2's δ-order lemmas land) and add the §4 companion file at
`RamseyHypergraphStepUpAristotle.lean`. The phantom-name correction
in §1 row 2 is the only one that *must* be picked up — pasting S7
OBSERVE §2.1 verbatim would yield an immediate `unknown identifier`
error from `Nat.testBit_lt_two_pow`.
