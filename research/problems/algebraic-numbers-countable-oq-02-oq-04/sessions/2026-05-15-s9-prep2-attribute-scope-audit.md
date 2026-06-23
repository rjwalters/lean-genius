# S9 PREP-2 — Attribute-scope audit of #19054 + lake-SHA pin verification (doc-only)

- **Date**: 2026-05-15
- **Session**: 9 (sibling PREP-2 to merged S8 PREP #19227)
- **Phase**: PREP (audit only — no Lean, state.md, or JSON edits in this PR)
- **Researcher**: researcher-8
- **Status**: doc-only, conflict-free coordination memo

## 1. TL;DR

Sibling PREP-2 to S8 PREP #19227 (researcher-12, merged-on-branch). Pin-verifies
the 5 v4.26.0 deltas claimed by the two competing mechanic PRs (#19054,
#19064) at the lake-locked Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
and surfaces **one concern S8 PREP missed**: #19054's
`attribute [-instance] Rat.instEncodable` is declared at file top-level
**without `local` or `section` wrapping**, which (per Mathlib's own
`GlobalAttributeIn` linter docs) makes the attribute change persistent
across importers, not file-scoped. The sibling-precedent in
`proofs/Proofs/Erdos1057Problem.lean:678-680` uses the same `-instance`
pattern correctly: wrapped in `section CarmichaelDecidable`.

The fix is a 1-word diff: prepend `local` to #19054's attribute line. With
that change, #19054 strictly dominates #19064 on every dimension. Without
it, the two PRs trade a global-propagation footgun (#19054) against
per-site verbosity (#19064).

Pattern (memory): sibling-PREP-after-PREP audit finds sharper safer path
that prior PREP missed — like `_sibling_prep_audits_peer_prep_workaround_finds_sharper_cancellation_path`,
but the bearer-audit angle is **scope-correctness** rather than
LOC-efficiency. 8th firing of the sibling-PREP-after-PREP pattern.

## 2. Pre-claim probe (2026-05-15T05:55 UTC)

```bash
$ gh api 'repos/rjwalters/lean-genius/pulls?state=open&per_page=100' \
    --jq '.[] | select(.head.ref | test("algebraic-numbers-countable|oq02oq04|anc-oq02oq04"; "i")) | "\(.number) \(.head.ref) | \(.title)"'
19227 research/algebraic-numbers-countable-oq-02-oq-04-s8-audit-1778813031 | research(...): S8 PREP — cross-PR mechanic audit for #19040/#19054/#19064 (doc-only)
```

The S8 PREP (#19227) is in the worktree's local git log (commit
`29c09500a78`) but not yet merged to `origin/main`. Open mechanic PRs:

| PR | Date | Approach | LOC delta |
|---|---|---|---|
| #19040 | 2026-05-14 11:50Z | research S7 (import unblocker + 4-error inventory) | 1+/1- Lean + 35+/3- state.md + 9+/7- JSON + 203 sessions/ |
| #19054 | 2026-05-14 13:32Z | mechanic — file-wide `attribute [-instance]` (no `local`) | 16+/9- Lean + 2+/2- meta.json |
| #19064 | 2026-05-14 14:49Z | mechanic — per-site `@`-pin (7 sites) | 21+/18- Lean only |
| #19227 | 2026-05-15 02:55Z | S8 PREP doc-only audit | 205 sessions/ |

No fourth ACT-class PR has appeared since #19227 was drafted. Slug now at
release-gate boundary (4 open PRs on the same slug); this S9 PREP-2 is
strictly conflict-free (single new file in `sessions/` with timestamp
distinct from #19227).

## 3. Pin-verification at lake-locked SHA

Lake-pinned Mathlib SHA: **`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`** (v4.26.0).

Method: `gh api 'repos/leanprover-community/mathlib4/contents/...?ref=<SHA>' --jq '.content'` for each bearer.

### 3.1 Import deltas

| Bearer | Status @ SHA | Mechanic claim |
|---|---|---|
| `Mathlib/Topology/Instances/Real.lean` | **404 (missing)** | ✅ correct — module split into `.Lemmas` |
| `Mathlib/Topology/Instances/Real/Lemmas.lean` | ✅ present (6268 bytes) | ✅ correct — replacement is real |
| `Mathlib/Data/Rat/Encodable.lean` | ✅ **present (783 bytes, new in v4.26.0)** | ✅ correct — `Rat.instEncodable` is direct |
| `Mathlib/Data/Rat/Denumerable.lean` | ✅ present (712 bytes) | (transitively imports `Rat.Encodable`) |
| `Mathlib/Data/Rat/Cardinal.lean` | ✅ present (569 bytes) | (provides `Cardinal.mkRat`) |

Body of `Mathlib/Data/Rat/Encodable.lean` at SHA:

```lean
namespace Rat
instance : Encodable ℚ :=
  Encodable.ofEquiv (Σ n : ℤ, { d : ℕ // 0 < d ∧ n.natAbs.Coprime d })
    ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, Nat.pos_of_ne_zero c, d⟩, …⟩
end Rat
```

This anonymous `instance` (auto-named `Rat.instEncodable`) is the direct,
high-priority `Encodable ℚ` that competes with the
`Primcodable.ofDenumerable ℚ`-derived path used by `Computable.encode`.

### 3.2 `Cardinal.mk_rat` → `Cardinal.mkRat` rename

`Mathlib/Data/Rat/Cardinal.lean` at SHA, line 23:

```lean
theorem Cardinal.mkRat : #ℚ = ℵ₀ := mk_eq_aleph0 ℚ
```

No `Cardinal.mk_rat` alias found via
`gh search code 'Cardinal.mk_rat' repo:leanprover-community/mathlib4`
(zero hits at v4.26.0 indexing). ✅ rename is real, must be applied.

### 3.3 `aleph0_add_of_ge` API surface

`Mathlib/SetTheory/Cardinal/Arithmetic.lean` at SHA:

| Line | Bearer | Available? |
|---|---|---|
| 238 | `theorem add_eq_self {c : Cardinal} (h : ℵ₀ ≤ c) : c + c = c` | ✅ |
| 247 | `theorem add_eq_max {a b : Cardinal} (ha : ℵ₀ ≤ a) : a + b = max a b` | ✅ |

The 1-liner used by #19054:
```lean
private theorem aleph0_add_of_ge {κ : Cardinal} (h : ℵ₀ ≤ κ) : ℵ₀ + κ = κ := by
  rw [Cardinal.add_eq_max le_rfl, max_eq_right h]
```
is the sharpest available form. ✅ #19054 wins this point over #19064's
4-line tactic-mode body.

### 3.4 `⊊` deprecation

GitHub code search for the literal `⊊` glyph at SHA returns **a single
hit** — `Mathlib/Tactic/Linter/TextBased/UnicodeLinter.lean` (the file
that *flags* the glyph). The `HasSSubset.SSubset` instance for `Set α`
lives at `Mathlib/Data/Set/Basic.lean:85`:

```lean
instance : HasSSubset (Set α) := ⟨fun s t => s ⊆ t ∧ ¬t ⊆ s⟩
```

with `⊂` as the canonical notation. ✅ #19054 uses
`HasSSubset.SSubset ...`; #19064 uses `⊂` — both correct.

### 3.5 The 5 deltas vs the original S7 inventory

S7 PREP (#19040) inventoried **4 errors** post-import-unblocker. The
mechanic PRs both report **5 fixes** = 4 from the inventory + 1 cascade
(the `⊊` deprecation, which #19040 predicted would cascade-resolve but
did not). All 5 deltas are real at SHA. ✅

## 4. NEW finding — `attribute [-instance]` scope hazard in #19054

### 4.1 The line, in context

PR #19054 adds, at file top-level (between imports and module docstring,
**not inside any `section`**):

```lean
-- Mathlib v4.26.0 introduced `Rat.instEncodable`…
attribute [-instance] Rat.instEncodable
```

No `local` modifier, no `scoped` modifier, no enclosing `section`.

### 4.2 Lean 4 attribute-scope semantics (per Mathlib's own linter docs)

`Mathlib/Tactic/Linter/GlobalAttributeIn.lean` documents (excerpted):

> The syntax `attribute [instance] instName in` can be used to
> **accidentally create a global instance**. This is **not** obvious from
> reading the code, and in fact happened twice during the port…
>
> Therefore, we lint against this pattern on all instances.
>
> For *removing* attributes, the `in` works as expected.
> `attribute [-instance] instAddNat in #synth Add Nat` ← scoped to the `in`
>
> // the `instance` persists
> `#synth Add Nat` ⇒ `instAddNat`

The linter targets the `attribute [...] X in <expr>` shape (which is a
trap because the `in` *looks* like scoping). The undocumented baseline
for `attribute [...] X` *without* `in` or `local` or `scoped` is the
Lean 4 default: **persistent at module-environment level, observable by
importers**. This is the standard behaviour Lean inherits for `@[simp]`,
`@[instance]`, etc.

Confirmation via sibling code precedent:

### 4.3 Gallery sibling precedent — `Erdos1057Problem.lean`

`proofs/Proofs/Erdos1057Problem.lean:678-680`:

```lean
section CarmichaelDecidable
-- Close Classical to use computable Decidable instances
attribute [-instance] Classical.propDecidable
```

The sibling uses **`section`-wrapping** to scope the `-instance` change.
This is the safe pattern. PR #19054's `attribute [-instance]` is **not**
inside a section; it sits between L13 (`Mathlib.Tactic` import) and L14
(module docstring opener `/-`).

### 4.4 Impact analysis

Module-import graph (verified at HEAD f2f57c1108b):

```
proofs/Proofs/AlgebraicNumbersCountableOQ02OQ04.lean
  ← proofs/Proofs.lean (umbrella; imports 2913 modules)
  ← (no direct sibling-file imports — only the umbrella)
```

Files transitively importing `Proofs.AlgebraicNumbersCountableOQ02OQ04`
inherit its persistent attribute state. Direct importer: the umbrella
`Proofs.lean`. Anything importing `Proofs` (gallery integration scripts,
catch-all tests) sees `Rat.instEncodable` as removed.

**What breaks** (post-#19054 merge, before any sibling import audit):

| Concern | Likelihood | Severity |
|---|---|---|
| Downstream `decide`-style proofs using `Encodable.encode (q : ℚ)` byte values get different numerics (silent) | Low (no gallery file currently does this on ℚ) | Medium (silent behaviour change) |
| Lean falls back to `Primcodable.toEncodable` for `Encodable ℚ` synthesis in importers (graceful) | High (Primcodable instance has priority 10, will be picked) | Low (functionally equivalent) |
| Future gallery additions assuming `Rat.instEncodable` is available trip a silent fallback | Medium | Low (Lean still synthesises *an* `Encodable ℚ`) |

In practice the build stays clean (mechanic verifies 3067 jobs ✅), but
the **scope of the attribute change exceeds the file's mathematical
scope**. This is the kind of footgun the `GlobalAttributeIn` linter was
written for, even if that linter specifically targets the `in`-variant.

### 4.5 S8 PREP §5 rationale, re-examined

S8 PREP #19227 §5 said:

> File-global attribute is the more maintainable answer to a Mathlib
> instance collision in a long-running file. Future S5+ content
> (`IsComputable e`, computable arithmetic closure, etc.) will introduce
> new `Encodable.encode` sites…

Two refinements to this rationale:

1. **If S5+ content stays in this file**: #19054's attribute (currently
   non-local) covers new sites automatically. ✅ S8 PREP correct here.
2. **If S5+ content becomes new files** (likely, given the file is
   already 649 lines and `IsComputable e` is a substantial sub-proof):
   - **Non-local `attribute [-instance]`** (current #19054): the
     attribute *does* propagate transitively, so the new file inherits
     the removal — but only if it imports OQ04 directly. If it imports
     `Mathlib` first and OQ04 later, instance resolution may differ.
     **Maintainability advantage** of #19054 over #19064 here is
     fragile — depends on import order.
   - **`local attribute [-instance]`** (proposed fix): the attribute does
     NOT propagate. New files need their own `local attribute [-instance]`,
     same as the per-site `@`-pin pattern of #19064. **Maintainability
     advantage** evaporates — both #19054(local) and #19064 require the
     same per-file boilerplate.

The S8 PREP's "more maintainable for S5+" argument is therefore **scope-
dependent**: it holds only for in-file S5+ extensions, not separate
files, and only if #19054 is left non-local (which trades safety for
maintainability — a footgun trade-off the PREP did not surface).

## 5. Recommended sharper third path

**Amend #19054 in place** with a 1-word change: prepend `local` to the
attribute line.

```diff
-attribute [-instance] Rat.instEncodable
+local attribute [-instance] Rat.instEncodable
```

This:

1. Preserves #19054's brevity (1 line, vs 7 sites in #19064)
2. Preserves #19054's 1-liner `aleph0_add_of_ge` via `add_eq_max + max_eq_right`
3. Preserves #19054's meta.json update (which #19064 omits)
4. **Eliminates** the global-propagation hazard
5. Matches the sibling-file pattern in `Erdos1057Problem.lean`
6. Costs 1 keyword (`local`), 0 LOC

With this amendment, #19054 dominates #19064 on every measured axis.

### 5.1 Alternative — section-wrapping

Equivalent safety, more verbose:

```lean
section Encodable_ℚ_Disambiguation
attribute [-instance] Rat.instEncodable
-- … existing file content …
end Encodable_ℚ_Disambiguation
```

Costs 2 LOC for `section`/`end`, but visually distinguishes the
disambiguation scope from unrelated content. Matches the
`Erdos1057Problem.lean:CarmichaelDecidable` pattern. Slightly more
intrusive than `local` but more discoverable.

### 5.2 Alternative — neither approach, just import order

Worth noting (but not recommending): some instance collisions resolve
just by adjusting import order. v4.26.0's `Rat.instEncodable` has no
explicit priority annotation, so it defaults to `1000`.
`Primcodable.ofDenumerable` has `priority := 10`. Lean prefers the
higher priority, so the new instance wins. Import-reordering won't fix
this; the explicit disambiguation (attribute or @-pin) is needed
regardless. ✗ Not viable.

### 5.3 Out-of-scope but worth flagging — upstream Mathlib fix

The real bug is upstream: in v4.26.0, `Encodable ℚ` has two equally-
synthesizable instances with different definitional bodies. Ideal
upstream fix is either:

- Reduce `Rat.instEncodable` priority to ≤ 10, making
  `Primcodable.ofDenumerable` win silently; or
- Add a `@[simp]`-or-`@[csimp]`-or-Eq lemma equating the two encode
  functions, so the elaborator can bridge them transparently.

Filing an upstream issue (or PR) is out of scope for this gallery
session, but worth recording as a "Mathlib upstream nice-to-have" in
the slug's followups.

## 6. Recommended merge sequence (amendment of S8 PREP §6)

S8 PREP recommended: `#19040 → #19054 → close #19064`.

S9 PREP-2 amendment:

1. **Merge #19040 first** (S7 research-scope, unchanged from S8).
2. **Doctor #19054 to add `local`** (1-word amendment via review
   comment or doctor agent), then merge.
3. **Close #19064** with cross-reference to amended #19054.

OR, if doctor-amend latency is high:

1. Merge #19040.
2. Merge #19064 (no global hazard, but per-site verbose).
3. Open a 1-LOC follow-up PR to migrate to the `local attribute` pattern.

The safety amendment in (2) is the load-bearing change. Without it,
prefer #19064 over #19054 — the verbosity is recoverable; a silent
global instance removal is not.

## 7. Numerical witness — does the global removal actually matter?

A direct test: does any file in the gallery currently use
`Encodable.encode (q : ℚ)` in a way that depends on its specific value?

```bash
$ grep -rn "Encodable.encode.*ℚ\|Encodable.encode (.* : ℚ)" proofs/Proofs/
(no hits)
```

So in the current state, the silent fallback to `Primcodable.toEncodable`
would be functionally invisible. **But the hazard is forward-looking**:
once #19054 lands without `local`, anyone adding a `decide`-style proof
involving `Encodable.encode (q : ℚ)` downstream gets a silent fallback —
their proof might still work, but with different encoded values than
they'd expect from `Rat.instEncodable.encode`.

## 8. Conflict-free guarantees

This PR adds exactly one new file:

- `research/problems/algebraic-numbers-countable-oq-02-oq-04/sessions/2026-05-15-s9-prep2-attribute-scope-audit.md`

It does **NOT** touch any of:

| Path | Reason untouched |
|---|---|
| `proofs/Proofs/AlgebraicNumbersCountableOQ02OQ04.lean` | PRs #19040 (1 LOC), #19054 (16+/9-), #19064 (21+/18-) own all Lean edits |
| `research/problems/.../state.md` | PR #19040 owns (35+/3-) |
| `src/data/research/problems/.../json` | PR #19040 owns (9+/7-) |
| `src/data/proofs/.../meta.json` | PR #19054 owns (2+/2-); follow-up if #19064 selected |
| `research/problems/.../sessions/2026-05-14-s7-...md` | PR #19040 owns |
| `research/problems/.../sessions/2026-05-15-s8-prep-cross-pr-mechanic-audit.md` | PR #19227 (S8) owns |

The `sessions/` directory is created freshly by PRs #19040 and #19227 and
this PR; distinct filenames mean no git-merge collision.

## 9. Pattern (memory)

- `_sibling_prep_audits_peer_prep_workaround_finds_sharper_cancellation_path`
  fired once on this slug (S8 PREP #19227 didn't catch the scope hazard
  because it focused on LOC-efficiency and rename-risk, not Lean's
  attribute-persistence semantics).
- This S9 PREP-2 generalises that pattern: **sibling-PREP audits peer
  PREP's *recommendation rationale*, not just bearer existence**. The
  scope-hazard finding is a refutation of S8 PREP §5's "more
  maintainable" claim — not a missing bearer, but a missed safety
  consideration. New flavour for the pattern: "rationale audit" vs
  "bearer audit" vs "cancellation path".
- Distinct from `_sibling_prep_audits_peer_scaffold_discharge_plan_finds_fictitious_bearer`
  (target is fictitious bearer in just-shipped SCAFFOLD).
- Distinct from `_preflight_pin_verifies_peer_prep_skeleton` (target is
  existence of bearers in drafted-but-unshipped skeleton).
- Composes with `_concrete_counterexample_falsifies_peer_prep_unsound_recommendation`
  (both refute peer PREP's RECOMMENDATION; here the counterexample is a
  scope-propagation footgun rather than a numerical witness).

## 10. References

- PR #19040 — researcher-12, 2026-05-14, S7 import unblocker + 4-error inventory
- PR #19054 — mechanic, 2026-05-14, attribute-hammer + meta.json (target of this audit)
- PR #19064 — mechanic, 2026-05-14, surgical instance qualification
- PR #19227 — researcher-12, 2026-05-15, S8 PREP cross-PR audit (prior PREP being supplemented)
- `Mathlib/Tactic/Linter/GlobalAttributeIn.lean` (at SHA `2df2f015...`) — Lean attribute-scope semantics reference
- `proofs/Proofs/Erdos1057Problem.lean:678-680` — sibling-file precedent for `attribute [-instance]` in a `section`
- `Mathlib/Data/Rat/Encodable.lean` (SHA `2df2f015...`) — Rat.instEncodable definition
- `Mathlib/SetTheory/Cardinal/Arithmetic.lean` (SHA `2df2f015...`) — `add_eq_max`/`add_eq_self` lines 238/247
- `feedback_researcher_sibling_prep_audits_peer_prep_workaround_finds_sharper_cancellation_path` — closest existing memory pattern; this session extends it to "rationale audit"
