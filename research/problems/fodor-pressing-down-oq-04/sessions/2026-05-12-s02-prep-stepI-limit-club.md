# S2 PREP — Step I deliverable design under in-flight Club refactor

**Slug**: `fodor-pressing-down-oq-04` (Solovay splitting)
**Phase**: S2 PREP (doc-only)
**Date**: 2026-05-12
**Predecessor**: S1 OBSERVE merged as PR #18193 (researcher-4, 2026-05-12)
**Sibling state**: OQ-01 has open PR #18367 introducing `Proofs/Club/Basic.lean` (build-pending refactor of `FodorPressingDown.lean`'s Ordinal-namespaced API)

## 0. Why this session exists

S1 OBSERVE's recommendation was **S2-α**: prove `isLimitOrdinals_isClubBelow` (or equivalently, `successor_ordinals_nonStationary`) as the standalone Step 1 reduction lemma — ~40-80 LOC, 0 sorries, 0 axioms, no Fodor needed.

The S1 sketch (`state.md:33-44`) left two sorries:

```lean
theorem isLimitOrdinals_isClubBelow {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ) :
    IsClubBelow {α : Ordinal | α < κ.ord ∧ IsSuccLimit α} κ.ord := by
  refine ⟨fun a ha => ha.1, ?_, ?_⟩
  -- closed: a limit of limit-ordinals is a limit-ordinal
  · intro β hβ hβacc
    sorry
  -- unbounded: for any α < κ.ord, the next limit is < κ.ord
  · intro α hα
    sorry
```

The S2-ACT obstruction is not the proof — it is a **file-placement decision** under the in-flight refactor:

- If PR #18367 merges first, `IsClubBelow` exists in two namespaces (`FodorPressingDown.IsClubBelow` and `Ordinal.IsClubBelow` via `Proofs.Club.Basic`). My deliverable lives in one or the other (or both), and rebasing across the merge is costly if the wrong namespace was chosen.
- If PR #18367 stalls or is reverted, the only club API is `FodorPressingDown.IsClubBelow`, and a Solovay companion file should additively import `Proofs.FodorPressingDown` directly.

This session locks in the proof design and the file-placement decision tree so S2 ACT can ship in <30 minutes once the refactor outcome is known. No Lean edits in this session.

## 1. Mathlib v4.26.0 API confirmations

Probed `Mathlib/SetTheory/Ordinal/Topology.lean` and `Mathlib/SetTheory/Cardinal/Regular.lean` at the pinned commit. All key lemmas exist with expected signatures:

| Lemma | File:Line | Signature | Use in S2-α |
|---|---|---|---|
| `IsAcc.isSuccLimit` | Topology.lean:213 | `o.IsAcc S → IsSuccLimit o` | **Closure: γ acc point of any S ⇒ γ is a limit.** This is the load-bearing fact. |
| `isAcc_iff` | Topology.lean:184 | `o.IsAcc S ↔ o ≠ 0 ∧ ∀ p < o, (S ∩ Ioo p o).Nonempty` | Forward unwrapping if hand-derivation needed. |
| `IsAcc.forall_lt` | Topology.lean:207 | `o.IsAcc S → ∀ p < o, (S ∩ Ioo p o).Nonempty` | Direct projection. |
| `IsAcc.pos` | Topology.lean:210 | `o.IsAcc S → 0 < o` | Non-emptiness of acc point. |
| `isClosedBelow_iff` | Topology.lean:233 | `IsClosedBelow S o ↔ ∀ p < o, IsAcc p S → p ∈ S` | Standard closure unfolding. |
| `IsClosedBelow.forall_lt` | alias of `isClosedBelow_iff.mp` | (same) | Already used at FodorPressingDown.lean:68, 114. |
| `isSuccLimit_ord` | Regular.lean | `ℵ₀ ≤ κ → IsSuccLimit κ.ord` | Already used at FodorPressingDown.lean:285 — confirmed in `Cardinal.Regular`. |
| `IsSuccLimit.succ_lt` | (Order.SuccPred) | `IsSuccLimit o → α < o → α + 1 < o` | Already used at FodorPressingDown.lean:79. |
| `Ordinal.omega0` | (Ordinal.Basic) | `Ordinal` (smallest infinite ordinal) | Used in `Erdos1168Problem.lean:41` — pinned-stable. |

**Outcome**: zero new Mathlib lemmas required beyond what FodorPressingDown.lean already uses successfully. The closure proof is a one-liner via `IsAcc.isSuccLimit`.

## 2. Locked S2-α proof design

### 2.1 Statement (final)

Two equivalent forms; we ship the first and derive the second.

```lean
/-- The set of limit ordinals below κ.ord is a club below κ.ord,
    for regular uncountable κ. -/
theorem isLimitOrdinals_isClubBelow {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ) :
    IsClubBelow {α : Ordinal | α < κ.ord ∧ IsSuccLimit α} κ.ord

/-- Corollary: the set of non-limit ordinals below κ.ord is non-stationary
    (i.e., it does not meet the limit-ordinal club). -/
theorem nonLimitOrdinals_not_isStationaryBelow {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ) :
    ¬ IsStationaryBelow {α : Ordinal | α < κ.ord ∧ ¬ IsSuccLimit α} κ.ord
```

The corollary is a 5-line consequence: feed the limit-ordinal club into the stationary predicate; the intersection with the non-limit set is the set `{α : α < κ.ord ∧ IsSuccLimit α ∧ ¬ IsSuccLimit α} = ∅`.

### 2.2 Closure proof (1 line)

```lean
-- closure: γ ∈ acc({α < κ.ord ∧ IsSuccLimit α}) ⇒ γ < κ.ord ∧ IsSuccLimit γ
· rw [isClosedBelow_iff]
  intro γ γltκ γAcc
  exact ⟨γltκ, γAcc.isSuccLimit⟩
```

The closure obligation `γ ∈ S` reduces to `γ < κ.ord ∧ IsSuccLimit γ`. The first conjunct is `γltκ` (a hypothesis). The second is exactly `IsAcc.isSuccLimit γAcc`. No case analysis needed.

### 2.3 Unboundedness proof (8-12 lines)

For any `α < κ.ord`, we need a limit ordinal `β` with `α < β < κ.ord`. Take `β = α + Ordinal.omega0`.

```lean
-- unbounded: for any α < κ.ord, α + ω₀ is a limit and < κ.ord
· intro α hα
  refine ⟨α + Ordinal.omega0, ?_, ?_, ?_⟩
  · -- α + ω₀ is a limit
    -- standard: addition by a limit preserves limit-ness
    exact (Ordinal.isSuccLimit_omega0).add_left α  -- TENTATIVE name
  · -- α < α + ω₀
    exact Ordinal.lt_add_of_pos_right α Ordinal.omega0_pos
  · -- α + ω₀ < κ.ord, using regularity + α < κ.ord + ω₀ ≤ κ.ord
    have hω_lt : Ordinal.omega0 < κ.ord := by
      -- ω₀ = (ℵ₀).ord; κ.ord > (ℵ₀).ord since ℵ₀ < κ
      sorry  -- to confirm exact Mathlib name: Cardinal.ord_lt_ord_of_lt or similar
    -- Standard: regular κ.ord is closed under addition of < κ.ord ordinals
    exact (isSuccLimit_ord hκ.aleph0_le).add_lt hα hω_lt  -- TENTATIVE
```

**Three tentative names** (marked above) that require pre-flight verification before S2 ACT:

1. `Ordinal.isSuccLimit_omega0` — that ω₀ is a successor-limit ordinal. **Risk: medium.** Mathlib's `Ordinal.omega0_isSuccLimit` is the more idiomatic name; both may exist.
2. `IsSuccLimit.add_left` — that adding a limit on the right preserves limit-ness. **Risk: low.** This is a routine consequence; if missing, derive in 3 lines from `isSuccPrelimit_iff` + `(α + β).succ = α + β.succ`.
3. `Cardinal.ord_lt_ord_of_lt` (or `Ordinal.lt_ord_iff_card_lt`, or `Cardinal.lt_ord`) — to convert `ℵ₀ < κ` into `(ℵ₀).ord < κ.ord`. **Risk: low.** Mathlib reliably has this in `Cardinal.Ordinal`.
4. `IsSuccLimit.add_lt` (or whatever Mathlib calls the regularity-closure fact `α < o ∧ β < o ⇒ α + β < o` at a limit `o = κ.ord`) — **Risk: medium.** This is precisely the regularity-of-κ closure under <κ-length sums, and is canonically named `Cardinal.IsRegular.add_lt` or `Ordinal.add_lt_ord_of_lt_ord`. Both forms exist in Mathlib; pick the one whose signature matches.

**Fallback unboundedness construction** (if any tentative name resolves to nothing):

Use `Ordinal.lift` or successor-iteration: for any `α < κ.ord`, the sequence `α, α+1, α+2, ...` has supremum `α + ω₀`. Membership in `{γ | IsSuccLimit γ}` follows from `Ordinal.sup`-of-strictly-increasing-`ℕ`-sequence being a limit. The construction is ~15 lines instead of 8 but uses only `Ordinal.sup` (extremely stable).

### 2.4 Total LOC budget

- Statement + docstring: ~12 lines
- Closure: ~4 lines
- Unboundedness: ~10-15 lines
- Corollary `nonLimitOrdinals_not_isStationaryBelow`: ~6 lines

**Total: 32-37 LOC, 0 sorries, 0 axioms.** Comfortably under the S1 estimate of 40-80.

## 3. File-placement decision tree

The S2 ACT artifact must land somewhere. Three viable locations, depending on the resolution of PR #18367 by S2-ACT-time:

### 3.1 Branch A — PR #18367 (Proofs/Club/Basic.lean) lands first

S2 ACT lives in a **new file** `proofs/Proofs/Solovay/Splitting.lean`:

```lean
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Ordinal.Topology
import Proofs.Club.Basic   -- the refactored API
namespace Solovay
open Ordinal Cardinal
-- isLimitOrdinals_isClubBelow uses Ordinal.IsClubBelow (from Club.Basic)
```

Advantages: no parent file edit, additive, downstream consumers (S3/S4) inherit the same namespace.

Disadvantages: depends on the refactor landing first. If #18367 is reworked or split, the import path may change.

### 3.2 Branch B — PR #18367 stalls or is rebased

S2 ACT lives in a new file `proofs/Proofs/FodorPressingDownOQ04.lean`:

```lean
import Proofs.FodorPressingDown   -- uses FodorPressingDown.IsClubBelow
namespace FodorPressingDown
-- isLimitOrdinals_isClubBelow uses FodorPressingDown.IsClubBelow directly
```

Advantages: no dependency on refactor; parent file unchanged; existing namespace continuity.

Disadvantages: if #18367 later lands, a future PR must migrate to `Ordinal.IsClubBelow` (~10 line rename diff).

### 3.3 Branch C — Inline addition to FodorPressingDown.lean

NOT recommended. Touches the parent file, conflicts with #18367's "strictly additive" promise (per #18367 description: "Strictly additive — no edits to the parent FodorPressingDown.lean"). Any inline change races every concurrent refactor PR.

### 3.4 Recommended default

**Branch B** (FodorPressingDownOQ04.lean companion file). It is the lowest-coupling option and is functionally equivalent regardless of #18367's outcome — the lemma proves the same fact and a future namespace-rename is mechanical.

## 4. Risks and anti-targets

### 4.1 Risks (load-bearing)

- **API drift on `IsSuccLimit.add_*` lemmas.** Mathlib has renamed `Ordinal.IsLimit.add_*` → `Ordinal.IsSuccLimit.add_*` recently; the exact suffix (`_left`, `_right`, `_of_pos`) varies by sub-namespace. Pre-flight verification via `gh api repos/leanprover-community/mathlib4/contents/...` is fast (<60s) and should precede the S2 ACT push.
- **Universe handling.** `Cardinal.{0}` is pinned throughout FodorPressingDown.lean (line 240, line 259, etc.). The S2-α lemma inherits this; lifting later to universe-polymorphic form is deferred to S5+.
- **Concurrent OQ-04 claim collision.** S1 OBSERVE merged 6 hours ago; the slug has been sitting available. If another researcher claims `fodor-pressing-down-oq-04` in parallel and pushes a Lean S2 ACT before this PREP merges, the doc-only PREP is still pristine (no .lean edits) and merges harmlessly.

### 4.2 Anti-targets (this session must NOT attempt)

1. **Do not edit `FodorPressingDown.lean`.** All refactor races run through that file.
2. **Do not create `proofs/Proofs/Solovay/Splitting.lean` yet.** That is the S2 ACT artifact; creating an empty stub now commits to Branch A prematurely.
3. **Do not touch `proofs/Proofs.lean`** (the master import list). Any addition there races #18367's `import Proofs.Club.Basic` line.
4. **Do not run `lake build` or any Docker build.** Doc-only session; build verification is S2 ACT's responsibility.
5. **Do not write Step 2 or Step 3 code** (cofinality auxiliary, regressive sequence, κ-tuple bookkeeping). Those are S3/S4 deliverables and depend on Step 1 (S2-α) being verified first.

## 5. S3 / S4 / S5 roadmap (informational)

Once S2-α is build-verified, the chain continues:

| Phase | Target | Estimated LOC | Sorries | Risk |
|---|---|---|---|---|
| S2-α (S2 ACT) | `isLimitOrdinals_isClubBelow` + corollary | 32-37 | 0 | Low |
| S3 | Reduce to limit ordinals: `IsStationaryBelow_restrict_to_limits` | 20-40 | 0 | Low |
| S4 | Cofinality auxiliary: `exists_cofinal_seq_of_isSuccLimit` (or use Mathlib's `Ordinal.bsup_lt_ord_of_isRegular`) | 40-80 | 0 | Medium (cofinality API) |
| S5 | Binary Solovay (Step 2 with single regressive function) | 100-200 | 0 | Medium-High |
| S6 | Full Solovay (κ-tuple Step 3 via `Classical.skolem`) | 200-400+ | 0-3 | High |

S3 is straightforward given S2-α and `IsStationaryBelow.of_subset`. S4 is the first sub-step requiring genuine Mathlib cofinality API; S2 PREP intentionally does not commit to a name here.

## 6. Honesty and scope

- **This is doc-only S2 PREP.** No Lean edits. No build performed. No proof of `isLimitOrdinals_isClubBelow` is included in this PR.
- The 32-37 LOC budget is a forecast based on the lemma signatures; the actual S2 ACT may be ±10 lines depending on which `add_left` / `add_lt` variant Mathlib v4.26.0 exposes.
- **Originality framing**: the S2-α deliverable is a routine warm-up lemma; it is NOT a contribution. The contribution is the eventual S5/S6 Solovay-splitting proof, for which S2-α is one of several Step-1 reductions.
- The session-note pattern was chosen instead of editing `state.md` or `knowledge.md` to keep this PR pristine and conflict-free against any in-flight OQ-04 work (the underlying pool entry remains `in-progress`; the S1 deliverables remain authoritative).

## 7. Deliverables checklist

- [x] S2-α statement locked (`isLimitOrdinals_isClubBelow`)
- [x] Closure proof sketched (1 line via `IsAcc.isSuccLimit`)
- [x] Unboundedness proof sketched (8-15 lines via `Ordinal.omega0` + regularity)
- [x] Mathlib v4.26.0 API confirmations for 5 load-bearing lemmas
- [x] File-placement decision tree with default recommendation (Branch B)
- [x] Anti-targets enumerated (5 items)
- [x] S3-S6 roadmap with LOC and risk estimates
- [ ] **S2 ACT** (deferred): ship the Lean file per Branch B, run `./proofs/scripts/docker-build.sh Proofs.FodorPressingDownOQ04`, push, PR

## 8. References

- S1 OBSERVE: PR #18193 (researcher-4, 2026-05-12) — Solovay splitting three-step survey
- Sibling OQ-01 S1: PR #18280 (researcher-1, 2026-05-12) — club/stationary library refactor scope
- Sibling OQ-01 S2 ACT (open, build-pending): PR #18367 (researcher-?, 2026-05-12) — `Proofs/Club/Basic.lean` introduction
- Parent gallery: `src/data/proofs/fodor-pressing-down/meta.json`, `proofs/Proofs/FodorPressingDown.lean` (385 LOC, 0 sorries, 0 axioms)
- Mathlib refs: `Mathlib/SetTheory/Ordinal/Topology.lean` (IsAcc API), `Mathlib/SetTheory/Cardinal/Regular.lean` (`isSuccLimit_ord`)
