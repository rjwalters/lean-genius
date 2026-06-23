# S2-β-δ PREP — `cofSecond` bearer confirmation + ready-to-build code

**Date**: 2026-06-14
**Researcher**: researcher-1
**Mode**: PREP (build-free; Docker verification blackout continues)
**Type**: Doc-only. No edits to `proofs/Proofs/FodorPressingDown.lean`
(stays 727 LOC, 0 sorries, 0 axioms, Docker-GREEN as of S2-β-γ 2026-06-12).
Edits limited to this memo, `state.md`, and the canonical research JSON.
**Lake-pinned Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(unchanged).

## Headline

**Resolved one of the two open design uncertainties on the `cofSecond`
route.** The S2-β-γ `nextAction` proposed building a second-term regressive
`cofSecond` (Classical.choose at index 1) plus a `cofHead_lt_cofSecond`
strict ordering, but flagged uncertainty: *"needs `1 < α.cof.ord` via the
`cofHead_lt` `aleph0_le_cof` bridge"* and left open whether the strict
ordering between the 0-th and 1-st terms is even available at the pin.

**Both are available.** A direct read of the pinned Mathlib
`Mathlib/SetTheory/Cardinal/Cofinality.lean` confirms
`IsFundamentalSequence.strict_mono` exists and has exactly the shape needed.
`cofSecond`, `cofSecond_lt`, and `cofHead_lt_cofSecond` are therefore all
provable at the pin — no new Mathlib bearer required. Ready-to-build code is
given in §3 below.

**Scope honesty (unchanged BLOCKED verdict).** This advances the
*infrastructure* front only. `cofSecond` is **necessary but not sufficient**
for the binary split: the genuine obstacle remains the
index-of-first-disagreement *counting* argument that produces two
complementary stationary pieces (S3b §4.3 `h_pair_distinct`). `cofSecond`
gives a second regressive function to press down on, but two regressive
functions each constant-on-a-stationary-subset does **not** by itself yield
two disjoint stationary pieces (Fodor gives a constant value on a stationary
*subset*; the within-`S` complement need not be stationary). The slug stays
**BLOCKED** on (a) the counting argument and (b) the Docker blackout.

## 1. The bearer (verbatim from pinned Mathlib)

`Mathlib/SetTheory/Cardinal/Cofinality.lean` at the pin:

```lean
def IsFundamentalSequence (a o : Ordinal.{u}) (f : ∀ b < o, Ordinal.{u}) : Prop :=
  o ≤ a.cof.ord ∧ (∀ {i j} (hi hj), i < j → f i hi < f j hj) ∧ blsub.{u, u} o f = a

protected theorem IsFundamentalSequence.strict_mono (hf : IsFundamentalSequence a o f) {i j} :
    ∀ hi hj, i < j → f i hi < f j hj := hf.2.1

protected theorem IsFundamentalSequence.lt {a o : Ordinal} {s : Π p < o, Ordinal}
    (h : IsFundamentalSequence a o s) {p : Ordinal} (hp : p < o) : s p hp < a := ...
```

`exists_fundamental_sequence (a) : ∃ f, IsFundamentalSequence a a.cof.ord f`
is the existing chooser already used by `cofHead` (file line 476).
Crucially, **`cofHead` and `cofSecond` both project the same chosen
sequence** `(Ordinal.exists_fundamental_sequence α).choose` — a single
deterministic `Classical.choose` term — so `strict_mono` applies between
their 0-th and 1-st terms directly. No "same-sequence" side condition to
discharge.

## 2. The `1 < α.cof.ord` gate (the other flagged uncertainty)

For `IsSuccLimit α`, the existing `cofHead_lt` proof already derives
`0 < α.cof.ord` from `ℵ₀ ≤ α.cof` (`Ordinal.aleph0_le_cof.mpr hα`) ⇒
`(ℵ₀).ord ≤ α.cof.ord` ⇒ `ω₀ ≤ α.cof.ord`. The **same** chain gives
`1 < α.cof.ord` by replacing `Ordinal.omega0_pos : 0 < ω₀` with
`Ordinal.one_lt_omega0 : 1 < ω₀` (already used elsewhere in this file at
line 396). So the index-1 gate is a one-token edit of the index-0 gate
proof.

## 3. Ready-to-build code (drop-in for §Part IX, when Docker is restored)

```lean
/-- **1-st element of the same chosen fundamental sequence** used by `cofHead`. -/
noncomputable def cofSecond (α : Ordinal) : Ordinal :=
  if h : (1 : Ordinal) < α.cof.ord then
    (Ordinal.exists_fundamental_sequence α).choose 1 h
  else 0

/-- For `IsSuccLimit α`, `1 < α.cof.ord`. -/
theorem one_lt_cof_ord {α : Ordinal} (hα : IsSuccLimit α) : (1 : Ordinal) < α.cof.ord := by
  have h_aleph0 : ℵ₀ ≤ α.cof := Ordinal.aleph0_le_cof.mpr hα
  have h_ord_le : (ℵ₀ : Cardinal).ord ≤ α.cof.ord := Cardinal.ord_le_ord.mpr h_aleph0
  rw [Cardinal.ord_aleph0] at h_ord_le
  exact lt_of_lt_of_le Ordinal.one_lt_omega0 h_ord_le

/-- `cofSecond α < α` for `IsSuccLimit α` (regressivity). -/
theorem cofSecond_lt {α : Ordinal} (hα : IsSuccLimit α) : cofSecond α < α := by
  have h1 : (1 : Ordinal) < α.cof.ord := one_lt_cof_ord hα
  simp only [cofSecond, dif_pos h1]
  exact (Ordinal.exists_fundamental_sequence α).choose_spec.lt h1

/-- `cofHead α < cofSecond α` for `IsSuccLimit α` (strict ordering of the
    0-th and 1-st terms of the shared chosen fundamental sequence). -/
theorem cofHead_lt_cofSecond {α : Ordinal} (hα : IsSuccLimit α) :
    cofHead α < cofSecond α := by
  have h0 : (0 : Ordinal) < α.cof.ord := lt_trans Ordinal.zero_lt_one (one_lt_cof_ord hα)
  have h1 : (1 : Ordinal) < α.cof.ord := one_lt_cof_ord hα
  simp only [cofHead, dif_pos h0, cofSecond, dif_pos h1]
  exact (Ordinal.exists_fundamental_sequence α).choose_spec.strict_mono h0 h1 Ordinal.zero_lt_one
```

Notes for the ACT writer:
- `cofHead`'s gate is `0 < α.cof.ord`; reuse `h0` above so the `dif_pos`
  rewrites line up. (The existing `cofHead_lt` builds its own `h_cof_pos`
  inline — either form works; `h0` above derives it from `one_lt_cof_ord`
  for brevity.)
- `Ordinal.zero_lt_one` / `Ordinal.one_lt_omega0` / `Ordinal.omega0_pos`
  are all already imported and used in this file.
- Proof-irrelevance handles the `dif_pos` proof terms vs the `strict_mono`
  `hi hj` arguments; if `simp` leaves a mismatch, `exact`-with-explicit
  proofs (as written) closes it.
- These 4 declarations are **independently useful, low-risk, ~20 LOC**, and
  should be shipped as a standalone verified increment — they do not depend
  on, and are not blocked by, the unresolved counting argument.

## 4. Why this still does NOT close the binary split

The two packaging reducers already on file
(`stationary_splits_of_fiber_compl`, `stationary_splits_of_two_fibers`)
consume **two complementary / two-distinct-value stationary pieces**.
`cofHead` (and now `cofSecond`) each give, via `fodor`, a constant value on
*one* stationary subset. To feed the packagers you must show a *second*
stationary piece exists — e.g. that
`{α ∈ S | cofHead α ≠ β}` (or a `cofHead`/`cofSecond` disagreement set) is
stationary. That co-stationarity is exactly the
index-of-first-disagreement counting argument, and it is **not** a corollary
of `strict_mono`. Concretely:

- A naive "iterate Fodor on `cofSecond` inside the `cofHead = β` stationary
  set" gives a *decreasing* chain of stationary sets with more agreeing
  initial terms — not two *disjoint* pieces.
- The countable intersection `⋂ₙ {a_n = c_n}` is the natural "all terms
  agree" set, but countable intersections of stationary sets need not be
  stationary, so the contradiction-for-indecomposability step needs the
  genuine Solovay diagonalization, not just `cofSecond`.

So §3 is the right *next infrastructure increment*, but the BLOCKED root
cause (the counting argument + Docker) is unchanged.

## 5. Verdict and recommendation

- **Design front advanced**: `cofSecond` / `cofHead_lt_cofSecond` confirmed
  buildable at the pin via `IsFundamentalSequence.strict_mono` — removes the
  S2-β-γ `nextAction` uncertainty. Ready-to-build code in §3.
- **Slug stays BLOCKED**: (a) Docker verification blackout (cannot machine-
  check new set-theory Lean — shipping unverified is premature, per the
  S2-β-γ BLOCKED note); (b) the index-of-first-disagreement counting
  argument for the co-stationary complement is still undischarged and is the
  true obstacle to `stationary_splits_binary`.
- **Recommended next ACT (Docker-up)**: ship the §3 4-tuple
  (`cofSecond`, `one_lt_cof_ord`, `cofSecond_lt`, `cofHead_lt_cofSecond`) as
  a small verified Part IX extension — high-confidence, independently
  useful, unblocks any future two-index design. *Defer* `fodor_anti_constant`
  / `stationary_splits_binary` until the counting argument is pinned down
  (still needs a dedicated PREP or an upstream Mathlib Solovay-splitting
  bearer).
- **Claim re-released** ahead of TTL expiry.

## Deliverables (this PR, doc-only)

1. NEW session memo: this file.
2. `state.md`: refine the BLOCKED note with the `cofSecond` design-front
   advance (bearer confirmed; ready-to-build code referenced).
3. Canonical JSON: `currentState.nextAction` updated to point at the §3
   verified increment as the first Docker-up move; `lastUpdate` →
   2026-06-14.
