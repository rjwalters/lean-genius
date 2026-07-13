# S2-β-γ ACT — binary-split packaging (researcher-2, 2026-06-12)

**Mode**: ACT (Lean, build-verified)
**PR**: research/fodor-oq04-binary-split-packaging
**Outcome**: +73 LOC to `proofs/Proofs/FodorPressingDown.lean` (654 → 727),
new `§ Part X`, 2 theorems, 0 sorries, 0 axioms, Docker **3062 jobs CLEAN**.

## 0. Why this granularity (packaging, not production)

The S3b PREP disjointness drill
(`sessions/2026-05-15-s3b-prep-disjointness-drill.md`) split the binary
Solovay milestone into three layers:

1. Cofinal-sequence picker (shipped: §Part IX, S2-β-β).
2. `fodor_anti_constant` — the index-of-first-disagreement companion.
3. `stationary_splits_binary` — wires everything via `Disjoint`.

Layer 3's disjointness step is described in S3b §4.4 as "mechanical once
`fodor_anti_constant` is in hand." This session ships exactly that
mechanical, high-confidence half — the **packaging reducers** — as
reusable named lemmas, while deliberately *not* attempting the
under-specified `fodor_anti_constant` (Layer 2).

### Why not Layer 2 this session

S3b §4.3 states `fodor_anti_constant`'s key hypothesis `h_pair_distinct`
as `... ∧ True /- some additional structural hypothesis -/` and notes the
disjointness ultimately needs "an ANTI-fodor / counting argument NOT
directly in Mathlib at SHA." The hypothesis is not yet correctly
formulated, so an ACT attempt would risk either a `sorry` or a vacuously /
incorrectly stated lemma. Per the researcher honesty standards, shipping
the provable packaging half now — and flagging Layer 2 as needing a PREP
to pin down `h_pair_distinct` — is the correct call.

## 1. Deliverables

```lean
theorem stationary_splits_of_fiber_compl {κ : Cardinal.{0}}
    {S : Set Ordinal} {P : Ordinal → Prop}
    (h₁ : IsStationaryBelow {α ∈ S | P α} κ.ord)
    (h₂ : IsStationaryBelow {α ∈ S | ¬ P α} κ.ord) :
    ∃ S₁ S₂ : Set Ordinal,
      S₁ ⊆ S ∧ S₂ ⊆ S ∧ Disjoint S₁ S₂ ∧
      IsStationaryBelow S₁ κ.ord ∧ IsStationaryBelow S₂ κ.ord

theorem stationary_splits_of_two_fibers {κ : Cardinal.{0}}
    {S : Set Ordinal} {f : Ordinal → Ordinal} {c₁ c₂ : Ordinal}
    (hc : c₁ ≠ c₂)
    (h₁ : IsStationaryBelow (S ∩ f ⁻¹' {c₁}) κ.ord)
    (h₂ : IsStationaryBelow (S ∩ f ⁻¹' {c₂}) κ.ord) :
    ∃ S₁ S₂ : Set Ordinal,
      S₁ ⊆ S ∧ S₂ ⊆ S ∧ Disjoint S₁ S₂ ∧
      IsStationaryBelow S₁ κ.ord ∧ IsStationaryBelow S₂ κ.ord
```

- `stationary_splits_of_fiber_compl` is the canonical consumer of a
  `fodor_anti_constant` two-conjunct output (`{α ∈ S | g₀ α = β₀ ∧ g₁ α = β₁}`
  vs `{α ∈ S | g₀ α ≠ β₀ ∨ g₁ α ≠ β₁}` are exactly `P` / `¬ P`).
- `stationary_splits_of_two_fibers` is the "two-Fodor" route packaging
  (S3 PREP §4.3): one regressive `f` with stationary fibers at two
  distinct values.

Proofs use only `Set.disjoint_left`, `Set.inter_subset_left`,
`Set.mem_preimage`, `Set.mem_singleton_iff`, and the supplied
stationarity hypotheses. No new imports; no new Mathlib bearers.

## 2. Build verification

```
$ ./proofs/scripts/docker-build.sh Proofs.FodorPressingDown
⚠ [3062/3062] Built Proofs.FodorPressingDown (13s)
warning: Proofs/FodorPressingDown.lean:261:5: unused variable `hS_pos`
warning: Proofs/FodorPressingDown.lean:344:34: unused variable `hTS`
Build completed successfully (3062 jobs).
```

Both warnings pre-existing (`fodor` / `IsStationaryBelow.of_subset`, per
#19052); Part X adds none. Mathlib pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` unchanged.

## 3. Counts

| File | before | after | Δ |
|---|---:|---:|---:|
| `FodorPressingDown.lean` LOC | 654 | 727 | +73 |
| `^theorem ` declarations | 20 | 22 | +2 |
| sorries | 0 | 0 | 0 |
| axioms | 0 | 0 | 0 |

Parent gallery meta `src/data/proofs/fodor-pressing-down/meta.json`
refreshed (`lineCount` 654→727, `theoremCount` 20→22 in both blocks).

## 4. Next (PREP-gated)

`stationary_splits_binary` is now reduced — via the two Part X lemmas — to
*producing* two complementary (or two distinct-value) stationary pieces.
That production is `fodor_anti_constant`. Recommended next step is a PREP
that pins down the correct `h_pair_distinct`: per limit α fix an
increasing cofinal fundamental sequence; two distinct limits' sequences
diverge after their first common term. Build `cofSecond` (Classical.choose
at index 1, `1 < α.cof.ord` via the `cofHead_lt` `aleph0_le_cof` bridge)
and `cofHead_lt_cofSecond`, then route the disagreement set into
`stationary_splits_of_fiber_compl`.
