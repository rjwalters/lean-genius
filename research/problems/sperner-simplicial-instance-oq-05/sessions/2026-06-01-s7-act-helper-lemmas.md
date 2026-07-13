# S7 ACT — (C2-1d) Helper Lemmas + Concrete `decide` Soundness (researcher-1, 2026-06-01)

## Why this S7 fires now

S6 ACT (PR #21357, researcher-1, 2026-05-30) shipped the `SpernerSimplicialInstanceOQ05Scarf1d.lean` skeleton — 6 defs + 1 instance + 2 theorems, 1 `sorry` on `scarfWalk_isPanchromatic`, Docker-build verified at Mathlib v4.26.0 SHA `2df2f0150c…`.

S5 PREP §4 sketched a ~40 LOC discharge plan (monotone-walk invariant + no-revisit corollary + fuel-exhaustion impossibility via pigeonhole on `Fin m`). On detailed audit during S7 ACT entry (researcher-1, 2026-06-01), I observed that the current `scarfWalk_isPanchromatic` statement is **unprovable as currently formulated** — and therefore the discharge plan from S5 PREP §4 cannot succeed without first amending the theorem statement to add a parity/endpoint hypothesis.

### S7 audit finding: existing theorem statement is unprovable

```lean
theorem scarfWalk_isPanchromatic (hm : 0 < m) (start : Fin m) (k : Fin 2)
    (h_start : ¬ IsPanchromatic1d c start) :
    IsPanchromatic1d c (scarfWalk c hm start k h_start) := sorry
```

**Counterexample**: `m = 3`, `c ≡ 0` (constant zero colouring), `start = ⟨0, _⟩`, `k = ⟨1, _⟩`.
- No panchromatic cell exists (all consecutive pairs are `(0, 0)`).
- The walk runs: from cell 0 entered through left face k=1, leave through right (k'=0) into cell 1, neither pancho; continue into cell 2; trying to leave cell 2 through right gives `adj 2 0 = none` (right boundary). `step` then returns `.inl 2` (boundary-stuck case), and `scarfWalkAux` returns cell 2 — **non-panchromatic**, contradicting the theorem.
- Alternative path: fuel-exhaustion. If the walk took longer, `scarfWalkAux` returns `start` at fuel 0 — also non-panchromatic.

In short, soundness requires an extra hypothesis (e.g. `c 0 ≠ c m`, the 1-d Sperner endpoint condition). The S5 PREP §4 discharge plan was sketched without this hypothesis and so cannot close as written.

### Decision: defer signature change; ship structural lemmas now

Amending the theorem signature has gallery / cross-reference fallout (the existing `exists_panchromatic_constructive` uses it). The signature change deserves its own S8 PREP memo with downstream impact analysis. For S7, scope to **structural reduction lemmas + concrete `decide`-proven soundness** that future S8+ discharge will need either way — these are net-additive and don't disturb the existing sorry.

## Scope (this S7 ACT)

Net add ~52 LOC to `proofs/Proofs/SpernerSimplicialInstanceOQ05Scarf1d.lean`:

| # | Symbol | Type | Purpose |
|---|---|---|---|
| 1 | `scarfWalk_eq_scarfWalkAux` | theorem | Unfolding: `scarfWalk c hm s k h = scarfWalkAux c hm s k m` |
| 2 | `scarfWalkAux_zero_fuel` | theorem | Base case: `scarfWalkAux _ _ start _ 0 = start` |
| 3 | `scarfWalkAux_of_panchromatic_start` | theorem | Pancho short-circuit at fuel `n+1` |
| 4 | concrete `decide`-proven `example` | example | m=3 / c(n) = ⟦n ≤ 1⟧, start (0,1) walks to a panchromatic cell |

Total: 3 named theorems + 1 anonymous `example` = 4 declarations, **0 sorries** in the S7 additions, **0 axioms**.

File total post-S7: 170 LOC, **1 sorry** (the pre-existing `scarfWalk_isPanchromatic`), **0 axioms**.

## Build verification

```
⚠ [1098/1098] Built Proofs.SpernerSimplicialInstanceOQ05Scarf1d (7.2s)
warning: Proofs/SpernerSimplicialInstanceOQ05Scarf1d.lean:102:8: declaration uses 'sorry'
Build completed successfully (1098 jobs).
=== Build succeeded ===
```

**Result**: **PASS**. Single warning is the pre-existing `scarfWalk_isPanchromatic` sorry (unchanged from S6). All 4 new declarations compile clean. `decide` successfully reduces `IsPanchromatic1d c (scarfWalk c (0 < 3) ⟨0, _⟩ ⟨1, _⟩ _)` to `True` at the kernel — kernel-level verification that the Scarf walk works on this concrete 3-cell instance.

In-session fix: initial `decide` example used `by norm_num` for the `Fin` proofs, which failed (`norm_num` requires `Mathlib.Tactic.NormNum`, not in scope here). Switched to `by decide` for `0 < 3` and `Fin` value bounds — clean.

## Value-add of S7 additions

The three structural lemmas are **syntactic reductions** that any future S8+ discharge will need to perform anyway:

- `scarfWalk_eq_scarfWalkAux` lets you unfold the entry-point definition once and work with `scarfWalkAux` directly, avoiding repeated `unfold scarfWalk` calls.
- `scarfWalkAux_zero_fuel` is the base case of any induction on fuel — needed for the fuel-exhaustion-impossibility step.
- `scarfWalkAux_of_panchromatic_start` lets the induction skip the `if h : IsPanchromatic1d c start` branch in `scarfWalkAux` (which is irrelevant once the walk has terminated at a panchromatic cell).

The `decide`-proven example is the **strongest possible concrete soundness statement**: a kernel-checked proof on a specific instance. It complements the kernel-checked existence demo in `SpernerSimplicialInstanceOQ05.lean` (the C1 brute-force file), giving the slug TWO kernel-level Sperner verifications on the same `intervalTriangulation 3` instance — one through brute force enumeration, one through the Scarf door-walk.

## Next action — S8+ candidates

(a) **S8 PREP: amend `scarfWalk_isPanchromatic` signature** to add a parity hypothesis (likely `c 0 ≠ c m` for the 1-d endpoint condition, or alternatively a "panchromatic cell exists" hypothesis to make soundness conditional on `exists_panchromatic` rather than re-deriving it). Then S8 ACT discharges the amended theorem using the S5 PREP §4 plan (monotone-walk + no-revisit + fuel pigeonhole) plus the S7 structural lemmas. Risk: HIGH — full discharge requires `iadj_cases`-style case analysis on every step's `adj` outcome, plus a strictly-monotone-in-cell-index invariant on the walk's recursive structure.

(b) **S8 ALT: gallery promotion**. Add the Scarf1d leaf file to `meta.json` `leanFile.additionalFiles[]` and `meta.additionalFiles[]` (mirror per the project_mechanic_additionalfiles_format_convention memory). Cleanly orthogonal to (a); could ship as a separate doc-only PR or be bundled into (a)'s ACT.

(c) **S8 ALT: 2-D Hex-no-draw extension**. Gale's 1979 Hex-no-draw theorem can be derived from a 2-D Sperner walk; given a 2-D `Triangulation` instance (e.g. the `m × m` subdivision in C-grid), the same skeleton + a discharged 2-D soundness theorem could give a constructive Hex winner-finder. Deferred — requires the 2-D triangulation instance which is itself ACT-pending under `sperner-simplicial-instance-oq-01` (C2-1d sibling slug).

## Out of scope (NOT touched at S7)

- The pre-existing `scarfWalk_isPanchromatic` sorry — its discharge depends on a signature change deferred to S8 PREP.
- The S5 PREP §4 discharge plan as literally sketched — does not succeed without the signature change documented above.
- Gallery `meta.json` `leanFile.additionalFiles[]` update for the Scarf1d file — mechanic batch territory post-merge OR S8 ALT (b).
- C3 (`findOppositeIdx` Classical.choose → Finset.filter.min'`) — separate slug branch.
- 2-D Sperner walk (C2-gen) — blocked on C3 + the 2-D triangulation instance.

## Ship scope (this S7 ACT)

4 files:
- `proofs/Proofs/SpernerSimplicialInstanceOQ05Scarf1d.lean` — net +52 LOC (118 → 170), 3 new theorems + 1 `decide` example, 0 new sorries, Docker-verified
- `research/problems/sperner-simplicial-instance-oq-05/state.md` — iter 11 → 12, prepend S7 ACT block, S6 ACT preserved
- `src/data/research/problems/sperner-simplicial-instance-oq-05.json` — iter / phase / focus / nextAction / attemptCounts / lastUpdate / builtItems / insights / nextSteps refreshed
- This session memo
