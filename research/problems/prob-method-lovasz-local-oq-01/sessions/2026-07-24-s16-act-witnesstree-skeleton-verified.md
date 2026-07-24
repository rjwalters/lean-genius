# S16 ACT — OQ-01-B WitnessTree skeleton landed + Docker-verified (v4.31)

**Date**: 2026-07-24
**Researcher**: researcher-2
**Mode**: ACT (substantive Lean delivery, build-verified)
**Branch**: `research/lovasz-oq01-s16-witnesstree-verified`

## 1. What shipped

The S13 PREP §3 skeleton (design memo
`2026-06-12-s13-prep-witnesstree-encoding.md`) is now landed in
`proofs/Proofs/MoserTardos.lean` as a new **Part VI** and Docker-verified at
the current toolchain pin:

- **Toolchain**: `leanprover/lean4:v4.31.0`, Mathlib rev `9a9483a9`
- **Build**: `./proofs/scripts/docker-build.sh Proofs.MoserTardos` —
  **8576 jobs, exit 0** (Mathlib cache hit 8560/8560)
- **File delta**: 522 → 580 lines (+60/-2 net vs `origin/main`)
- **Sorries/axioms**: 0 new sorries, 0 new axioms (file remains 0/0)

Declarations added (namespace `MTProblem.WitnessTree`):

| Decl | Kind | Notes |
|------|------|-------|
| `WitnessTree P` | `inductive` | `node (label : Fin P.numEvents) (children : List (WitnessTree P))` — List children per S13 strict-positivity resolution (Finset = Quotient of Multiset fails nested positivity) |
| `labelOf` | `def` | root label projection |
| `labelOf_node` | `@[simp] theorem` | `rfl` |
| `inclNbhd i` | `noncomputable def` | `insert i (P.collisionAdj i)` = Γ⁺(i); **noncomputable required** — `collisionAdj` is noncomputable (Fixup commit b188453e01) |
| `self_mem_inclNbhd` | `@[simp] theorem` | `Finset.mem_insert_self` |
| `isProper` | `def` (recursive) | Nodup labels ∧ labels ⊆ Γ⁺(parent) ∧ children proper |
| `isProper_leaf` | `@[simp] theorem` | leaves are proper, by `simp [isProper]` |

## 2. Recursion-form outcome (S13 §5 risk resolved)

S13 ranked three candidate recursion forms for `isProper`, uncertain which
would pass Lean's termination/structural check. The **primary form won**:

```lean
def isProper : WitnessTree P → Prop
  | .node i ch =>
      (ch.map labelOf).Nodup
      ∧ (∀ t ∈ ch, labelOf t ∈ inclNbhd (P := P) i)
      ∧ ∀ t ∈ ch, isProper t
```

`∀ t ∈ ch, isProper t` (recursive call on a subterm bound by list membership)
elaborates directly via structural recursion at v4.31 — no `termination_by
sizeOf`, no mutual `isProperList` helper, no `List.Forall` needed. The ranked
fallbacks were held in reserve and never used.

## 3. Deviation from the S13 plan

S13 proposed also shipping `DecidablePred (isProper (P := P))`. **Deferred**:
`inclNbhd` depends on `collisionAdj`, which is `noncomputable` (defined via
set-builder Finset.filter over `P.isBad` semantic collision, itself
classical), so a `Decidable` instance is not derivable without reworking
`collisionAdj` computability — out of scope for the skeleton and not on the
critical path (the S17+ probability bound sums over trees abstractly; no
`decide` usage planned).

The one build repair needed: the first commit declared `inclNbhd` as a plain
`def`, and the compiler rejected it because of the `collisionAdj` dependency
(`noncomputable` marker required). Fixed in b188453e01.

## 4. Where this sits in the roadmap

OQ-01-B = witness trees (S6-S8 estimate in the original roadmap, realized as
S13 PREP + S16 ACT so far):

- [x] S13 PREP — encoding design
- [x] **S16 ACT (this session)** — `inductive WitnessTree` + `isProper` landed + verified
- [ ] S17+ — `witness_valid` (execution-log extraction produces proper trees)
- [ ] S18+ — `witness_prob_bd` (Pr[τ appears] ≤ ∏_v uniformDrawProb (labelOf v)),
      consuming `LLLAdmissibleUniform.lll_uniform` from S12's Part V
- [ ] then OQ-01-C — Galton–Watson sum bound (`gwTreeProb`, `gw_sum_bound`)

## 5. Gate flips (S15 GATE-SYNC reverted)

S14/S15 flagged BLOCKED (Docker daemon down) and propagated the flag to the
gates `claim-random` reads. This session **empirically confirms Docker is
back** (build succeeded), so per the S15 un-block instruction the gates are
reverted: JSON `status`/`phase`/`currentState.phase` → `active`/`ACT`/`ACT`;
pool → `available` (set after claim release).

## 6. Honesty block

- This is a **skeleton** landing: type + invariant + 3 sanity lemmas. No
  probability content was proved this session. The mathematical weight of
  OQ-01-B is in `witness_valid`/`witness_prob_bd`, still ahead.
- The sanity lemmas are `rfl`/`simp`-trivial by design (API surface, not
  results).
- Net Lean delta is +58 lines; the value is unblocking S17+ on a verified
  foundation and resolving the S13 recursion-form uncertainty.
