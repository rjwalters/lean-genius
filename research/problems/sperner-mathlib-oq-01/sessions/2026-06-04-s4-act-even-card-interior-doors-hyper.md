# S4 ACT — Close `even_card_interior_doors_hyper`

**Date**: 2026-06-04
**Researcher**: researcher-1
**Mode**: ACT
**File touched**: `proofs/Proofs/SpernerMathlibHyper.lean`
**LOC delta**: +40 (342 → 382)
**Sorries**: 3 → 2 (33% reduction)
**Build**: Docker-verified (7744 jobs, 16s build, no Lean errors)

## 0. TL;DR

S4 ACT closes the `even_card_interior_doors_hyper` sorry by applying
`Sperner.even_card_fpf_invol` to the involution `adjMapHyper adj` on the
Σ-type `Σ s : Cell, ι s`. The three side-conditions (involution,
set-stability, fixed-point-free) follow from `hadj_symm`,
`isDoorHyper_iff_of_adj`, and `hadj_ne` respectively, matching the parent
file's `even_card_interior_doors` structure exactly except for one
elaboration quirk in Σ-type land (see §2).

Remaining sorries (2):

* `door_count_parity_hyper` equality case `|ι s| = |P|` (line 189) —
  requires `Fintype.equivOfCardEq` transport.
* `sperner_parity_hyper` finite-sum chain (line 351) — mechanical given
  the §3 and §4 bearers, ~80 LOC of bookkeeping.

## 1. The proof

Length: 41-LOC body (vs. parent's 43-LOC). The structure mirrors the
parent's `even_card_interior_doors` (`SpernerMathlib.lean:423–465`):

```lean
theorem even_card_interior_doors_hyper
    (vertex : VertexMap V Cell ι) (adj : AdjMap Cell ι)
    (hadj_symm : …) (hadj_vertex : …) (hadj_ne : …)
    (top : P) (c : V → P) :
    Even ((Finset.univ : Finset (Σ s : Cell, ι s)).filter
      (fun p => IsDoorHyper vertex c top p.1 p.2 ∧
        adj p.1 p.2 ≠ none)).card := by
  set S := …
  -- Helper: `simp only` doesn't reduce the match in `adjMapHyper`'s body;
  -- we expose the reduction via a local `have`.
  have hMap : ∀ (q : Σ s : Cell, ι s) (sk : Σ s : Cell, ι s),
      adj q.1 q.2 = some sk → adjMapHyper adj q = sk := by
    intro q sk hq; unfold adjMapHyper; rw [hq]
  apply Sperner.even_card_fpf_invol S (adjMapHyper adj)
  · -- involution
    intro p hp
    simp only [S, mem_filter, mem_univ, true_and] at hp
    obtain ⟨_, hadj_ne'⟩ := hp
    obtain ⟨⟨s', k'⟩, hadj_eq⟩ := adjHyper_some_of_ne_none adj p hadj_ne'
    have hadj_back := hadj_symm p.1 p.2 s' k' hadj_eq
    have h1 := hMap p ⟨s', k'⟩ hadj_eq
    have h2 := hMap (⟨s', k'⟩ : Σ s : Cell, ι s) ⟨p.1, p.2⟩ hadj_back
    -- structure-eta closes ⟨p.1, p.2⟩ = p as rfl after the rewrites
    rw [h1, h2]
  · -- set-stability
    intro p hp
    simp only [S, mem_filter, mem_univ, true_and] at hp ⊢
    obtain ⟨hdoor, hadj_ne'⟩ := hp
    obtain ⟨⟨s', k'⟩, hadj_eq⟩ := adjHyper_some_of_ne_none adj p hadj_ne'
    have hadj_back := hadj_symm p.1 p.2 s' k' hadj_eq
    have h1 := hMap p ⟨s', k'⟩ hadj_eq
    rw [h1]
    refine ⟨(isDoorHyper_iff_of_adj vertex adj hadj_vertex hadj_eq).mp hdoor, ?_⟩
    rw [hadj_back]; exact Option.noConfusion
  · -- fixed-point-free
    intro p hp
    simp only [S, mem_filter, mem_univ, true_and] at hp
    obtain ⟨_, hadj_ne'⟩ := hp
    obtain ⟨⟨s', k'⟩, hadj_eq⟩ := adjHyper_some_of_ne_none adj p hadj_ne'
    have h1 := hMap p ⟨s', k'⟩ hadj_eq
    rw [h1]
    intro heq
    exact hadj_ne p.1 p.2 s' k' hadj_eq ((Sigma.eta p).trans heq.symm)
```

## 2. Departures from S2e PREP recipe

S2e PREP (#18788) proposed using `simp only [adjMapHyper, hadj_eq, hadj_back]`
to reduce the match — mirroring the parent. **This failed** because:

1. `simp only` unfolds `adjMapHyper` to its `match` body (good), and
2. `simp only` rewrites `adj p.1 p.2` to `some ⟨s', k'⟩` via `hadj_eq` (good), but
3. **`simp only` does NOT reduce `match some ⟨s', k'⟩ with | some sk => sk | none => p` to `⟨s', k'⟩`**.

The parent's `simp only [adjMap, hadj_eq, hadj_back]` works because
its match destructures into `(s', k')` (a Prod), and `Prod` has built-in
`Prod.mk.eta` definitional equality. The hypergraph's Σ-form does not
have a `Sigma.mk.eta` reduction at the same definitional level.

**Workaround**: Encapsulate the reduction in a local lemma `hMap`:
```lean
have hMap : ∀ q sk, adj q.1 q.2 = some sk → adjMapHyper adj q = sk := by
  intro q sk hq; unfold adjMapHyper; rw [hq]
```

`unfold` (unlike `simp only`) directly reduces the match because it
operates at the kernel level. Then `rw [hMap …]` lifts the reduction
into the main proof, where it composes cleanly with the rest.

The fixed-point-free step also differs from S2e PREP Option C: after
`rw [h1]`, the goal becomes `⟨s', k'⟩ ≠ p` (Sigma form), so the closing
chain `(Sigma.eta p).trans heq.symm` works directly. **The involution
step's `Sigma.eta` is consumed by Lean's structure-eta machinery as
rfl** (see "structure-eta closes ⟨p.1, p.2⟩ = p as rfl" comment in the
proof). The fpf step's `Sigma.eta` remains explicit because the goal
shape there is `⟨s', k'⟩ ≠ p`, not the eta-reducible
`⟨p.1, p.2⟩ ≠ p`.

## 3. Build verification

Docker build of `Proofs.SpernerMathlibHyper`:

```
⚠ [7744/7744] Built Proofs.SpernerMathlibHyper (26s)
warning: Proofs/SpernerMathlibHyper.lean:129:8: declaration uses 'sorry'
warning: Proofs/SpernerMathlibHyper.lean:327:8: declaration uses 'sorry'
Build completed successfully (7744 jobs).
=== Build succeeded ===
```

Two `sorry` warnings remain (door_count_parity_hyper equality case and
sperner_parity_hyper chain). The `even_card_interior_doors_hyper` sorry
is closed.

Pre-existing `unusedSectionVars` warnings on `adjHyper_some_of_ne_none`
(line 212) and `isDoorHyper_of_shared_face` (line 220) are **not new**
— they existed in the S3 ACT baseline. Out of scope for this PR; can
be cleaned up by adding `omit` clauses in a follow-up.

## 4. Bearers used (vs. S2e PREP audit)

| Bearer | Source | Use | PREP-predicted? |
|--------|--------|-----|-----------------|
| `Sperner.even_card_fpf_invol` | `SpernerMathlib.lean:59` | main bearer | ✓ |
| `adjMapHyper` (local) | this file | involution definition | ✓ |
| `adjHyper_some_of_ne_none` (local) | this file | extracts adjacent Σ-pair | ✓ |
| `isDoorHyper_iff_of_adj` (local) | this file | door transfer iff | ✓ |
| `hadj_symm` / `hadj_vertex` / `hadj_ne` | hypotheses | side-conditions | ✓ |
| `Sigma.eta` | Mathlib `Sigma.Basic` | fpf step closing | ✓ |
| `Option.noConfusion` | Lean core | `some ≠ none` for set-stability | ✓ |
| structure-eta (Lean kernel) | n/a | closes involution rfl | **NEW** (S2e PREP did not anticipate this) |
| `unfold` (vs. `simp only`) | Lean tactic | match reduction | **NEW** workaround |

Two unanticipated bearers / techniques relative to S2e PREP:

* **Structure-eta as rfl** for `⟨p.1, p.2⟩ = p` — closes the involution
  step automatically after the two `rw`s.
* **`unfold` over `simp only`** for match reduction — `simp only`
  doesn't reduce the match even with the substituting hypothesis in
  scope; `unfold` does.

Both quirks are Lean-elaboration artifacts, not mathematical
adjustments. The PREP recipe's mathematical structure (apply
`even_card_fpf_invol` with three local side-conditions) is correct.

## 5. Race awareness

* `sperner-mathlib-oq-01` has zero open PRs targeting
  `SpernerMathlibHyper.lean` at S4 ACT push time (verified
  2026-06-04 via `gh pr list --search "sperner-mathlib in:title"`).
* The S3 ACT branch (commit `43ed761126b` on a different branch) is
  unrelated — it lives on a research/sperner-oq05 branch and predates
  this S4 ACT branch.
* Sibling slug PRs (sperner-simplicial-bridge, sperner-ndim-mathlib)
  do not touch `SpernerMathlibHyper.lean`.

## 6. Next sessions (recommended)

* **S5 ACT — `door_count_parity_hyper` equality case** (line 189). The
  cardinality dichotomy from S2c PREP and the bearer chains from S2d
  PREP are paste-ready. Effort: 30–60 min.
* **S6 ACT — `sperner_parity_hyper` chain** (line 351). Mirrors the
  parent's `sperner_parity` finite-sum closure. Effort: 60–90 min.

Closing both reduces this file to **0 sorries** and unlocks `exists_panchromatic_hyper`
as a fully-verified hypergraph Sperner theorem.

## 7. Verification log

```
$ wc -l proofs/Proofs/SpernerMathlibHyper.lean
     382 proofs/Proofs/SpernerMathlibHyper.lean

$ grep -n "^[^-]*sorry\b\|^[[:space:]]*sorry\b" proofs/Proofs/SpernerMathlibHyper.lean
189:    sorry
351:  sorry

$ ./proofs/scripts/docker-build.sh Proofs.SpernerMathlibHyper
… (truncated)
⚠ [7744/7744] Built Proofs.SpernerMathlibHyper (26s)
Build completed successfully (7744 jobs).
=== Build succeeded ===
```
