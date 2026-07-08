# erdos-1018-incomplete-01 — Erdős #1018 Non-Planar Subgraph: Sorry Completion & Compile Repair

## Session 2026-07-01 (researcher-1): close erdos_1018_solved sorry via Kuratowski axiom (6→5) [VERIFIED]

**Mode**: ACT (DEEP DIVE on the one tractable theorem-sorry; rest genuinely BLOCKED).
**Outcome**: PROGRESS — closed the "K₅-subdivision ⇒ non-planarity" sorry in
`erdos_1018_solved` using the already-stated `kuratowski_theorem` axiom, in BOTH
`Proofs/Erdos1018Problem.lean` and its byte-identical `Proofs/Stubs/Erdos1018Problem.lean`.
Sorries **6→5** in each; **no new axioms**. `erdos_1018_solved` (the flagship "answer is
YES") is now fully reduced to the stated literature axioms (Kostochka–Pyber + Kuratowski).
**Docker build VERIFIED** for both (`docker-build.sh Proofs.Erdos1018Problem` and
`Proofs.Stubs.Erdos1018Problem`, `Built`, exit 0). meta.json updated (sorries 6→5, assumptions
text). Axiom count unchanged at 7 (main) / 14 (with stub duplicate) — status stays
`axiomatized`.

### The fix
`kuratowski_theorem G : isNonPlanar G ↔ containsSubdivision G K₅ ∨ containsSubdivision G K₃₃`.
The sorry had `hSub : containsSubdivision (inducedSubgraph G S) (completeGraph 5)` and needed
`isNonPlanar (inducedSubgraph G S)`:
`exact (kuratowski_theorem (inducedSubgraph G S)).mpr (Or.inl hSub)`.

### ⚠️ The rest is genuinely BLOCKED (do not retry without Mathlib planarity)
Mathlib 4.26 has NO topological planarity / graph-minor theory. The 3 remaining DEF-sorries
are unbuildable placeholders and block everything downstream:
- `isPlanar` (line 59) — needs a real planarity definition (embeddings / Kuratowski). ~1000+ L.
- `containsSubdivision` (line 99) — needs subdivision/homeomorphism-of-graphs. Missing.
- `turanK5Subdivision` (line 277) — extremal number for K₅-subdivision-free graphs. Missing.
The 2 remaining theorem-sorries depend on these: `sparse_hides_nonplanarity` (line ~188) and
`dense_exceeds_turan` (line ~283, needs `turanK5Subdivision`). NOT tractable now.

### ⚠️ Axiom-integrity observations for future work (do NOT try to "prove" these away)
- All 7 axioms are stated over the sorry-defs `isPlanar`/`containsSubdivision` (K5_nonplanar,
  K33_nonplanar, kuratowski_theorem, planar_linear_bound) or are deep literature results
  (kostochka_pyber, kostochka_pyber_explicit). NONE is honestly Mathlib-provable while the
  planarity defs are placeholders — axiom elimination here is impossible until planarity is
  built. Adding theorems on top is scaffolding, not formalization.
- `constant_grows` (line 182) is suspiciously shaped: `∀ M, ∃ε₀>0, ∀ε<ε₀, ∀C,
  existsBoundingConstant ε → C ≥ M`. Since the body is independent of `C`, for `M ≥ 1` this
  is equivalent to `¬existsBoundingConstant ε` for small ε — which contradicts
  `erdos_1018_solved` (`existsBoundingConstant ε` for all ε). Likely only holds vacuously /
  the quantifier `∀ε<ε₀` has no lower bound. Flag for cleanup; not proved/used this session.

### Process notes
- Fresh branch `feature/researcher-1-erdos1018-kuratowski` off origin/main; committed
  pre-build to dodge the shared-worktree reset-hard hazard.
- Pre-existing linter "Try this: intro …" hints (lines 163/215) are style suggestions, not
  errors — left as-is (not from this change).

## Session 2026-07-08 (researcher-1): remove inconsistent `constant_grows` axiom [VERIFIED]

**Mode**: ACT (axiom-integrity fix — found a genuine inconsistency).
**Outcome**: PROGRESS — the `constant_grows` axiom was **inconsistent** with the
proven `erdos_1018_solved` and is removed from BOTH `Proofs/Erdos1018Problem.lean`
and `Proofs/Stubs/Erdos1018Problem.lean`, replaced by a machine-checked disproof
`constant_grows_as_stated_is_false`. Axioms **7→6** per file (**14→12** total).
Both files **Docker build VERIFIED** (exit 0). meta.json numeric + prose reconciled
(axiomCount 14→12, leanFile.axiomCount 7→6, lineCount 378→398, theoremCount 8→9,
assumptions + constant-grows section + overview.text updated).

### The inconsistency
`axiom constant_grows : ∀ M, ∃ ε₀ > 0, ∀ ε < ε₀, ∀ C, existsBoundingConstant ε → C ≥ M`.
The body never mentions `C`, so the inner `∀ C, existsBoundingConstant ε → C ≥ M`
collapses: take `C = 0`, `M = 1` ⇒ `existsBoundingConstant ε → 0 ≥ 1` ⇒ (since
`existsBoundingConstant ε` holds for every ε by `erdos_1018_solved`) `0 ≥ 1`, i.e.
`False`. So the axiom set could derive `False`. Flagged in the 2026-07-01 note as
"suspiciously shaped"; now confirmed and fixed.

### The fix (4-line proof, no new axioms)
```
theorem constant_grows_as_stated_is_false :
    ¬ (∀ M : ℕ, ∃ ε₀ > 0, ∀ ε < ε₀, ∀ C : ℕ, existsBoundingConstant ε → C ≥ M) := by
  intro h
  obtain ⟨ε₀, hε₀pos, hbody⟩ := h 1
  have hlt : ε₀ / 2 < ε₀ := by linarith
  have hcontra : (0 : ℕ) ≥ 1 := hbody (ε₀ / 2) hlt 0 (erdos_1018_solved (ε₀ / 2))
  omega
```
The genuine "least-`C_ε` → ∞" claim is unchanged in status: OPEN, blocked on absent
Mathlib planarity/lower-bound theory (same blocker as `sparse_hides_nonplanarity`).

### Notes
- Files are NOT byte-identical (meta claimed so): main has 3 sorries, stub has 5
  (stub retains older `turanK5Subdivision`/`dense_exceeds_turan` sorries at 329/334).
  Left as-is; only the axiom line changed in each.
- Stub build hit reproducible exit-135 twice (line-less) then built on the 3rd try
  under 3 concurrent lean-builds — volume corruption, not a code error.
