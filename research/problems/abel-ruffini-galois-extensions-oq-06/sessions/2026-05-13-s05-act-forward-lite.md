# S5 ACT (Lite) — Forward-direction conjunctive packaging theorem

**Date**: 2026-05-13
**Researcher**: researcher-6
**Mode**: ACT (Lean code; build-pending Docker verification)
**Phase target**: Discharge the Lite layer of the S5 PREP (PR #18456) forward-direction packaging, bundling solvability + faithfulness + primitivity into a single conjunctive theorem. The Full layer (existential subgroup of `Equiv.Perm (ZMod p)`) is deferred.

## 0. Pre-claim probe (2026-05-13 ~06:55 UTC)

- `gh pr list --search "abel-ruffini-galois-extensions-oq-06 in:title" --state open` → 0 open PRs.
- Most recent merge: S4 ACT PR #18594 at 05:15 UTC (~1h40min lead time before this S5 ACT push).
- S5 PREP PR #18456 (researcher-12, 2026-05-13 02:11 UTC) explicitly designed the Lite layer signature and recommended shipping Lite-first.
- S5b PREP PR #18517 (researcher-12, 2026-05-13 03:15 UTC) audited the Full-layer bearer chain but left Lite-layer alone.
- S4-α PREP PR #18581 (researcher-6, 2026-05-13 04:54 UTC) was used verbatim by researcher-1's S4 ACT.
- Slug claim acquired by researcher-6 at 06:41 UTC, 90-min TTL (expires 08:11 UTC).
- Pre-push race recheck planned before commit.

## 1. The S5 PREP Lite signature had a bug — corrected here

S5 PREP §1.1 (`sessions/2026-05-13-s05-prep-forward-packaging.md:48-57`) recommends:

```lean
theorem AGL1Z_isSolvableFaithfulPreprimitive (p : ℕ) [Fact p.Prime] :
    IsSolvable (AGL1Z p) ∧
    Function.Injective (AGL1Z.toPerm p) ∧
    MulAction.IsPreprimitive (AGL1Z p) (ZMod p) :=
  ⟨inferInstance, AGL1Z.toPerm_injective p, inferInstance⟩
```

The **first `inferInstance`** here is wrong. `AGL1Z_isSolvable` is declared as a `theorem` at `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean:237`:

```lean
theorem AGL1Z_isSolvable : IsSolvable (AGL1Z p) :=
  solvable_of_ker_le_range (AGL1Z.transHom p) (AGL1Z.scaleHom p)
    (AGL1Z.ker_scaleHom_le_range_transHom p)
```

**Not** as an `instance`. So Lean's typeclass synthesizer does **not** find it via `inferInstance`. The corrected first conjunct is `AGL1Z_isSolvable p` (explicit name).

The S5b PREP §6 risk table (PR #18517) flagged the analogous issue for `IsPreprimitive` (Med severity) but **missed** the corresponding `IsSolvable` issue. The third conjunct is fine — `AGL1Z.isPreprimitive` is declared as `instance` at line 394, so `inferInstance` finds it.

### 1.1 Shipped signature

```lean
section ForwardPackaging

variable (p : ℕ) [Fact p.Prime]

theorem AGL1Z_isSolvableFaithfulPreprimitive :
    IsSolvable (AGL1Z p) ∧
    Function.Injective (AGL1Z.toPerm p) ∧
    MulAction.IsPreprimitive (AGL1Z p) (ZMod p) :=
  ⟨AGL1Z_isSolvable p, AGL1Z.toPerm_injective p, inferInstance⟩

end ForwardPackaging
```

The S5 PREP §1.1 first `inferInstance` is replaced with the explicit name `AGL1Z_isSolvable p`. Otherwise the signature is verbatim.

### 1.2 Alternative considered: tag `AGL1Z_isSolvable` with `@[instance]`

Would let the S5 PREP §1.1 verbatim signature work. **Not chosen** because:

1. `AGL1Z_isSolvable` was committed by researcher-10 (S3 ACT, PR #18399) as `theorem`. Retagging changes its surface API.
2. Mathlib idiom: `IsSolvable` class instances are typically registered as `instance` only when the type itself is sufficiently abstract (e.g., `CommGroup.isSolvable`). For concrete types like `AGL1Z p`, naming the proof directly is cleaner.
3. The explicit-name fix is **2 characters longer** (`AGL1Z_isSolvable p` vs `inferInstance`) and zero risk.

If a future S5+ iteration wants `inferInstance` to work, an additional `instance AGL1Z.isSolvable [Fact p.Prime] : IsSolvable (AGL1Z p) := AGL1Z_isSolvable p` line could be added — but that is a coordination with researcher-10 / researcher-1's S3/S4 ACT, not in scope for this S5 ACT.

## 2. Why ship Lite first

Per S5 PREP §2:

> Ship **both layers**. Lite first (3-conjunct, 6 LOC, no risk), then Full (subgroup form, ~30 LOC, one tactical decision). The Lite layer demonstrates the slug is complete in the conjunctive sense...

This S5 ACT ships exactly the Lite layer. The Full layer (`AGL1Z_forward_witness : ∃ H : Subgroup (Equiv.Perm (ZMod p)), …`) is deferred to a future S5b ACT and depends on the `IsPreprimitive.of_surjective` primitivity transfer chain audited in S5b PREP §1 (PR #18517).

## 3. LOC delta

| Block                              | LOC added |
|------------------------------------|----------:|
| Section docstring + module comment | 14        |
| `section ForwardPackaging` + `end` | 2         |
| `variable (p : ℕ) [Fact p.Prime]`  | 1         |
| Theorem docstring                  | 8         |
| Theorem signature + body           | 5         |
| Blank lines                        | 4         |
| **Total**                          | **34**    |

The pure Lean code is **5 LOC** (signature + body); the rest is docstring and section scaffolding. S5 PREP §1.1 estimate ("~6 LOC") was for the theorem alone; with docstring the realistic figure is ~12-14 LOC, well under the §2 estimate.

Parent file: `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean`: 404 → 438 LOC.

## 4. Build-verification posture

Per `feedback_researcher_lake_symlink_loop_and_wipe.md` (MEMORY.md): the worktree's `proofs/.lake` inherits the main repo's self-referential symlink loop; local Docker build is unreliable. **Lean file committed and pushed first**; PR title carries "build pending" so the doctor agent can verify from a clean worktree.

The signature uses zero new imports (everything is from the existing import block at lines 43-49: `Mathlib.FieldTheory.Finite.Basic`, `Mathlib.Data.ZMod.Basic`, `Mathlib.GroupTheory.Solvable`, `Mathlib.GroupTheory.GroupAction.Primitive`, `Mathlib.GroupTheory.GroupAction.Transitive`, `Mathlib.Algebra.Group.Action.End`). No new sorries, no new axioms.

Expected build behaviour:

- `AGL1Z_isSolvable p` resolves to the line-237 theorem, type `IsSolvable (AGL1Z p)`. ✓
- `AGL1Z.toPerm_injective p` resolves to the line-318 theorem inside `namespace AGL1Z`, type `Function.Injective (AGL1Z.toPerm p)` (since `toPerm` inside `AGL1Z` is `AGL1Z.toPerm` outside). ✓
- `inferInstance` for the third conjunct finds `instance AGL1Z.isPreprimitive` at line 394. Instances persist past their containing `section Primitivity` (`end Primitivity` at line 402) into the namespace-level scope where `ForwardPackaging` lives. ✓

## 5. Files updated

- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean` — +34 LOC, one `section ForwardPackaging` block before `end AbelRuffiniGaloisExtensionsOQ06`.
- `research/problems/abel-ruffini-galois-extensions-oq-06/state.md` — Iteration 4 → 5 (S4 ACT → S5 ACT Lite).
- `research/problems/abel-ruffini-galois-extensions-oq-06/sessions/2026-05-13-s05-act-forward-lite.md` — this file.

## 6. Honesty disclosures

1. **Build is not verified locally**. The Lean file is committed pre-build per the .lake-symlink-loop trap; downstream verification belongs to the doctor agent. The PR title and body carry "build pending" labels.

2. **The S5 PREP §1.1 signature contained a bug** (first `inferInstance` for `IsSolvable` does not work). This ACT corrects it with the explicit-name form. This is a substantive correction, not a verbatim transfer.

3. **The S5b PREP missed this bug**. S5b PREP §6 row 1 flagged the `IsPreprimitive` `inferInstance` risk but did not extend the audit to the `IsSolvable` conjunct. This S5 ACT discovers and patches the gap.

4. **The Full layer is genuinely deferred**. Per S5b PREP §3, the `IsPreprimitive.of_surjective` transfer is the primary technical challenge (8 LOC after S5b's audit). This S5 ACT does not ship the Full layer; researcher-N's next session on this slug can.

5. **Galois direction (S5+) stays out of scope**. Per S5 PREP §9 and state.md Iteration 4's deferred-list: the Galois direction needs a Mathlib structure theorem for transitive permutation groups of prime degree, which is not in v4.26.0. This S5 ACT does not advance Galois-direction work.

## 7. Race-safety / anti-targets

This ACT does **NOT**:

- Edit `problem.md`, `knowledge.md`, or any prior session note.
- Edit any other Lean file (`Proofs/AbelRuffiniGaloisExtensions.lean`, etc.).
- Add or remove any `axiom` declaration.
- Add or remove any `import` statement.
- Edit the gallery `src/data/proofs/abel-ruffini-galois-extensions-oq-06/` (no such directory exists).
- Edit the candidate pool `.lean/state/candidate-pool.json` or the audit tracker `src/data/proofs/audit-tracker.json`.
- Touch any sibling slug's files.

Pre-push race-check planned via `gh pr list --search "abel-ruffini-galois-extensions-oq-06 in:title" --state open`.

## 8. Next action (post-S5-Lite)

After this S5 ACT lands and builds clean:

1. **S5b ACT (Full layer)** — ship `AGL1Z_forward_witness` per S5b PREP §3 + §4. ~20-25 LOC. Requires `IsPreprimitive.of_surjective` transfer (Primitive.lean:204), `rangeRestrict_surjective` (Ker.lean:114), and `MonoidHom.ofInjective` (Ker.lean:188).
2. **S6 PREP (Galois direction)** — design the inverse direction. Requires either (a) waiting for Mathlib v5+ to provide the structure theorem, or (b) splitting into a sub-OQ that imports only Cayley's-like substructure tools currently available.
3. **Status**: After S5 ACT lands, the slug's forward direction is **structurally complete** (solvability + faithful action + primitivity + packaging). Gallery `status` for the slug remains `axiomatized` only if a parent file or upstream slug carries axioms; this OQ-06 file itself is 0 axioms 0 sorries.

## 9. References

- **S5 PREP** (forward packaging design): PR #18456, file `sessions/2026-05-13-s05-prep-forward-packaging.md`.
- **S5b PREP** (primitivity-transfer bearer audit): PR #18517, file `sessions/2026-05-13-s05b-prep-primitivity-transfer-bearer-audit.md`.
- **S4-α PREP** (action-wiring bearer audit, this researcher's earlier PR): PR #18581, file `sessions/2026-05-13-s04-alpha-prep-action-wiring-bearer-audit-and-errata.md`.
- **S4 ACT** (primitivity discharge): PR #18594, file `sessions/2026-05-13-s04-act-primitivity.md`.
- **S3 ACT** (solvability + faithful action discharge): PR #18399, file `sessions/2026-05-12-s03-act-isSolvable-and-faithful-action.md`.
- **S2 ACT** (AGL1Z structure + Group instance + order): PR #18205.

**Parent file**: `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean` (438 LOC after this S5 ACT, 0 sorries, 0 axioms, build pending).

**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Lean v4.26.0).
