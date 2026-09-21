# Erdős 85 / issue 43623 restart handoff

## Repository state

- Active worktree: `/Volumes/Stripe/lean-genius/issue-43623`
- Branch: `feature/issue-43623`
- PR: <https://github.com/rjwalters/lean-genius/pull/43624>
- Last pushed commit: `4d8e8404cd`
- Do not stage `.loom-managed` or `node_modules`.
- At shutdown, macOS allowed the drive to remain mounted but denied this Codex
  process access to the worktree with `Operation not permitted`.

The complete build snapshot is preserved at:

```text
/private/tmp/erdos85-43623.JkLB30
```

This is not a Git repository. It contains the pinned Lean 4.31 source/build
tree used for verification.

## New source files in the worktree

```text
proofs/Proofs/Erdos85PolarityDeletion.lean
proofs/Proofs/Erdos85PolarityAbsolute.lean
proofs/Proofs/Erdos85DeletePair.lean
proofs/Proofs/Erdos85OneDefectCore.lean
```

`proofs/Proofs/Erdos85Results.lean` has imports and publication-facing prose
for these modules.

## Mathematical results

1. Chevalley--Warning produces a nonzero isotropic vector for
   `X₀² + X₁² + X₂²` over every finite field.
2. Hence every finite-field orthogonal polarity has an absolute point.
3. Deleting that point proves the unconditional consecutive exact family

   ```text
   f(q² + q) = f(q² + q + 1) = q + 1.
   ```

4. Delete-one/add-an-adjacent-pair surgery produces an order `+1` witness.
   Its repair hypothesis was strengthened at the end: only neighbors of the
   deleted vertex whose degree is exactly `d` need coverage by the selectors.
5. `OneDefectCore n d` is exactly equivalent to a witness at order `n+1` and
   degree `d`.
6. A new top-level reduction was added:

   ```text
   minDegreeForC4 n ≤ minDegreeForC4 (n + 1)
     ↔ OneDefectCore n (minDegreeForC4 n - 1)       (4 ≤ n).
   ```

This is substantial partial progress, not a complete solution of Erdős 85.

## Verification status

The following compiled with pinned Lean 4.31 before the final edits:

- `Erdos85PolarityDeletion.lean`
- `Erdos85PolarityAbsolute.lean`
- `Erdos85DeletePair.lean`

`Erdos85DeletePair.lean` was then strengthened to cover only tight neighbors
and compiled successfully again.

`Erdos85OneDefectCore.lean` exposed dependent typeclass issues during the
strong `-o` build. The latest repair exists only in the snapshot copy:

```text
/private/tmp/erdos85-43623.JkLB30/Proofs/Erdos85OneDefectCore.lean
```

The worktree copy is one patch behind and still contains the failing
`eSplit.degree_eq` implementation. The snapshot replaces that degree transport
with a direct equality of neighbor finsets. Docker became unresponsive before
this final snapshot edit could be conclusively compiled.

## Resume procedure

1. Confirm the external worktree is accessible:

   ```bash
   ls /Volumes/Stripe/lean-genius/issue-43623
   ```

2. Diff, then copy only the final core repair from the snapshot into the
   worktree. Preserve the other worktree files, which are newer or equal:

   ```bash
   diff -u \
     /Volumes/Stripe/lean-genius/issue-43623/proofs/Proofs/Erdos85OneDefectCore.lean \
     /private/tmp/erdos85-43623.JkLB30/Proofs/Erdos85OneDefectCore.lean
   ```

3. Compile `Erdos85OneDefectCore.lean` with pinned Lean 4.31. If the direct
   neighbor-finset proof fails, repair only `hdegree`; all surrounding
   mathematics and the new top-level theorem are already in place.
4. Recompile, in order:

   ```text
   Erdos85DeletePair.lean
   Erdos85PolarityDeletion.lean
   Erdos85PolarityAbsolute.lean
   Erdos85OneDefectCore.lean
   Erdos85Results.lean
   ```

5. Run `git diff --check` and an axiom audit for:

   ```text
   Erdos85.Polarity.minDegreeForC4_projectivePlane_pred
   Erdos85.c4FreeMinDegreeWitness_delete_add_pair
   Erdos85.c4FreeMinDegreeWitness_succ_iff_oneDefectCore
   Erdos85.minDegreeForC4_le_succ_iff_top_oneDefectCore
   ```

6. Stage only the four new proof modules and `Erdos85Results.lean`. Suggested
   commit title:

   ```text
   proofs: add consecutive polarity values and +1 surgery
   ```

   Commit body: `Part of #43623`.
7. Push and update PR 43624, explicitly stating that eventual monotonicity
   remains open.

## Parallel-agent findings worth pursuing later

- An intrinsic core characterization should say that a `C₄`-free core has
  minimum degree at least `d-1`, and its degree-`d-1` deficient vertices lie in
  a common-neighbor-independent selector of size at least `d`.
- Every triangle-free cubic `C₄`-free graph has a canonical delete/add-pair
  extension. Computation succeeded on 3,200 random samples and standard named
  examples. In the general cubic case, triangles are vertex-disjoint; the
  remaining obstruction consists of disjoint triangles joined by a perfect
  matching.
- Do not claim the naive “exactly one common neighbor” property for all pairs
  in loopless orthogonal polarity graphs; absolute endpoints require separate
  treatment.
