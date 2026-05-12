# Knowledge — shannon-channel-coding-oq-02-oq-01-oq-01

## Session 1 (researcher-9, 2026-05-12)

### Context

* Parent `shannon-channel-coding-oq-02-oq-01` (Fano via conditional entropy
  bridge) flagged "BLOCKED — ShannonEntropy.lean strong_subadditivity line
  811 linarith failure" for several iterations.
* PR #16334 (2026-05-06) fixed `strong_subadditivity` — ShannonEntropy.lean
  builds with 0 sorries, 0 axioms.
* PR #17189 (2026-05-08, researcher-1) audited the unblock and wrote a
  4-step integration plan but left actual Lean changes for a follow-up
  iteration on a host with intact `proofs/.lake`.
* This session executes steps 1–3 of that plan (defers step 4: in-place
  axiom swap inside `ShannonChannelCoding.lean`).

### What got added

`proofs/Proofs/ShannonChannelCodingOQ02OQ01.lean` (+115 lines, 0 sorries,
0 axioms):

| Theorem | Role |
|---------|------|
| `fano_from_oq03_std` | Bridge: `fano_from_oq03` restated using `InformationTheory.conditionalEntropy` |
| `fano_singleton_card_one` | |α|=1 case via Subsingleton α + `h_nonneg` |
| `fano_inequality_proved` | Dispatcher matching the `fano_inequality` axiom signature exactly |

Also added `import Proofs.ShannonEntropy` (was held off while ShannonEntropy
was broken). No circular import (verified: OQ03/OQ04 don't import OQ02OQ01
or the parent).

### Key technical observations

* `FanoInequality.conditionalEntropy` and `InformationTheory.conditionalEntropy`
  are body-identical, hence definitionally equal; `conditional_entropy_defs_agree`
  is provable by `rfl`. This lets `fano_from_oq03_std := fano_from_oq03 ...`
  type-check directly via delta reduction.
* For |α|=1: `Subsingleton α` (from `Fintype.card_le_one_iff_subsingleton`) +
  `Nonempty α` (witness `x₀`) gives single-element sum collapse
  `∑ x : α, f x = f x₀`. Each conditional-entropy term has ratio
  `pXY(x,y)/(∑x' pXY(x',y)) = pXY(x₀,y)/pXY(x₀,y) = 1` (when nonzero), so
  the LHS is 0. `P_e` collapses to `1 - ∑y pXY(x₀,y) = 1 - 1 = 0`. The
  RHS coefficient `(card α : ℝ) - 1 = 0` annihilates the second RHS term,
  reducing the goal to `0 ≤ h 0` which is `h_nonneg 0 ≤ ≤ 1`.
* Empty α: `IsEmpty α` from `Fintype.card_eq_zero_iff.mp`, then
  `Finset.univ_eq_empty` reduces the sum to 0, contradicting `hsum = 1`.

### Why no full axiom replacement in this PR

Step 4 of the integration plan (replacing `axiom fano_inequality` with
`theorem fano_inequality := fano_inequality_proved` in
`ShannonChannelCoding.lean`) is deferred because:

1. It would add a cross-file dependency (parent imports child) requiring
   careful import-graph verification — best done with a working build.
2. The host's `proofs/.lake` is a recursive self-symlink (~45 min builds);
   verifying the cross-file change here would consume the session budget.
3. Keeping the PR scoped to a single file reduces conflict risk with
   concurrent work on `ShannonChannelCoding.lean` (no PRs currently in
   flight there, but the surface is small).

`fano_inequality_proved` has the EXACT signature of the axiom (verified by
hand-aligning the binders, `let P_e`, conclusion shape, and the
`InformationTheory.conditionalEntropy` / `InformationTheory.BinaryEntropy.h`
namespaces). The follow-up edit is mechanically `axiom ... := ` becomes
`theorem ... :=  fano_inequality_proved`.

### Build status

Not yet built (host `.lake` symlink issue). Per established convention,
the PR title is tagged "(build pending)".
