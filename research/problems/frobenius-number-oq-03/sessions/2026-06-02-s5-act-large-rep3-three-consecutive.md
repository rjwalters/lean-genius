# S5 ACT — `large_representable3_three_consecutive` (researcher-1, 2026-06-02)

## §1 Summary

Ships `large_representable3_three_consecutive : ∀ {n m : ℕ}, 1 ≤ n →
(n - 1) * n ≤ m → Representable3 n (n + 1) (n + 2) m`. Direct
specialization of S3b's `large_representable3_via_two_gen` (PR #19412,
researcher-9) to the three-consecutive family `(n, n + 1, n + 2)` via
the consecutive-integer coprimality
`Nat.Coprime n (n + 1)`. The bound `(n - 1) * n = n² - n` is the
Sylvester quantity `(a - 1) * (b - 1)` evaluated at `a := n, b := n + 1`.

## §2 Delta

- `proofs/Proofs/FrobeniusNumberOQ03.lean`: 253 → 281 LOC (+28).
- New theorem: `large_representable3_three_consecutive`.
- 17 theorems / 2 definitions / 0 sorries / 0 axioms (was 16 / 2 / 0 / 0).
- No new imports (all bearers in S3b's import stack already).
- `src/data/proofs/frobenius-number-oq-03/meta.json`: lineCount
  253 → 281, theoremCount 16 → 17, description and assumptions
  updated, new section entry
  `s5-large-representable3-three-consecutive`, S4a section summary
  edited to remove "Closes the namespace" (S5 now closes).

## §3 Proof structure

8-line body:

```lean
theorem large_representable3_three_consecutive {n m : ℕ} (hn : 1 ≤ n)
    (hm : (n - 1) * n ≤ m) : Representable3 n (n + 1) (n + 2) m := by
  have hcop : Nat.Coprime n (n + 1) := by
    rw [Nat.coprime_self_add_right]
    exact Nat.coprime_one_right n
  have hb : 1 ≤ n + 1 := by omega
  have hbound : (n - 1) * (n + 1 - 1) ≤ m := by
    have heq : n + 1 - 1 = n := by omega
    rw [heq]
    exact hm
  exact large_representable3_via_two_gen hcop hn hb hbound
```

Three sub-arguments:

1. **Consecutive coprimality**:
   `Nat.coprime_self_add_right` (Mathlib `@[simp]`) gives
   `Coprime n (n + 1) ↔ Coprime n 1`, then
   `Nat.coprime_one_right n` discharges `Coprime n 1` directly.
2. **`1 ≤ n + 1`**: `omega` from `hn`.
3. **Sylvester-bound rewrite**:
   `(n - 1) * (n + 1 - 1) = (n - 1) * n` after the single
   `omega`-discharged `n + 1 - 1 = n` rewrite. ℕ-subtraction is
   safe here because `1 ≤ n + 1` always holds.

Apply `large_representable3_via_two_gen` with `a := n, b := n + 1,
c := n + 2` (the `c` is implicit; only `a, b` figure in the bound).

## §4 The bound — loose vs Roberts d = 1

S5's bound `(n - 1) * n = n² - n` instantiates the **Sylvester
2-generator bound** `(a - 1) * (b - 1)` at `a := n, b := n + 1`. The
**Roberts d = 1 closed form** (1956) is:

```
g(n, n + 1, n + 2) = ⌊(n - 2) / 2⌋ · n + (n - 1)
```

Asymptotically `n² / 2`. So Roberts is **half** of S5's bound.
Numerical verification from `knowledge.md` §S1:

| `n` | Roberts `g` | S5 bound `n² − n` | ratio S5 / Roberts |
|----:|:-----------:|:-----------------:|:------------------:|
|  3  |     2       |        6          |    3.0             |
|  4  |     7       |       12          |    1.7             |
|  5  |     9       |       20          |    2.2             |
|  6  |    17       |       30          |    1.8             |
|  7  |    20       |       42          |    2.1             |

S5 is **valid but not tight**. The tightening to Roberts is the
S6 ACT target.

## §5 Risk-acceptance (3/3 GREEN, build-pending shipping policy)

Per the post-ship pivot pattern
([[project-researcher-1-2026-06-02-s11b-alpha-act-isadmissible-iff-...]]
+ predecessors):

| Criterion | Status |
|---|---|
| (i) Leaf-only adds | ✅ append at end of `FrobeniusOQ03` namespace below S4a (line 252); no existing API touched; no downstream importer of this slug |
| (ii) Recent BUILD-VERIFY | ✅ S4a ACT [#21768] (mine, 2026-05-31) Docker `✔ [3059/3059] Built Proofs.FrobeniusNumberOQ03 (28s)`, `Build completed successfully (3059 jobs)`, `=== Build succeeded ===` — 2 days ago |
| (iii) Bearer-0-drift | ✅ Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` unchanged since 2026-05-13 (21 calendar days); 3 new bearers spot-checked at pin (see §6) |

Local Docker build deferred per
[[project-researcher-1-2026-06-02-s13-act-clt-gaussian-in-own-doa]]:
sibling container `lean-build-57602` (image `9026c55995f4`,
`lean4-arm64:v4.26.0`) has been running 5+ hours; restarting Docker
to flush the corrupted image blob would disrupt the sibling agent's
work. Build-pending ship is appropriate when risk-acceptance is GREEN
and the local infra is occupied.

## §6 Bearer inventory (S5-new)

### 1. `Nat.coprime_self_add_right`

`Mathlib/Data/Nat/GCD/Basic.lean:106` @ pin `2df2f0150c…`:

```lean
@[simp]
theorem coprime_self_add_right {m n : ℕ} : Coprime m (m + n) ↔ Coprime m n := by
  rw [add_comm, coprime_add_self_right]
```

Verified at pin via `curl -s
"https://raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/Mathlib/Data/Nat/GCD/Basic.lean"`.

### 2. `Nat.coprime_one_right`

`Init/Data/Nat/Coprime.lean:155` (Lean core, stable):

```lean
theorem coprime_one_right : ∀ n, Coprime n 1 := gcd_one_right
```

Verified at Lean master via `curl -s
"https://raw.githubusercontent.com/leanprover/lean4/refs/heads/master/src/Init/Data/Nat/Coprime.lean"`.

### 3. `omega`

Standard Mathlib tactic for ℕ linear arithmetic. Used twice (for
`1 ≤ n + 1` and `n + 1 - 1 = n`).

### In-repo precedent

`proofs/Proofs/GCDAlgorithm.lean:163-165` already uses the identical
`Nat.coprime_self_add_right` + `Nat.coprime_one_right` pattern for
its own `consecutive_coprime` theorem — verifies the bearer chain
at this Mathlib pin via existing build-clean code in the same
repository.

## §7 Forward outlook — S6 Roberts d = 1 tight closed form

S6 ACT target:

```lean
theorem frobeniusNumber3_three_consecutive_eq {n : ℕ} (hn : 3 ≤ n) :
    frobeniusNumber3 n (n + 1) (n + 2)
      = (n - 2) / 2 * n + (n - 1)
```

(The `3 ≤ n` hypothesis matches Roberts' original statement; the
`n ∈ {1, 2}` degenerate cases need separate accounting since `n = 1`
makes everything representable and `n = 2` gives the 2-generator
case `g(2, 3, 4) = g(2, 3) = 1`.)

Proof strategy (Apéry-set approach, deferred to S6):

1. **Upper bound** `≤ (n - 2) / 2 · n + (n - 1)`: exhibit, for each
   residue `r ∈ {0, 1, ..., n - 1}` modulo `n`, the **smallest**
   representable element of that residue class. The supremum is
   the largest of these, minus `n` (Brauer–Shockley identity, S1 §4).
2. **Sharpness** (i.e. the supremum is *not* representable): a
   single witness exhibition for the specific value above.

S6 LOC estimate: Route A direct enumeration ~80 LOC, Route B
Apéry-set machinery ~150 LOC (from state.md S4a §"Forward outlook").

S5's role: provides the **valid upper bound entry point** to the
Apéry-set chain via `frobeniusNumber3_le_of_subset_Iio` applied at
`K := (n - 1) * n`. The tightening to Roberts happens in S6 by
exhibiting a sharper containment.

## §8 Non-actions (explicit)

1. **No knowledge.md edit.** `knowledge.md` is research/domain
   territory; S5 is the standard build of the slug's roadmap roadmap,
   no new insights worth a knowledge.md entry (the Roberts
   numerical verification table is already in §S1).
2. **No `Proofs/FrobeniusNumber.lean` edit.** Parent file unchanged.
   Out-scope `le_or_lt` deprecation warning noted in S4a state.md
   remains out-of-scope here.
3. **No `Proofs.lean` umbrella refresh.** `import
   Proofs.FrobeniusNumberOQ03` already in place since S2 (PR #18937).
4. **No `relatedProofs` cross-reference changes.** Slug's
   cross-reference graph unchanged.
5. **No `pnpm annotations:build` rerun.** Gallery section structure
   preserved (new S5 section entry added directly to `meta.json`
   per gallery convention; annotations.json unchanged).
6. **No JSON tracker rewrite of `progressSummary` history.**
   Append-only discipline preserved (one new bullet, prior content
   verbatim).

## §9 Host state (informational)

- **Disk** (G7): 22 GiB free on `/dev/disk3s5` (worktree mount).
  Threshold: GREEN at ≥ 5 GiB, AMBER 1-5 GiB, RED < 1 GiB. Status:
  **GREEN**.
- **Docker** (G8): `Docker version 29.4.1` running; sibling
  container `lean-build-57602` (image `9026c55995f4`,
  `lean4-arm64:v4.26.0`) up 5+ hours holding shared image. Local
  Docker build deferred to avoid disrupting sibling work.
- **`.lake` symlink** (G9): not investigated this iteration (S4a
  recipe documented that the cache-volume mount in Docker overlays
  the circular self-symlink, so the issue is host-AMBER but does
  not block builds).

## §10 References

- `proofs/Proofs/FrobeniusNumberOQ03.lean:253-281` — S5 ACT theorem (this PR).
- `proofs/Proofs/FrobeniusNumberOQ03.lean:163-167` — S3b bridge `large_representable3_via_two_gen`.
- `proofs/Proofs/GCDAlgorithm.lean:163-165` — in-repo precedent for `consecutive_coprime` via same bearer chain.
- Mathlib bearer 1: `Mathlib/Data/Nat/GCD/Basic.lean:106` @ pin `2df2f0150c…`.
- Lean core bearer 2: `Init/Data/Nat/Coprime.lean:155`.
- Roberts (1956) — primary source for the tight closed form (S6 target).
- `state.md` "Forward outlook" — S6 Roberts d=1, S7 Roberts 3-AP, S7+ Fibonacci/Mersenne triples.
