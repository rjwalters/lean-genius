# Knowledge Base: erdos-816-oq-01

OQ: remove/lower the `n ≥ 600` restriction in Chen–Ma's stronger result (every
graph on `2n+1` vertices with `≥ n²+n` edges, other than `K_{n,n+1}`, has an
equal-degree pair joined by a path of length 3).

---

## Session 1 (researcher-1, 2026-06-14) — OBSERVE → ORIENT, exhaustive small-n verification

Both build backends down (Docker daemon down; Aristotle MCP `prove` → "Resource
not found"), so this is a **build-free, Python-verified** ORIENT. Artifact:
`scripts/verify_threshold.py` (host `python3`, no deps).

### The degeneracy boundary: the restriction CANNOT reach n = 1

A path of length 3 needs **4 distinct vertices**. For `n = 1`, `2n+1 = 3 < 4`, so
**no** 3-vertex graph has an equal-degree P3 pair at all. The triangle `K_3` has
`3 ≥ n²+n = 2` edges and is **not** `K_{1,2}`, so it is a genuine non-`K_{n,n+1}`
counterexample. Hence the stronger result is **false at n = 1** for trivial reasons;
the smallest possible threshold is `n ≥ 2`. (Rigorous, no computation.)

### Exhaustive brute force confirms the result at n = 2 and n = 3

For each `n`, enumerate **every** graph on `2n+1` vertices with `≥ n²+n` edges,
test the property (early-exit on the first equal-degree pair admitting a P3), and
classify the graphs that LACK it as either `K_{n,n+1}` or a genuine counterexample.

| n | vertices | min edges | graphs enumerated | K_{n,n+1} fails (= C(2n+1, n)) | OTHER counterexamples |
|---|----------|-----------|-------------------|--------------------------------|-----------------------|
| 2 | 5 | 6 | 386 (exhaustive) | 10 = C(5,2) | **0** |
| 3 | 7 | 12 | 695 860 (exhaustive) | 35 = C(7,3) | **0** |

So at `n = 2` and `n = 3` the stronger result is **TRUE** and `K_{n,n+1}` is the
**unique** exception (up to isomorphism). The labelled-copy counts `C(2n+1, n)`
match exactly the number of ways to choose the size-`n` part, confirming the
`K_{n,n+1}` detector.

### Inference on the true threshold

`n = 2, 3` hold cleanly and `n = 1` fails only for the degenerate
"not enough vertices for a P3" reason. This is strong evidence that the **true
threshold is `n ≥ 2`** and that Chen–Ma's `n ≥ 600` is an artifact of their
proof method (stability/counting arguments that only become valid for large `n`),
not the actual boundary. No sporadic small-`n` exception beyond `K_{n,n+1}` was
found.

### Feasibility limit

`n = 4` needs graphs on `9` vertices with `≥ 20` edges: `Σ_{k≥20} C(36,k)` is in
the billions — infeasible by naïve labelled enumeration. Extending the empirical
check past `n = 3` requires isomorph-rejection (e.g. `nauty`) or a structural
small-case argument. Not attempted this session.

---

## Lean / formalization gap

- `Erdos816Problem.lean` only axiomatizes the `n²+n+1` form (`erdos_816_full`).
  The stronger `≥ n²+n` form is a *predicate* (`satisfiesWeakerEH816`), unstated as
  a theorem.
- A formal resolution would prove, for the smallest provable `n₀`,
  `∀ n ≥ n₀, satisfiesWeakerEH816 G n ∧ ¬isCompleteBipartite G n → hasEqualDegreePath3Pair G`.
  The `n = 2, 3` base cases are now machine-checked here (decidable, finite); the
  hard content is the general `n` argument (Chen–Ma), which is well beyond a single
  Lean session and is `axiomatized` in the gallery.

## Dead ends / cautions

- Naïve labelled enumeration stops being feasible at `n = 4`.
- The `n = 1` failure is **not** a counterexample to Erdős #816 itself (which uses
  `n²+n+1` edges and answer YES for all `n`); it only bounds how far the *stronger*
  `≥ n²+n` statement can be pushed downward.
