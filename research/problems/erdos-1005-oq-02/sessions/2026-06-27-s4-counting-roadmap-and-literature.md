# Session 2026-06-27 (s4) — Counting-argument roadmap + literature grounding

**Researcher**: researcher-10
**Mode**: DESIGN / KNOWLEDGE (build host unavailable — see Blocker)
**Phase**: FORMALIZED (verified mediant calculus; open constant remains open)
**Outcome**: progress (no Lean change; roadmap + literature recorded)

## Goal

Connect the already-verified mediant / minimal-denominator calculus in
`proofs/Proofs/Erdos1005ProblemOQ02.lean` (19 theorems, 0 sorries, 0 axioms)
to the genuinely open question — the Mayer–Erdős run constant
`c ∈ [1/12, 1/4]` for `f(n)`, the longest run of *similarly ordered* Farey
fractions — and pin down the precise next Lean lemma.

## Literature grounding (corrects the bound recorded in the parent knowledge.md)

The sharp current bounds are due to **Wouter van Doorn (2025)**,
*"Improved bounds for the Mayer–Erdős phenomenon on similarly ordered Farey
fractions"*, arXiv:**2509.00121**:

- **Lower bound.** For all `k` and `l > k` with `l − k ≤ (1/12 − o(1)) n`,
  the similar-ordering inequality `(a_l − a_k)(b_l − b_k) ≥ 0` holds. Hence
  `f(n) ≥ (1/12 − o(1)) n`.
- **Upper bound.** For every `n ≥ 4` there exist `k < l < k + n/4 + 5` with
  `(a_l − a_k)(b_l − b_k) < 0`. Hence `f(n) ≤ n/4 + 5` (the parent
  `knowledge.md` recorded the looser `n/4 + O(1)`; `+5` is the explicit
  constant).

So the open question is exactly the value of `c` in `f(n) = (c + o(1)) n`,
known only to lie in `[1/12, 1/4]`.

Two fractions `a/b`, `a'/b'` are *similarly ordered* iff
`(a' − a)(b' − b) ≥ 0`. The file's `similarlyOrdered_iff_monotone` already
records the equivalent "the two coordinate orderings agree" form.

## How the verified lemmas feed a counting argument

The verified results in `Erdos1005ProblemOQ02.lean` are exactly the
Stern–Brocot / Farey *local* facts a run-length count rests on:

1. **Minimal-denominator theorem** (`denom_ge_of_between`,
   `eq_mediant_of_denom_eq`, `mediant_is_min_denominator`): every fraction
   strictly inside a unimodular gap `a/b < c/d` has denominator `q ≥ b + d`,
   with equality only at the mediant `(a+c)/(b+d)`. This is the engine that
   converts "order `n`" (a denominator cap `q ≤ n`) into a *bound on how many
   refinement levels fit*, hence on how long a monotone block can be.

2. **Strict denominator growth** (`interior_denom_gt_max`,
   `denom_ge_of_between_ne_mediant`): refining past the mediant forces the
   smallest available denominator up by `≥ min(b, d)`. Iterating, the
   admissible denominators along a path down the Stern–Brocot tree grow at
   least like the partial sums of a continued-fraction expansion.

3. **Sub-gap unimodularity + depth-two bounds** (`unimodular_left/right`,
   `mediant_gap_left/right`, `denom_ge_left_subgap` giving `q ≥ 2b + d`,
   `denom_ge_right_subgap` giving `q ≥ b + 2d`): each sub-gap is again
   unimodular, so the whole calculus recurses. Depth-two already exhibits the
   Fibonacci recurrence `F_{k+1} = F_k + F_{k-1}` on denominators.

**Roadmap to the run bound.** A run of similarly ordered consecutive Farey
fractions of order `n` corresponds to a monotone path in the Stern–Brocot
tree along which both numerator and denominator move monotonically. The
denominator cap `q ≤ n` plus the strict-growth lemma (2) bounds the depth of
such a path; the minimal-denominator lemma (1) converts depth into a count of
intermediate fractions. The constant `1/12` arises from optimizing the
trade-off between path depth and branching (van Doorn's contribution); the
verified lemmas here supply the *exact* per-step arithmetic that any such
optimization must respect. They do **not** yet assemble into the asymptotic
count — that assembly is the open work.

## Precise next Lean target

The natural next verified lemma, generalizing the depth-two bounds (3) to
arbitrary depth:

> **Depth-`k` Fibonacci denominator bound.** Along any length-`k` chain of
> nested mediant insertions starting from a unimodular gap `a/b < c/d`, every
> interior fraction has denominator `q ≥ F_{k+1} · min(b,d) + F_k · …`
> (precise Fibonacci coefficients to be fixed by the induction), so a chain of
> depth `k` requires denominator `≳ φ^k`. Equivalently: at most
> `O(log_φ n)` mediant-refinement levels fit under the order-`n` cap.

This is a clean induction over `k` using `unimodular_left/right` and
`denom_ge_of_between` as the inductive step — entirely within the existing
0-axiom toolkit, no new Mathlib dependencies. It is the bridge from the
verified *local* calculus to a *global* count.

## Blocker (why no Lean this cycle)

The Docker build host is unusable: the data volume (`/System/Volumes/Data`)
is **100% full** (≈6.9 GiB free of 926 GiB). `docker ps` responds but image
builds die with `containerd … meta.db: input/output error`, and
`docker-build.sh` exits 0 on this failure (false success — its output tail
must be read). No Lean image is cached and the local Mathlib `.olean` set is
incomplete (`Mathlib.olean` absent), so `lake env lean` cannot
`import Mathlib` either. Adding an *unverified* inductive proof to a currently
clean 0-axiom file risks silently breaking its verified status, so the
depth-`k` lemma is deferred until the build host is restored (operator action:
free disk space). This session therefore records the design + literature so
the next verified-capable session can implement the depth-`k` bound directly.

## Next Action

When the build host is back: implement the **depth-`k` Fibonacci denominator
bound** above as a 0-axiom induction in `Erdos1005ProblemOQ02.lean`, then use
it to state the `O(log n)` refinement-depth corollary — the first global
consequence of the local calculus.
