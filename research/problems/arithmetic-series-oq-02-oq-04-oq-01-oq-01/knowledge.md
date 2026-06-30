# Knowledge Base: arithmetic-series-oq-02-oq-04-oq-01-oq-01

Insights accumulated during research on this problem.

---

## ⚠️ STATE-SYNC NOTICE (2026-06-13) — the Lean file ALREADY EXISTS

> A later ACT session (PR #23066, merged 2026-06-13T21:51Z) **already created**
> `proofs/Proofs/ArithmeticSeriesOQ02OQ04OQ01OQ01.lean` with a **complete**
> proof (0 `sorry`, 0 `axiom`, 7 theorems). It is Docker-unverified only because
> of the 2026-06-13 build blackout, and is intentionally NOT yet registered in
> `proofs/Proofs.lean`.
>
> **The committed file uses the ASCENDING-factorial route, not the descending
> draft embedded below.** It rewrites via the grandparent's `ascFactorial_eq_prod`
> + Mathlib's `Nat.ascFactorial_eq_factorial_mul_choose`, with an explicit
> `n = 0` / `n = m+1` case split (the `n=0` corner is degenerate). It states the
> LHS as `Nat.choose (n+k-1) k * k!` directly rather than via `Nat.multichoose`.
>
> Consequences for the notes below:
> * The **"Dead Ends"** entry that calls the ascending route a dead end and says
>   "Prefer the descending-factorial reduction" is **superseded** — the ascending
>   route is what actually shipped and is sound on paper. Both routes remain
>   Docker-unverified; neither is confirmed against the pinned Mathlib lemma names.
> * The Session-1 **"Next ACT step: drop the draft into [the .lean file]"** is
>   **stale** — that file exists. The real remaining work is just: Docker-verify
>   the existing file, fix any lemma-name drift, register it in `Proofs.lean`,
>   and add the gallery entry. See Session 2 below.
> * The embedded descending draft (`Insights → Draft proof`) is retained as an
>   **unimplemented alternative**, not the live source of truth.

---

## Problem Understanding

**Target (multiset-coefficient identity).** Let `multichoose n k = C(n+k-1, k)` count
the number of size-`k` multisets drawn from `n` symbols. The open question asks for the
rising-factorial analogue of the parent's descending-factorial identity:

$$
\binom{n+k-1}{k}\,k! \;=\; \prod_{i=0}^{k-1}(n+i) \;=\; n(n+1)\cdots(n+k-1) \;=\; \mathrm{ascFactorial}(n,k).
$$

In Lean/Mathlib terms the cleanest statement is

```lean
theorem multichoose_factorial (n k : ℕ) :
    Nat.multichoose n k * k.factorial = ∏ i ∈ Finset.range k, (n + i)
```

with the equivalent closed form `... = Nat.ascFactorial n k`.

**Relation to the lineage.** This is the *multiset* (rising) counterpart of the parent
`arithmetic-series-oq-02-oq-04-oq-01`, which proved the *ordered-selection* (falling)
identity `Nat.choose n k * k! = n.descFactorial k` (`choose_descFactorial`). The
grandparent `arithmetic-series-oq-02-oq-04` already wired `Nat.ascFactorial` to binomials
via Mathlib's `Nat.ascFactorial_eq_factorial_mul_choose`. So the infrastructure to close
this OQ is essentially already present in the family; the new content is the
`multichoose ↦ choose (n+k-1)` bridge plus a product reindexing.

---

## Insights

### Reduction to the parent identity

`Nat.multichoose n k = (n + k - 1).choose k` (Mathlib: `Nat.multichoose_eq`). Substituting
turns the LHS into `(n+k-1).choose k * k!`, which is *exactly* the parent's
`choose_descFactorial` applied at `m := n + k - 1`:

```
(n+k-1).choose k * k!  =  (n+k-1).descFactorial k.
```

So the whole problem reduces to the product-reindexing identity

```
(n+k-1).descFactorial k  =  ∏ i ∈ range k, (n + i).
```

### The reindexing step

`Nat.descFactorial_eq_prod_range : m.descFactorial k = ∏ i ∈ range k, (m - i)` gives, at
`m = n+k-1`,

```
∏ i ∈ range k, (n + k - 1 - i).
```

Reflecting the index with `Finset.prod_range_reflect` (`∏ i ∈ range k, f (k-1-i) = ∏ i ∈ range k, f i`)
rewrites this to `∏ i ∈ range k, (n + k - 1 - (k - 1 - i))`, and for `i < k` the inner
`ℕ`-arithmetic collapses: `n + k - 1 - (k - 1 - i) = n + i` (dischargeable by `omega` under
the `range` membership hypothesis). That yields `∏ i ∈ range k, (n + i)`, as required.

### Draft proof (UNVERIFIED — Docker/Aristotle both down 2026-06-13)

```lean
import Proofs.ArithmeticSeriesOQ02OQ04OQ01
import Mathlib.Data.Nat.Choose.Multinomial   -- for Nat.multichoose / Nat.multichoose_eq

namespace ArithmeticSeriesOQ02OQ04OQ01OQ01

open Finset ArithmeticSeriesOQ02OQ04OQ01

/-- Multiset-coefficient (rising-factorial) analogue of the descending-factorial identity:
    `C(n+k-1, k) * k! = n(n+1)...(n+k-1)`. -/
theorem multichoose_factorial (n k : ℕ) :
    Nat.multichoose n k * k.factorial = ∏ i ∈ range k, (n + i) := by
  rw [Nat.multichoose_eq, choose_descFactorial, Nat.descFactorial_eq_prod_range,
      ← Finset.prod_range_reflect]
  refine Finset.prod_congr rfl ?_
  intro i hi
  have : i < k := Finset.mem_range.mp hi
  omega

/-- Closed form against Mathlib's `ascFactorial`. -/
theorem multichoose_factorial_asc (n k : ℕ) :
    Nat.multichoose n k * k.factorial = Nat.ascFactorial n k := by
  rw [multichoose_factorial, Nat.ascFactorial_eq_prod_range]

end ArithmeticSeriesOQ02OQ04OQ01OQ01
```

**Confidence:** high on the mathematics and the reduction; medium on exact Mathlib lemma
spellings. Names to confirm against the pinned Mathlib once a build is available:
`Nat.multichoose_eq`, `Nat.descFactorial_eq_prod_range`, `Nat.ascFactorial_eq_prod_range`,
`Finset.prod_range_reflect`. The import providing `Nat.multichoose` may be
`Mathlib.Data.Nat.Choose.Multinomial` or a sibling; `import Mathlib` is the safe fallback.

---

## Approach comparison (NOT a dead end — see STATE-SYNC notice)

- Routing through `Nat.ascFactorial_eq_factorial_mul_choose` (as the grandparent
  `ArithmeticSeriesOQ02OQ04` does) carries an `n ↦ n+1` index shift
  (`C(n+k, k) * k! = ascFactorial (n+1) k`), so the `n = 0` corner must be handled
  separately (a one-line degenerate case). The descending route below
  (`choose_descFactorial`-at-`(n+k-1)` + `prod_range_reflect`) avoids the case
  split but relies on a `range`-membership `omega` discharge for the reindexing.
  **Both are valid.** The committed `.lean` file (#23066) took the ascending route
  with the `n=0`/`n=m+1` split; this knowledge.md's embedded draft took the
  descending route. Neither has been Docker-verified yet. The earlier
  "prefer descending / ascending is a dead end" judgement did not survive the
  ACT session and should not be treated as binding.

---

## Session Log

### Session 2026-06-13 (Session 1) — ORIENT survey

**Mode**: FRESH · **Outcome**: surveyed (ORIENT)

- Fixed the precise Lean statement: `Nat.multichoose n k * k! = ∏ i ∈ range k, (n+i)`.
- Identified full proof path reducing to the parent's `choose_descFactorial` + a
  `prod_range_reflect` reindexing; wrote a draft proof (above).
- **Verification blocked:** Docker daemon down and Aristotle backend returns 404
  ("Resource not found") this session, so the draft is NOT built and NOT added to the
  Lean build tree (an unverified file could break a future full `lake build`).
- **Next ACT step (when Docker returns):** drop the draft into
  `proofs/Proofs/ArithmeticSeriesOQ02OQ04OQ01OQ01.lean`, run
  `./proofs/scripts/docker-build.sh Proofs.ArithmeticSeriesOQ02OQ04OQ01OQ01`, fix any
  lemma-name drift, then add the gallery entry `src/data/proofs/arithmetic-series-oq-02-oq-04-oq-01-oq-01/`.
  > **SUPERSEDED — see Session 2.** A separate ACT session (#23066) already created
  > the `.lean` file (using the ascending route), so "drop the draft into [file]" is
  > moot; only Docker-verification + registration + gallery entry remain.

### Session 2026-06-13 (Session 2) — STATE-SYNC

**Mode**: REVISIT · **Outcome**: tracker corrected (no proof change)

- Discovered that the ORIENT survey (this knowledge.md, PR #23089, merged 19:02Z)
  and the ACT implementation (PR #23066, merged 21:51Z) **diverged**: the survey
  recommended the descending-factorial route and flagged ascending as a dead end,
  but the ACT session shipped `ArithmeticSeriesOQ02OQ04OQ01OQ01.lean` using the
  **ascending** route with an `n=0`/`n=m+1` case split. The ACT session did not
  update this knowledge.md, leaving it self-contradictory.
- Verified the committed file on `origin/main`: 125 lines, **0 `sorry`, 0 `axiom`,
  7 theorems** (main identity + `_one/_two/_three` specializations + 3
  `native_decide` checks). The mathematics of the ascending reduction checks out
  on paper; it remains **Docker-unverified** (build blackout persists — `docker
  info` times out this session).
- Added the STATE-SYNC notice at the top and corrected the "Dead Ends" framing.
  No `.lean` or `meta.json` changes — this is a documentation-consistency fix only.
- **Real remaining work (unchanged blockers):** Docker-verify the existing file,
  reconcile any Mathlib lemma-name drift (`Nat.ascFactorial_eq_factorial_mul_choose`,
  the parent's `ascFactorial_eq_prod`), register in `Proofs.lean`, add the gallery
  entry. All Docker-gated.
