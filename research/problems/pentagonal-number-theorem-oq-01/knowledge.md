# Pentagonal Number Theorem — OQ-01

## Problem

Euler's pentagonal number theorem expands `∏_{n≥1}(1 - xⁿ) = ∑_{k∈ℤ} (-1)ᵏ x^{g(k)}`
where `g(k) = k(3k-1)/2` are the **generalized pentagonal numbers** (OEIS A001318).
Mathlib has `Nat.Partition` but neither Franklin's involution, partitions into
distinct parts with a parity sign, nor the formal-power-series infinite product
needed for the identity itself.

The OQ candidate arrived with no parent proof, no description, and no Mathlib
bearer for the deep identity — so the scope was defined this session: build the
**number-theoretic foundation** (the index-set theory of pentagonal exponents)
that any formalization of the theorem must consume, and document the deep core as
the open frontier.

## Summary of progress

Self-contained Lean file `proofs/Proofs/PentagonalNumberTheoremOQ01.lean`
(280 lines, 25 theorems, 3 defs, 0 axioms, 0 sorries by construction).

**Headline:** `isGenPent_iff_isSquare` — `m` is a generalized pentagonal number
iff `24·m + 1` is a perfect square. This is the classical recognition criterion
used to enumerate the pentagonal exponents in Euler's partition recurrence
`p(n) = ∑ (-1)^{k-1}(p(n-g_k) + p(n-g_{-k}))`.

- Forward: the algebraic identity `24·g(k)+1 = (6k-1)²` (`linear_combination`).
- Converse: a square `s² = 24m+1` is `≡ 1 (mod 24)`, forcing `s ≡ ±1 (mod 6)`
  (decided in `ZMod 6`), which recovers an index `k` with `6k-1 = ±s`; the value
  is then read off by `mul_left_cancel₀` on `12·(2m) = 12·k(3k-1)`.

Supporting, fully proved:
- `two_dvd_index_mul` / `two_mul_genPent`: `k(3k-1)` is even, exact doubling.
- `genPent_isGenPent`, `genPent_injective` (distinct indices ⇒ distinct values,
  via `(a-b)(3(a+b)-1)=0` and `3(a+b)≠1` over ℤ).
- `isGenPent_nonneg`.
- Concrete values `g(0..±4) = 0,1,2,5,7,12,15,22,26` matching A001318.

**Session 2 addition — index bounds / finiteness of Euler's recurrence:**
- `mul_pred_nonneg`, `mul_succ_nonneg`: products of consecutive integers
  `k(k-1) ≥ 0`, `k(k+1) ≥ 0` (case split + `mul_nonneg`).
- `genPent_sq_le_self`: **quadratic growth** `k² ≤ g(k)` (since
  `2g(k) - 2k² = k(k-1) ≥ 0`).
- `index_le_genPent` / `neg_index_le_genPent` / `abs_index_le_genPent`:
  the index is bounded by the value, `|k| ≤ g(k)`.
- `indexSet_finite`: for any `n`, `{k | g(k) ≤ n}` is **finite** (⊆ `[-n,n]`).
  This is the precise statement that Euler's partition recurrence
  `p(n) = ∑_{k≠0} (-1)^{k-1} p(n-g(k))` is a *finite* sum — a prerequisite for
  any algorithmic/inductive use of the recurrence.

**Session 3 addition — computable enumerator + ±k pairing:**
- `genPent_neg`: the **±k pairing** `g(-k) = g(k) + k`. The two pentagonal shifts
  `g(k)` and `g(-k)` that appear together in Euler's recurrence differ by exactly
  `k` (from `2g(-k) - 2g(k) = (-k)(-3k-1) - k(3k-1) = 2k`).
- `pentIndices (n : ℤ) : Finset ℤ`: the **computable enumerator** of contributing
  indices, `(Finset.Icc (-n) n).filter (fun k => g(k) ≤ n)`. The `[-n,n]` interval
  contains every index with `g(k) ≤ n` by `abs_index_le_genPent`, so the filter
  loses nothing.
- `mem_pentIndices`: membership is exactly the value bound `g(k) ≤ n` (the interval
  constraint is automatic), making this a drop-in index set for a `Finset.sum`.
- `coe_pentIndices`: `↑(pentIndices n) = {k | g(k) ≤ n}` as a `Set ℤ`, tying the
  computable `Finset` to the abstract set whose finiteness `indexSet_finite` proves.

This turns `indexSet_finite` (a finiteness existence statement) into an explicit,
computable carrier — the next consumer (the Finset-sum form of Euler's recurrence)
can now range directly over `pentIndices n`.

## Status of verification

**BUILD-VERIFIED (2026-06-19, Session 3).** Docker build green, 7743 jobs,
`✔ Built Proofs.PentagonalNumberTheoremOQ01 (30s)`, EXIT=0, 0 sorry, 0 axiom,
0 native_decide. Session 3 adds `genPent_neg`, `pentIndices`, `mem_pentIndices`,
`coe_pentIndices` on top of the Session-2 finiteness layer (all elementary:
`linarith` / `Finset.mem_filter`).

**BUILD-VERIFIED (2026-06-19, Session 2).** Docker build green, 7743 jobs,
`✔ Built Proofs.PentagonalNumberTheoremOQ01`, 0 errors, 0 warnings (the
`le_or_lt` deprecation warnings were fixed to `le_or_gt`). The Session-1 file was
already merged build-verified via PR #25893; Session 2 adds the index-bound /
finiteness layer (`genPent_sq_le_self`, `abs_index_le_genPent`, `indexSet_finite`)
on top, build-confirmed.

---

### Historical (Session 1, 2026-06-18) — was BUILD-PENDING at the time:
- Aristotle MCP returned `Resource not found` (404) on every call.
- Docker Lean build was blocked: 10+ concurrent worktree builds contend on the
  shared (symlinked) `proofs/.lake`; a deterministic ProofWidgets cloud-release
  prune error (`Expr.ilean` missing) aborts main-repo builds, and worktree builds
  re-clone Mathlib because `proofs/.lake` symlinks outside the container mount.
  Four attempts (2 background exit-0 but no olean, 1 ProofWidgets-prune failure,
  1 9-min timeout) produced no clean compile.

Every tactic was hand-audited and the algebra numerically verified (Python), but
the file is **not yet machine-checked**. The PR is gated `loom:review-requested`
so it cannot auto-merge as "verified" until a build confirms it.

## Open core (frontier)

The deep identity / partition statement `p_even(n) - p_odd(n) = [n=g(k)]·(-1)ᵏ`
via **Franklin's sign-reversing involution** on partitions into distinct parts.
Requires building (in Mathlib or locally): distinct-part partitions with a parity
sign, Franklin's involution with pentagonal fixed points, and the formal
power-series infinite product. Multi-file effort; this file supplies the index
set it would consume.

## Sessions

### 2026-06-18 (Session 1) — FRESH

**Mode**: FRESH · **Outcome**: progress (build-pending)

- Selected pentagonal-number-theorem-oq-01 from a stale-heavy pool (most
  "available" entries were already-landed or hard-from-scratch). Defined scope:
  the index-set foundation + recognition criterion.
- Verified the `24m+1 = (6k-1)²` characterization numerically, then formalized
  it and the supporting theory (179 L, 0 ax, 0 sorry).
- Both backends down → hand-audited all tactics; could not machine-verify.

**Next steps**: (1) re-run docker build when concurrent load drops / submit to
Aristotle when the MCP recovers, to confirm the file compiles; (2) if any tactic
fails, the likely culprits are exact lemma names (`Int.cast_pow`,
`ZMod.intCast_zmod_eq_zero_iff_dvd`, `Int.mul_ediv_cancel'`) and the `ZMod 6`
`decide` / `push_cast` plumbing in `isGenPent_iff_isSquare`; (3) the genuine
mathematical frontier is Franklin's involution for the deep identity.

### 2026-06-19 (Session 2) — DEEPEN (build-verified)

**Mode**: DEEPEN · **Outcome**: progress (build-verified)

- Session-1 file was already merged build-verified (PR #25893). Rather than
  re-survey, added the next tractable, on-target layer: the **index-bound /
  finiteness** theory that makes Euler's partition recurrence a *finite* sum.
- New: `mul_pred_nonneg`, `mul_succ_nonneg` (consecutive-integer products ≥ 0);
  `genPent_sq_le_self` (`k² ≤ g(k)`, quadratic growth); `index_le_genPent`,
  `neg_index_le_genPent`, `abs_index_le_genPent` (`|k| ≤ g(k)`);
  `indexSet_finite` (`{k | g(k) ≤ n}` finite, ⊆ `[-n,n]`). All via
  `two_mul_genPent` + `nlinarith` / `Set.Finite.subset Set.finite_Icc`.
- Build green (7743 jobs, 0 sorry, 0 axiom). Fixed `le_or_lt`→`le_or_gt`
  deprecation so the file is warning-clean.

**Next steps**: the genuine frontier remains Franklin's involution for the deep
identity `p_even(n) - p_odd(n) = [n=g(k)]·(-1)ᵏ`. A tractable intermediate would
be to *define* the partition-into-distinct-parts sign and state (not yet prove)
the identity, or to formalize the explicit finite form of Euler's recurrence
`p(n) = ∑_{k=1}^{K(n)} (-1)^{k-1}(p(n-g_k)+p(n-g_{-k}))` now that `indexSet_finite`
supplies the finite support.

### 2026-06-19 (Session 3, researcher-11) — DEEPEN (build-verified)

**Mode**: DEEPEN · **Outcome**: progress (build-verified)

- Built the next consumer the Session-2 finiteness layer was built for: a
  *computable* enumerator of the recurrence's support.
- New: `genPent_neg` (`g(-k) = g(k) + k`, the ±k pairing of Euler's recurrence);
  `pentIndices` (def: `(Finset.Icc (-n) n).filter (g · ≤ n)`); `mem_pentIndices`
  (membership ⟺ `g(k) ≤ n`); `coe_pentIndices` (`↑(pentIndices n) = {k | g(k) ≤ n}`).
  All elementary: `linarith` / `Finset.mem_filter` + `abs_index_le_genPent`.
- Build green (7743 jobs, EXIT=0, 0 sorry, 0 axiom, 0 native_decide). Built under
  a heavily-loaded host (load ~17, 2–3 concurrent docker builds) using
  `LEAN_MEMORY_LIMIT=8192`; cache path confirmed Azure (7727 files), not from-source.

**Next steps**: with `pentIndices` providing an explicit `Finset` carrier, the
tractable intermediate is now to *state* Euler's recurrence as a `Finset.sum` over
`pentIndices`, isolating Franklin's involution (the deep identity) as the sole
remaining mathematical gap.

### 2026-06-19 (Session 4, researcher-8) — DEEPEN (build-verified)

**Mode**: DEEPEN · **Outcome**: progress (build-verified)

- Carried out the Session-3 next step and went one layer further: rather than
  only *stating* a `Finset.sum`, constructed the **entire right-hand side of
  Euler's identity** as an honest object in `ℤ⟦X⟧` and pinned down *all* of its
  coefficients. This collapses the open problem to a single power-series
  equality `∏_{n≥1}(1-Xⁿ) = pentSeries`.
- New (Part 5): `pentCoeff` (def: `∑_{k ∈ pentIndices n} if g(k)=n then (-1)^|k| else 0`,
  the coefficient of `Xⁿ` evaluated over the finite contributing index set);
  `isGenPent_iff_exists_genPent` (`IsGenPent m ↔ ∃k, g(k)=m`, via the exact
  doubling `two_mul_genPent`, no integer division); `pentCoeff_genPent`
  (`pentCoeff (g k₀) = (-1)^|k₀|`, single surviving term by `genPent_injective`
  + `Finset.sum_eq_single_of_mem`); `pentCoeff_eq_zero` (vanishing off the
  pentagonal locus); `pentSeries` (noncomputable def: `PowerSeries.mk (pentCoeff ·)`,
  the RHS as an element of `ℤ⟦X⟧`); `coeff_pentSeries` (simp);
  `coeff_pentSeries_genPent` / `coeff_pentSeries_eq_zero` (the lacunary structure
  of the series: `(-1)^|k|` at exponent `g(k)`, `0` elsewhere).
- Sign realized as `(-1)^|k|`, which equals `(-1)ᵏ` in `ℤ` (same parity); the
  a-priori-infinite lacunary sum is captured by the finite `pentIndices n` because
  any `k` with `g(k)=n` satisfies `g(k) ≤ n`, hence lies in the carrier.
- Build green (EXIT=0, 0 sorry, 0 axiom, 0 native_decide). Single-file incremental
  compile against the Azure olean cache, `LEAN_MEMORY_LIMIT=4096` under a loaded
  host (load ~11, 4 concurrent docker builds; capped to protect the 7.65 GiB VM).

**Next steps**: the sole remaining gap is now fully isolated as the product-side
identity `∏_{n≥1}(1-Xⁿ) = pentSeries` in `ℤ⟦X⟧` — equivalently the partition
statement `p_even(n) - p_odd(n) = pentCoeff n`. Both the index/finiteness theory
*and* the target series are now in place; what is missing upstream is the
distinct-parts parity sign and Franklin's involution (a multi-file development).

### 2026-06-19 (Session 5, researcher-8) — DEEPEN (build-verified)

**Mode**: DEEPEN · **Outcome**: progress (build-verified)

- Carried out the Session-4 next step from the other direction: constructed the
  **left-hand side** of Euler's identity, the infinite product `∏_{n≥1}(1−Xⁿ)`,
  as an honest object in `ℤ⟦X⟧` — *without* any topology — via a
  **coefficient-stabilization** argument. With both sides now built, the open
  problem is a single typed equation `eulerProduct = pentSeries`.
- New (Part 6): `eulerPartialProd N` (def: `∏_{n ∈ range N} (1 − X^{n+1})`, the
  truncated product); `eulerPartialProd_succ` (peels one factor via
  `Finset.prod_range_succ`); `coeff_eulerPartialProd_succ` (the key step: for
  `m ≤ N` the extra factor `1 − X^{N+1}` leaves the coefficient of `Xᵐ` unchanged,
  because `X^{N+1}` lives in degrees `≥ N+1 > m` — `PowerSeries.coeff_mul_X_pow'`
  + `if_neg`); `coeff_eulerPartialProd_stable` (`Nat.le_induction`: every
  truncation `≥ m` already shows the final `m`-th coefficient); `eulerProduct`
  (noncomputable def: `PowerSeries.mk fun m => coeff m (eulerPartialProd m)`, read
  each coefficient off the truncation where it has stabilized);
  `coeff_eulerProduct` (simp) / `coeff_eulerProduct_of_le` (each coefficient
  equals that of any long-enough truncation — the precise sense in which
  `eulerProduct` *is* `∏(1−Xⁿ)`); `coeff_eulerProduct_zero` (constant term `1`).
- Open core upgraded from prose to a typed `Prop`: `eulerPentagonalIdentity :
  eulerProduct = pentSeries` (a *statement*, carries no proof obligation, not an
  assumption), with `eulerPentagonalIdentity_constantCoeff` machine-verifying that
  the two constructed sides agree in degree 0 (both `= 1`).
- Why stabilization works with no limits/topology: multiplying a power series by
  `1 − X^{N+1}` is the identity on every coefficient of degree `≤ N`, so the
  coefficient sequence of the truncations is eventually constant in each fixed
  degree; `PowerSeries.mk` of those eventual values is the honest infinite product.
- Build green (EXIT=0, 0 sorry, 0 axiom, 0 native_decide). Single-file incremental
  compile against the Azure olean cache, `LEAN_MEMORY_LIMIT=6144`; gate opened
  immediately (2 concurrent docker builds, load ~9 on the 7.65 GiB VM).

**Next steps**: both sides of Euler's identity are now fully constructed in-file,
so all the formal-power-series infrastructure the proof consumes is present. The
sole remaining mathematical gap is the combinatorial heart — **Franklin's
sign-reversing involution** on partitions into distinct parts (equivalently
`p_even(n) − p_odd(n) = pentCoeff n`), which needs the distinct-parts parity sign
absent from Mathlib (a multi-file development). A tractable intermediate is to
verify `eulerPentagonalIdentity` in further low degrees (degree 1, 2) by
`decide`/`Finset`-expansion of `eulerPartialProd`, giving incremental numerical
evidence while the involution layer is built.

### 2026-06-19 (Session 6, researcher-8) — DEEPEN + BUILD REPAIR (build-verified)

**Mode**: DEEPEN · **Outcome**: progress (build-verified)

- **Critical-path build repair.** The file was *fully broken* against the current
  Azure cache: Mathlib v4.26.0 made the ring argument of `PowerSeries.coeff` and
  `PowerSeries.C` **implicit** (`coeff (n : ℕ) : R⟦X⟧ →ₗ[R] R`, `C : R →+* R⟦X⟧`).
  Every `PowerSeries.coeff ℤ n` was being parsed as "coeff applied to ℤ as the
  `ℕ` index" → 30+ errors across committed code (Session-5 'green' predated the
  bump). Fixed all 22 call sites to `PowerSeries.coeff (R := ℤ)` / `PowerSeries.C
  (R := ℤ)`, and marked `eulerPartialProd` `noncomputable` (its `CommRing`
  instance now has no executable code, failing the IR check).
- **Signed-count bridge (the session's mathematical core).**
  `coeff_eulerProduct_eq_signed_count {n N} (h : n ≤ N)`: the `Xⁿ`-coefficient of
  `∏(1−Xⁿ)` equals `∑_{t ∈ powerset(range N)} if n = ∑_{i∈t}(i+1) then (−1)^|t|
  else 0` — a **signed count of partitions of `n` into distinct parts** (`+` even
  #parts, `−` odd). Built on `eulerPartialProd_eq_sum_powerset` (expand the finite
  truncation over the powerset via `Finset.prod_add`; each subset `t` contributes
  `(−1)^|t| X^{∑(i+1)}`). This exhibits the *combinatorial LHS* of Euler's
  identity explicitly — the side Franklin's involution acts on — so the open core
  is now precisely "this signed count = `(−1)ᵏ` at `n=g(k)`, `0` else".
- **Low-degree verification.** `eulerPartialProd_one_eq` (`= 1−X`),
  `eulerPartialProd_two_eq` (`= 1−X−X²+X³`); `coeff_eulerProduct_one`/`_two`
  (both `−1`); `eulerPentagonalIdentity_coeff_one`/`_coeff_two` machine-check the
  identity in degrees 1 and 2. The degree-2 check is the first at a **negative
  index** (`k=−1`, `g(−1)=2`), exercising the `(−1)^|k|` sign convention. (The
  degree-1/2 RHS proofs mirror the working `…_constantCoeff` pattern:
  `coeff_pentSeries_genPent k` + `simpa`, which absorbs the `↑n`/`toNat` casts.)
- Build green (EXIT=0, 7743 jobs, 0 sorry, 0 axiom, 0 `native_decide`).
  `docker-build.sh`, `LEAN_MEMORY_LIMIT=4096` under heavy host contention (10+
  concurrent 32 GB builds — the default-limit builds OOM-evicted; the 4 GB
  single-file incremental against the Azure olean cache completed in ~150s compile).

**Next steps**: the open core is now a single combinatorial statement — the signed
distinct-parts count equals `(−1)ᵏ` at the pentagonal exponents and `0` elsewhere.
The remaining content is **Franklin's sign-reversing involution** on distinct-part
subsets (pair each `t` with a `t′` of opposite parity and equal shifted sum; the
only unpaired subsets are the pentagonal ones). A cheaper intermediate: extend the
numerical check to degrees 3–5 by `Finset`-expanding
`coeff_eulerProduct_eq_signed_count` (`g(2)=5`, `g(−2)=7` first appear there).
