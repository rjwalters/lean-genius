# Knowledge Base: quadratic-reciprocity-algorithm-oq-03

Insights accumulated during research on this problem.

---

## Problem Understanding

**Target.** Give a *permutation-sign* proof of quadratic reciprocity, organized around
**Zolotarev's lemma**: for an odd prime `p` and `a` coprime to `p`,

$$\left(\tfrac{a}{p}\right) = \operatorname{sgn}(\pi_a), \qquad \pi_a : \mathbb{Z}/p\mathbb{Z}\to\mathbb{Z}/p\mathbb{Z},\ x\mapsto a x.$$

The Legendre symbol equals the sign of the multiply-by-`a` permutation of the residue field.
From Zolotarev's lemma, full reciprocity follows by computing the sign of a single "shuffle"
permutation on `ZMod p × ZMod q`.

This is the most *computational* of the 200+ known proofs of reciprocity and sits naturally next
to the parent gallery entry `quadratic-reciprocity-algorithm` (a flip-and-reduce evaluator). The
statement is already pinned down because Mathlib has reciprocity (`legendreSym.quadratic_reciprocity`,
Gauss-sum proof), so any Zolotarev development is cross-checkable.

---

## Insights

### Session 2026-06-14 (researcher-8, S1) — build-free ORIENT

**Mode:** FRESH (claimed from pool, knowledge score 0). **Outcome:** scouted/ORIENT. Docker down
(`docker info` timeout) and no materialized Mathlib in the worktree, so no Lean was built or
verified; this session resolves the OQ on paper and pins the formalizable core.

#### The proof, made precise (so the Lean target is unambiguous)

Work in the finite field `F = ZMod p`, `p` an odd prime. Its unit group `Fˣ` is **cyclic of order
`p − 1`** (finite-field units are cyclic). Fix a generator `g`.

1. **`π_a` is a permutation of `F` fixing 0.** For `a ≠ 0`, `x ↦ a x` is `Equiv.mulLeft₀ a ha :
   F ≃ F`; it fixes `0` and restricts to a permutation of the `p − 1` units.

2. **`sgn(π_g) = −1`.** Because `g` generates `Fˣ`, the orbit of `1` under repeated multiplication
   by `g` is *all* `p − 1` units, so `π_g` is a single `(p − 1)`-cycle on the units (plus the fixed
   point `0`). The sign of an `m`-cycle is `(−1)^{m−1}`, hence
   `sgn(π_g) = (−1)^{(p−1)−1} = (−1)^{p−2} = −1` since `p` is odd (`p − 2` is odd).

3. **Zolotarev for general `a`.** Write `a = g^k` in `Fˣ`. Then `π_a = (π_g)^k` (multiplication is
   associative), and `sgn` is a homomorphism, so `sgn(π_a) = sgn(π_g)^k = (−1)^k`.

4. **Tie to the Legendre symbol.** `a` is a quadratic residue mod `p` iff its discrete log `k` is
   even; equivalently `legendreSym p a = (−1)^k` (Euler's criterion:
   `legendreSym p a ≡ a^{(p−1)/2} = g^{k(p−1)/2}`, and `g^{(p−1)/2} = −1` since `g` has order
   `p − 1`, giving `(−1)^k`). Combining (3) and (4): `legendreSym p a = sgn(π_a)`. ∎

This identifies **exactly** where the genuine mathematics lives (steps 2 and 4) and where it is
bookkeeping with existing Mathlib homomorphism lemmas (steps 1 and 3).

#### Mathlib inventory (what carries the proof) and the gap

Relevant, already-present machinery (names to confirm at build time; all in current Mathlib):

- `legendreSym p a : ℤ`; Euler's criterion `ZMod.euler_criterion` / `legendreSym.eq_pow`
  (`(legendreSym p a : ZMod p) = a ^ (p / 2)`).
- `Equiv.mulLeft₀ : a ≠ 0 → α ≃ α` for a `GroupWithZero`/field `α` — supplies `π_a` as an `Equiv`.
- `Equiv.Perm.sign : Perm α →* ℤˣ` (Fintype + DecidableEq), with `map_pow`/`map_one`.
- Sign of a cycle: `Equiv.Perm.IsCycle.sign` (`hc.sign = -(-1) ^ c.support.card`).
- `Fˣ` cyclic for a finite field `F`: the `IsCyclic Fˣ` instance (finite-field units), giving a
  generator and a discrete-log decomposition `a = g ^ k`.

**Confirmed Mathlib gap (the OQ is genuinely open in-gallery and absent upstream):** Zolotarev's
lemma itself — `legendreSym p a = Perm.sign (mulLeft a)` — is **not** in Mathlib. Mathlib proves
reciprocity via Gauss sums (`Mathlib.NumberTheory.LegendreSymbol.GaussSum` /
`...QuadraticReciprocity`) and does **not** isolate the permutation-sign characterization. So the
Zolotarev lemma is a real, reusable addition (and a plausible Mathlib contribution on its own).

**Second, larger gap — the reciprocity step.** Deriving `(p/q)(q/p) = (−1)^{(p−1)/2·(q−1)/2}` from
Zolotarev (the Zolotarev–Frobenius argument) needs the sign of a specific permutation of
`ZMod p × ZMod q` / `ZMod (p·q)` (the "row-vs-column"/CRT shuffle). Mathlib has **no**
lattice-shuffle-sign machinery for this; it must be built. **Honesty flag:** the shuffle-sign
parity count reproduces the same `∑⌊·⌋` parity as Eisenstein's lattice-point proof — care is
needed to keep the derivation genuinely permutation-theoretic rather than a relabelling of the
existing Mathlib proof. This step is the bulk of the work and is the part most at risk of being
"a second proof in name only."

#### Formalizable core vs. build-gated remainder

- **Milestone 1 — Zolotarev's lemma (the clean win, ~80–120 LOC).** `legendreSym p a =
  Perm.sign (Equiv.mulLeft₀ a ha)` (with the `ℤˣ → ℤ` coercion). Self-contained: cyclic units +
  cycle-sign + Euler's criterion. This is the right first build target and is **oq-01-independent**
  (oq-01 is the Euclidean *algorithm*; this is the sign characterization). Buildable as soon as
  Docker/Mathlib return.
- **Milestone 2 — reciprocity from Zolotarev (gated, larger, ~250–450 LOC).** Build the CRT/shuffle
  permutation and compute its sign two ways. Needs new permutation-sign infrastructure; assess
  buildability against the < 500-line guideline only after Milestone 1 lands. Because Mathlib
  *already* has reciprocity, Milestone 2 is pedagogical/structural value, **not** a gap-filler — it
  should only proceed if it stays genuinely permutation-theoretic (see honesty flag above).

#### Doc-integrity finding (registry)

`src/data/research/problems/quadratic-reciprocity-algorithm-oq-03.json` lists
`leanFiles = [QuadraticReciprocityAlgorithmOQ01.lean]` — that is the **sibling oq-01** file
(`jacobiAlgo`, the recursive evaluator), not this problem. oq-03 has **no** Lean file yet. This is
the seeker "leanFiles slug-matched to a sibling" misattribution pattern; cleared to `[]` in local
registry state this session so oq-03 is not mistaken for already-formalized.

### Session 2026-06-14 (researcher-4, S2) — build-free numerical verification of the M1 spine

**Mode:** CONTINUE. Docker still down, no materialized Mathlib, Aristotle `prove` still
"Resource not found" — so still build-free. Used `python3`/sympy to **verify Milestone 1's exact
statement and its key structural step numerically**, de-risking the eventual Lean ACT (confirms
the lemma is TRUE as written — not a false-converse/sign-convention trap — and pins the precise
form before any code is written).

- **Zolotarev's lemma holds exactly as stated.** Computed the permutation `π_a : x ↦ a·x` on
  `ZMod p` (fixing 0) for every odd prime `p < 40` and every `a ∈ {1,…,p−1}`, took its
  permutation sign by cycle decomposition, and compared to `legendre_symbol(a,p)`:
  **all match** (e.g. `p=7`: signs `+,+,−,+,−,−` for `a=1..6` = Legendre symbols). The
  units-only variant (drop the fixed point 0) gives the **same** sign for all primes `< 60` —
  confirming the `Equiv.mulLeft₀ a ha` on the field and its restriction to `Fˣ` carry the same
  sign, so either formulation is sound for the Lean statement.
- **Step (2) verified directly:** for every prime `p < 60`, multiplication by a primitive root
  `g` is a **single `(p−1)`-cycle** on the units (cycle count = 1), so `sgn(π_g) = (−1)^{p−2} = −1`.
  This is the one genuinely structural claim in the M1 proof and it checks out.
- **Implication for ACT:** the M1 target `legendreSym p a = (Perm.sign (Equiv.mulLeft₀ (a:ZMod p) ha) : ℤ)`
  is numerically certified; the remaining work is purely wiring the four Mathlib lemmas (cyclic
  units, cycle-sign, `map_pow`, Euler's criterion), names listed above to confirm at build.

No new dead ends; no change to the Milestone-2 honesty flag.

### Session 2026-06-14 (researcher-5, S3) — made the M1 verification reproducible

**Mode:** CONTINUE. Docker still down (`docker ps` times out), no materialized Mathlib — build-free.
Researcher-4's S2 verified Milestone 1 numerically but only in prose (the computation was
ephemeral). This session **commits the verification as a re-runnable artifact** so it survives the
outage and can be re-checked by anyone:

**Artifact:** `verify_zolotarev.py` (committed beside this file; `python3 verify_zolotarev.py`,
needs only sympy; exits non-zero on any mismatch). It re-derives and asserts every step of the S1
proof for **all odd primes `3 ≤ p < 80`** (21 primes), every nonzero residue `a` — wider than the
S2 prose (`< 40` / `< 60`) and with the discrete-log steps made explicit:

- **Main identity:** `legendreSym p a = sign(π_a)`, `π_a : x ↦ a·x` on `ZMod p`. The sign is taken
  independently by orbit decomposition (`sign = (−1)^(n − #cycles)`), so the match is a genuine
  cross-check, not a restatement of any Legendre formula. ✅ all 21 primes, every `a`.
- **Step 1** `π_a` fixes 0, permutes the units; **Step 2** `π_g` is a single `(p−1)`-cycle on the
  units (orbit lengths asserted `== [p−1]`) so `sign(π_g) = −1 = (−1)^{p−2}`; **Step 3** with
  `a = g^k`, `sign(π_a) = (−1)^k`; **Step 4** `legendreSym p a = (−1)^k = a^{(p−1)/2} mod p`. All ✅.

This converts S2's "verified, trust the prose" into a durable, reproducible certificate of the
exact Lean target. No change to strategy, scope, Mathlib inventory, or the Milestone-2 honesty flag.

**Registry note (unchanged from prior sessions):** `src/data/research/problems/...-oq-03.json`
`currentState` still trails reality (reads phase NEW / iteration 1 while the work is ORIENT
iteration 2/3). That file is DB-managed and not present in this worktree, so it cannot be corrected
from the research branch; the top-level `phase: ORIENT` and `knowledge.progressSummary` there are
already accurate.

### Session 2026-06-14 (researcher-4, S4) — ACT-readiness de-risk: every M1 bearer pinned to file:line @v4.26.0

**Mode:** CONTINUE. Both backends still down (Docker `docker info` times out; Aristotle MCP
`prove` returns `"Resource not found"` — the tool now *loads* but the backend is unreachable, so a
submitted M1 snippet could not be dispatched). The M1 spine is already numerically certified and
durably scripted (S2/S3), so the only remaining build-free risk on M1 was the standing caveat
"**confirm exact Mathlib names at build time**." This session closes that caveat: each of the four
bearer lemmas + the cyclic-units instance was located in Mathlib **at the repo's exact pin**
(`lean-toolchain` = `v4.26.0`, `lake-manifest` mathlib rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)
by fetching the source at that rev via `gh api .../contents/<path>?ref=<rev>`. All present, with
the signatures the M1 proof needs:

| M1 step | Bearer (confirmed @ v4.26.0) | Location |
|---------|------------------------------|----------|
| π_a as a `Perm` (fixes 0) | `Equiv.mulLeft₀ (a : G₀) (ha : a ≠ 0) : Perm G₀` | `Mathlib/Algebra/GroupWithZero/Units/Equiv.lean:34` |
| units cyclic ⇒ generator `g`, `a = g^k` | `instance [Finite Rˣ] : IsCyclic Rˣ` (finite integral domain) + `IsCyclic.exists_generator` | `Mathlib/RingTheory/IntegralDomain.lean:137` |
| sign of the `(p−1)`-cycle | `Equiv.Perm.IsCycle.sign : sign f = -(-1) ^ #f.support` | `Mathlib/GroupTheory/Perm/Cycle/Basic.lean:434` |
| Euler's criterion (tie to `(−1)^k`) | `legendreSym.eq_pow : (legendreSym p a : ZMod p) = (a : ZMod p) ^ (p/2)` and `ZMod.euler_criterion {a} (ha : a ≠ 0) : IsSquare a ↔ a^(p/2) = 1` | `Mathlib/NumberTheory/LegendreSymbol/Basic.lean:114, :62` |

Note `mulLeft₀` returns a `Perm G₀` directly (not a bare `Equiv`), so the target statement
`legendreSym p (a.val : ℤ) = (Equiv.Perm.sign (Equiv.mulLeft₀ a ha) : ℤ)` type-checks as written —
`Perm.sign` applies with no wrapping. `legendreSym (a : ℤ)` takes an integer argument with `p`/`[Fact
p.Prime]` as section variables, so the `a.val` cast is the right bridge from `a : ZMod p`.

**Upstream-gap re-audit (the load-bearing justification this is open research):** searched current
Mathlib (default branch, *newer* than the pin) for `zolotarev` and for any `legendreSym` lemma
involving `sign`/`perm`/`mulLeft` — **zero hits**. Mathlib still proves reciprocity only via Gauss
sums and does not isolate the permutation-sign characterization. The gap is intact; M1 remains a
genuine, reusable addition (and a plausible standalone Mathlib contribution).

**Net effect:** M1 is now *paste-ready* — numerically certified (S2/S3) **and** every Mathlib
dependency pinned to an exact `file:line` at the build version, so the eventual ACT is pure wiring
with no name-discovery risk. No change to strategy, scope, or the Milestone-2 honesty flag.
Milestone 2 (reciprocity from the CRT/shuffle-sign) bearers deliberately NOT audited — gated behind
M1 and still subject to the "second proof in name only" honesty flag.

---

## Milestone 2 numerically certified (S6, researcher-2) — grid-transpose sign is the bridge

`verify_reciprocity_m2.py` (all asserts pass, distinct odd primes `3 ≤ p,q < 60`, 240 pairs)
discharges the **honesty flag** on M2: it pins exactly which permutation realizes the reciprocity
factor, using verify-before-assert (candidate relations are *computed*, asserted only after the data
confirms them). Findings:

- **(B) The grid-transpose permutation sign is the reciprocity factor — a self-contained,
  M1-independent combinatorial identity.** Let `σ = c∘r⁻¹` on `{0..pq-1}`, where `r(i,j)=i·q+j`
  (row-major) and `c(i,j)=j·p+i` (column-major), `i∈[0,p), j∈[0,q)`. Then
  `sign(σ) = (-1)^((p-1)/2·(q-1)/2)` for **all** 240 pairs. This is the genuinely new building
  block beyond M1; it is *not* equivalent to QR (it is true unconditionally).
- **(A) Zolotarev signs reconfirmed** as the other building block: `sign(mult_q on ℤ/p)=(q/p)`,
  `sign(mult_p on ℤ/q)=(p/q)`.
- **QR is the assembly** `(p/q)(q/p) = sign(σ) = (-1)^((p-1)/2·(q-1)/2)` — reproduced from (A)+(B).
- **Refuted guess (verify-before-assert win):** the *naive* CRT-listing permutation
  `ρ(k)=(k mod p)·q + (k mod q)` was conjectured to carry the reciprocity sign — **it does NOT**
  (`sign(ρ) ≠ qr_rhs` and `≠ (q/p)(p/q)` across the pairs). The correct bridge is the explicit
  grid-transpose `σ`, not this CRT reindexing. Future ACT must use `σ` (B), not `ρ`.

**M2 Lean target, now pinned:** the grid-transpose sign lemma (B) — a finite, decidable
permutation-sign computation independent of M1 — assembled with the M1 Zolotarev signs to recover
reciprocity. Still Docker-gated.

**M2 bearer audit (S6, @ pin `2df2f01` / v4.26.0):**
- **The permutation-sign route is ABSENT upstream** (same status as M1): on current mathlib4,
  `Zolotarev` → 0 hits, `legendreSym … sign` → 0 hits; `quadraticReciprocity` exists (6 hits) but
  only via the **Gauss-sum** proof (`Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean`).
  So the Zolotarev/grid-sign route is a genuine, reusable gap, not duplication.
- **Building blocks present at the exact pin** (confirmed via `gh api contents?ref=2df2f01`):
  - `Equiv.Perm.sign : Perm α →* ℤˣ` — `Mathlib/GroupTheory/Perm/Sign.lean:357` (a `MonoidHom`,
    so multiplicativity `sign (σ∘τ)=sign σ · sign τ` is free); `sign_symm` :385.
  - `finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)` — `Mathlib/Logic/Equiv/Fin/Basic.lean:329`
    (the indexing that turns the `p × q` grid into `Fin (p*q)`; the grid-transpose `σ` is its
    conjugate of the factor swap `Equiv.prodComm`).
- **Residual to discharge in ACT:** express `σ` as `(finProdFinEquiv).permCongr`-conjugate of
  `prodComm`/transpose and evaluate `Equiv.Perm.sign σ = (-1)^((p-1)/2·(q-1)/2)` — no upstream lemma
  gives this sign directly, so it is the new ~30–80 LOC content (decidable for fixed p,q, but the
  uniform formula needs the explicit cycle/inversion count). Then assemble with M1 via the
  `sign` MonoidHom. This is the genuinely-new M2 work; M1 stays the prerequisite.

### Session 2026-06-14 (S7, researcher-5) — M2 conjugation-transport bearer pinned

Small refinement to the S6 M2 bearer table: the "express `σ` as a `finProdFinEquiv`-conjugate"
step (S6 residual) does **not** require any manual sign bookkeeping — its sign-preservation is a
`@[simp]` lemma at the pin. Confirmed via `gh api contents?ref=2df2f01`:

- `Equiv.Perm.sign_symm_trans_trans (f : Perm α) (e : α ≃ β) :`
  `sign ((e.symm.trans f).trans e) = sign f` — `Mathlib/GroupTheory/Perm/Sign.lean:400`, `@[simp]`.
- `Equiv.Perm.sign_trans_trans_symm (f : Perm β) (e : α ≃ β) :`
  `sign ((e.trans f).trans e.symm) = sign f` — same file `:405`, `@[simp]`.
- (companion) `Equiv.Perm.sign_trans (f g) : sign (f.trans g) = sign g * sign f` — `:369`.

**Effect on the M2 ACT:** conjugation of a permutation by *any* equiv `e` (here
`e = finProdFinEquiv`) preserves `sign`, and it fires by `simp`. So the M2 proof can compute the
grid-transpose sign on the **product type** `Fin p × Fin q` directly (the reindex permutation
`r⁻¹ ∘ c` viewed there) and transport to `Perm (Fin (p*q))` for free — no `permCongr` sign lemma
to hand-prove. This trims, but does not remove, the residual: the *new* content remains the
`(-1)^((p-1)/2·(q-1)/2)` value of the reindex permutation's sign (the inversion/cycle count), for
which there is still **no** upstream bearer. Net: M2's "~30–80 LOC" estimate stands, but the
transport sub-step is now a known `simp` rather than an open sub-task. (Build-free, Docker still
down; no Lean written. Minor ACT-readiness delta, not a new result.)

## Dead Ends

- **Algorithm-confluence route** (prove the flip-and-reduce evaluator is order-independent and read
  reciprocity off its rewrite rules): matches the literal OQ wording but is heavier to formalize
  than proving Zolotarev directly, and Mathlib has no rewrite-confluence framework to lean on.
  Deprioritized in favor of the direct Zolotarev lemma. Not disproven — just a worse first target.
