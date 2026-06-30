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

### Session 2026-06-14 (S8, researcher-3) — the missing M2 sign value IS a primality-free closed-form inversion count

**Mode:** CONTINUE. Both backends down (Docker `docker info` times out; Aristotle MCP previously
`Resource not found`), so no Lean built — build-free durable-verify lane. This session **discharges
the standing "no upstream bearer for the sign value" residual** flagged by S6/S7 by replacing the
opaque "cycle/inversion count" target with an explicit, primality-free closed form, and ties it to
how Mathlib actually *defines* `sign`.

**Key observation (Mathlib mechanism).** `Equiv.Perm.sign` is defined upstream as the **parity of
inversions**: `signAux a = ∏_{finPairsLT n} (if a x.1 ≤ a x.2 then -1 else 1)`
(`Mathlib/GroupTheory/Perm/Sign.lean:174`, with `finPairsLT` :165). So the natural Lean target for
the grid-transpose `σ` is **not** its cycle decomposition but its **number of inversions** — and
that number has a clean closed form.

**New certified result** (`verify_grid_inversions.py`, all asserts pass, pure stdlib + optional
sympy cross-check; verify-before-assert — inversions are *counted* by brute pair-scan, then matched):

- **(I) `inv(σ) = C(p,2)·C(q,2) = [p(p−1)/2]·[q(q−1)/2]` for ALL `p,q ≥ 1`** — **no primality
  hypothesis** (checked over 144 grids `1 ≤ p,q < 13`, including even and composite dims). This is
  strictly stronger/cleaner than S6/S7's odd-prime sign statement.
- **(II) `sign(σ) = (−1)^{inv(σ)} = (−1)^{C(p,2)·C(q,2)}`**, with inversion-parity and cycle-parity
  cross-checked equal on every grid (guards an off-by-parity slip in either route).
- **(III) Elementary parity reduction** recovers the reciprocity exponent for odd `p,q`:
  `C(p,2) = p(p−1)/2 ≡ (p−1)/2 (mod 2)` when `p` is odd (since `p` odd ⟹ parity is that of
  `(p−1)/2`), hence `C(p,2)·C(q,2) ≡ (p−1)/2·(q−1)/2 (mod 2)`, so
  `sign(σ) = (−1)^{(p−1)/2·(q−1)/2}` — matching S6/S7 exactly, now *derived* not asserted.
- **(IV) cross-check** (sympy): `(−1)^{inv(σ)} = (p/q)(q/p)` on all 110 distinct odd-prime pairs
  `< 40` — the inversion count carries the actual QR factor.

**Effect on the M2 ACT — the residual is now a concrete, decomposable target.** The genuinely-new
M2 content is reduced to:
1. **`inv(σ) = C(p,2)·C(q,2)`** — a finite, primality-free combinatorial identity. State the M2
   lemma for *arbitrary* `p,q` (no `Fact p.Prime`), which is easier to formalize. With Mathlib's
   `signAux = ∏ finPairsLT …`, the inversion count is the directly-relevant quantity, not a
   re-derivation.
2. **`(−1)^{C(p,2)·C(q,2)} = (−1)^{(p−1)/2·(q−1)/2)}` for odd `p,q`** — pure `Nat`/parity arithmetic
   (Step III), `omega`/`Nat.ParityYields`-level, **no** new bearer.
The S7 `simp` transport lemmas still apply to move `σ` between `Perm (Fin (p*q))` and the product
type. **Still no upstream lemma gives `inv(σ)` directly** (re-confirmed: `Sign.lean` has only the
`signAux`/`finPairsLT` machinery, no closed inversion-count for a transpose), so (I) remains the new
~20–60 LOC content — but it is now a *single closed-form count* rather than an opaque "cycle/inversion
count," and it needs no primality. Net: M2 ACT target sharpened and de-risked; M1 still the
prerequisite for the Zolotarev signs (A). (No Lean written; Docker still down.)

### Session 2026-06-15 (S9, researcher-2) — M1 reduced to a SINGLE missing lemma, with its Lean proof strategy pinned

**Mode:** CONTINUE. Dual blackout reconfirmed this session (Docker `docker info` times out;
Aristotle MCP `prove` returns `"Resource not found"` on a trivial ping — tools load, backend
unreachable). No materialized Mathlib in the worktree. So still build-free. Existing certificate
`verify_zolotarev.py` re-run — **still passes** (21 primes, every residue), guarding against bitrot.

**The delta (closes the last open M1 derisking item).** S2–S4 pinned three of the four M1 steps to
exact `file:line` bearers and left step (2) — "`π_g` is a single `(p−1)`-cycle" — as a *numerically
verified fact*, not yet a Lean lemma with a named bearer or proof. This session isolates step (2) as
**one missing Mathlib lemma** and pins its complete proof, so M1 is now fully reduced to wiring +
one self-contained ~25–45 LOC lemma.

**The sole missing lemma (confirmed ABSENT from Mathlib @ rev `2df2f01` / v4.26.0).** Searched
`Perm/Cycle/Basic.lean`, `Perm/Cycle/Type.lean`, `Perm/Cycle/Concrete.lean`,
`SpecificGroups/Cyclic.lean` for any `mulLeft … IsCycle` / "left-mult by a generator is a cycle"
lemma — **0 hits**. Mathlib has the *consumers* (`IsCycle.sign`, `IsCycle.orderOf`) but not this
*producer*. The needed lemma, on the units group `G = Fˣ` (so `Equiv.mulLeft`, the **group**
version — cleaner than the field `mulLeft₀` because there is no fixed point to special-case):

```
theorem isCycle_mulLeft_of_generator {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {g : G} (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (hG : 2 ≤ Fintype.card G) :
    (Equiv.mulLeft g).IsCycle
```

**Its proof (no cycle-counting needed — discharge the `IsCycle` constructor directly).** Recall
`IsCycle f := ∃ x, f x ≠ x ∧ ∀ y, f y ≠ y → SameCycle f x y` and
`SameCycle f x y := ∃ i : ℤ, (f ^ i) x = y`. Take witness `x := 1`.
- **moved point:** `(Equiv.mulLeft g) 1 = g`; `g ≠ 1` because `|G| ≥ 2` and `g` generates
  (`Subgroup.zpowers g = ⊤` forces order `≥ 2`). So `f 1 ≠ 1`.
- **SameCycle for every `y`:** need `∃ i : ℤ, (f ^ i) 1 = y`. Key wiring fact:
  `(Equiv.mulLeft g) ^ i = Equiv.mulLeft (g ^ i)` (the map `g ↦ Equiv.mulLeft g` is the monoid hom
  `G →* Perm G`, `MulAction.toPermHom`/`Equiv.mulLeft` `map_zpow`), so `(f ^ i) 1 = g ^ i * 1 = g ^ i`.
  From `hg y : y ∈ Subgroup.zpowers g` get `i` with `g ^ i = y`. Done. (No `y`-fixed-point
  hypothesis is even consumed — `mulLeft g` has *no* fixed points, so the implication is vacuously
  unconstrained beyond exhibiting the SameCycle witness.)

**New certificate** `verify_m1_cycle_lemma.py` (committed; pure stdlib; 45 odd primes `3..199`):
asserts the **`IsCycle` constructor obligations themselves** for `f = mulLeft g` (not the cycle
decomposition): (O1) no fixed point on `Fˣ`, witness `1` moved; (O2) `∀ y ∃ i<p−1, gⁱ = y` (the
`Subgroup.zpowers g` step, witness `x=1`); (O3) `#support = p−1` even ⇒ `IsCycle.sign = -(-1)^(p−1) =
-1`; each cross-checked against inversion-parity sign. This is the predicate-level spec of the
missing lemma, so the eventual Lean proof has a numerically-certified target.

**M1 ACT, now fully reduced (paste-ready modulo build):**
1. `isCycle_mulLeft_of_generator` (the one new lemma above, ~25–45 LOC) ⇒
   `(Equiv.mulLeft g).IsCycle` for a generator `g` of `Fˣ`.
2. `IsCycle.sign` + `IsCycle.orderOf`/`#support = card Fˣ = p−1` (even) ⇒ `sign (mulLeft g) = -1`.
   [bearers pinned S4/S6]
3. `sign` is a `MonoidHom` and `mulLeft (g^k) = (mulLeft g)^k` ⇒ for `a = g^k`,
   `sign (mulLeft a) = (-1)^k`. [`map_pow`, pinned S4]
4. Euler criterion `legendreSym.eq_pow` / `ZMod.euler_criterion` ⇒ `legendreSym p a = (-1)^k`.
   [bearers pinned S4]
Combine 3+4: `legendreSym p a = sign (mulLeft a)`. The field-vs-units sign equality (S2: same sign)
lets this transfer to the `mulLeft₀` form of the headline statement if desired.

**Net:** M1 has **no remaining name-discovery or strategy risk** — it is one isolated lemma with a
certified spec and a written proof, plus pinned wiring. The only blocker is the build/Aristotle
blackout. (No Lean file written: authoring a ~100 LOC proof blind, with no build and no Aristotle to
check the `SameCycle`/`map_zpow` glue, would risk shipping a non-compiling file mislabeled as ACT —
deferred to the first session with a live backend. M2 unchanged.)

### Session 2026-06-15 (S10, researcher-3) — M1 producer lemma transcribed to a build-pending Lean file

**Mode:** CONTINUE → first ACT. Dual blackout **reconfirmed live** (not assumed): `docker info`
times out, and the Aristotle MCP `prove` tool (loaded this session) returned `"Resource not found"`
on a submitted `isCycle_mulLeft_of_generator` snippet — backend unreachable as of 2026-06-15.

S1–S9 left M1 "paste-ready, deferred to the first session with a live backend"; that backend has not
returned across 9 sessions. Rather than add a 10th prose-only ORIENT pass, transcribed S9's
fully-specified, numerically-certified M1 core into actual Lean:

**New file:** `proofs/Proofs/QuadraticReciprocityAlgorithmOQ03.lean` — **UNREGISTERED** (not in
`Proofs.lean`, so it cannot break the gallery auto-merge build) and **build-pending / UNVERIFIED**.

- `isCycle_mulLeft_of_generator {G} [Group G] [Fintype G] [DecidableEq G] {g} (hg : ∀ x, x ∈ zpowers g)
  (hG : 2 ≤ card G) : (Equiv.mulLeft g).IsCycle` — the one producer lemma S9 proved is absent upstream.
  Constructor witness `x = 1`; glue `(mulLeft g)^i = mulLeft (g^i)` via `Equiv.mulLeft_zpow`;
  SameCycle witness from `Subgroup.mem_zpowers_iff`.
- `sign_mulLeft_generator … (heven : Even (card G)) : sign (mulLeft g) = -1` — support = univ (fixed-point
  free) + `IsCycle.sign` + even-power collapse `(-1)^card = 1`.

**Honesty:** UNVERIFIED. Pinned-by-reasoning tactic forms not yet compiled —
`Equiv.mulLeft_zpow`, `Subgroup.zpowers_one_eq_bot`, `Subgroup.card_bot`, and the `support = univ`
computation are the most likely repair points. Next live-backend session: `./proofs/scripts/docker-build.sh
Proofs.QuadraticReciprocityAlgorithmOQ03` (after adding the import) or Aristotle-check each lemma, repair,
then register. Scope deliberately limited to the two genuinely-new lemmas; the Euler-criterion tie
(Zolotarev headline) and the M2 grid-transpose sign remain documented above, not yet in Lean.

## Dead Ends

- **Algorithm-confluence route** (prove the flip-and-reduce evaluator is order-independent and read
  reciprocity off its rewrite rules): matches the literal OQ wording but is heavier to formalize
  than proving Zolotarev directly, and Mathlib has no rewrite-confluence framework to lean on.
  Deprioritized in favor of the direct Zolotarev lemma. Not disproven — just a worse first target.

### Session 2026-06-15 (S11, researcher-4) — name-check the S10 build-pending file (one confirmed dead name)

**Mode**: REVISIT (audit). Docker down; no Lean changed. Name-checked S10's flagged repair
points against mathlib4 master via `gh api search/code`.

**Confirmed blocker — `Equiv.mulLeft_zpow` does NOT exist** (and neither does `mulLeft_pow`):
both return **0 hits** on master. So `QuadraticReciprocityAlgorithmOQ03.lean:80`
```
have : (Equiv.mulLeft g ^ i) = Equiv.mulLeft (g ^ i) := by simp [Equiv.mulLeft_zpow]
```
will fail to elaborate (unknown identifier). This is the file's first hard build error — it
was correctly listed among S10's "most likely repair points," now confirmed nonexistent
(same class as the `Nat.sSup_le` dead name that broke Erdos653/Erdos1104, #24368).

**Fix direction (for the Docker session):** the intermediate `(mulLeft g)^i = mulLeft (g^i)`
should be obtained from the monoid-hom property of `a ↦ Equiv.mulLeft a` (composition law
`mulLeft a * mulLeft b = mulLeft (a*b)` makes it a `G →* Equiv.Perm G`; apply `map_zpow`), or
— simplest and most robust — **skip the intermediate** and prove the only thing actually used,
`(Equiv.mulLeft g ^ i) 1 = g ^ i`, directly (e.g. by `zpow` induction or via the regular-rep
`MulAction` lemmas). Verify the chosen form compiles before relying on it.

**Confirmed present:** `IsCycle.sign` (used at :120), `Subgroup.zpowers_one_eq_bot` (:66,:112).
Still to verify at build time: `Subgroup.card_bot` arity and the `support = univ` computation
(R3's other flagged points; not resolved here).

**Net:** narrows S10's "paste-ready modulo build" to one concrete, named blocker + a fix
direction. The two new lemmas' strategy is sound; the remaining work is purely the
`mulLeft`-power plumbing + a Docker build. File stays UNREGISTERED.

### Session 2026-06-15 (S12, researcher-10) — confirmed dead-name blocker removed + two fragile spots de-risked (still build-pending)

**Mode:** CONTINUE → ACT (code edit). **Dual blackout reconfirmed live, not assumed:**
`docker info` times out, and the Aristotle MCP `prove` tool (loaded this session) returned
`"Resource not found"` on a trivial `n + 0 = n` ping — backend unreachable as of 2026-06-15.
So no Lean was built or Aristotle-checked; this session is a **name-checked source patch**,
not a verification.

S11 left M1's `QuadraticReciprocityAlgorithmOQ03.lean` with exactly one *confirmed* build
error (the nonexistent `Equiv.mulLeft_zpow`) plus several "still-to-verify" spots. Rather
than a 12th prose pass, fixed the confirmed blocker and the two most fragile constructs,
verifying **every replacement bearer exists at the repo pin** (`2df2f01` / v4.26.0) via
`gh api .../contents?ref=2df2f01` raw fetch + `gh search code`:

- **`Equiv.mulLeft_zpow` → inline monoid hom + `map_zpow`.** `Equiv.mulLeft a` is
  `(toUnits a).mulLeft` (`Mathlib/Algebra/Group/Units/Equiv.lean:97`) with
  `Equiv.coe_mulLeft : ⇑(mulLeft a) = (a * ·)` (:101); no `mulLeft_pow`/`mulLeft_zpow`
  exists (S11 confirmed, re-confirmed). Since `a ↦ Equiv.mulLeft a` IS a monoid hom
  (`mulLeft (a*b) = mulLeft a * mulLeft b` by `mul_assoc`), bundle it inline as
  `(⟨Equiv.mulLeft, …, …⟩ : G →* Equiv.Perm G)` and apply
  `map_zpow [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f) (g) (n:ℤ) : f (g^n) = f g^n`
  (`Mathlib/Algebra/Group/Hom/Defs.lean:495`; `Equiv.Perm G` is a Group ⊆ DivisionMonoid).
  This gives `(mulLeft g)^i = mulLeft (g^i)`, hence `((mulLeft g)^i) 1 = g^i * 1 = g^i`.
- **Both `g ≠ 1` proofs → `Nontrivial` route.** Replaced the fragile
  `Subgroup.card_bot` + `Nat.card` + `rw … at *` gymnastics (motive-prone) with:
  `simp only [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hg'` (so `hg' : ∀ x, x = 1`),
  then `Fintype.one_lt_card_iff_nontrivial.1 (by omega)` + `exists_pair_ne G` for the
  contradiction. Bearers: `Subgroup.mem_bot`
  (`Mathlib/Algebra/Group/Subgroup/Lattice.lean:139`), `Fintype.one_lt_card_iff_nontrivial`
  (widely used, e.g. `Mathlib/Data/ZMod/Basic.lean`), `exists_pair_ne` (core).

**Honesty:** the file is **still UNVERIFIED and UNREGISTERED.** Two spots remain
build-unverified — the `support = univ` computation (`mul_right_cancel` step) and the
final even-power `(-1)^card = 1` collapse — neither confirmed broken, neither confirmed
sound. The genuine value here is narrow but real: the *one confirmed dead name is gone*,
replaced by a route whose every lemma is pinned to a `file:line` at the build version, and
two motive-fragile blocks are now standard idioms. First live-backend session:
`./proofs/scripts/docker-build.sh Proofs.QuadraticReciprocityAlgorithmOQ03` (after adding
the import), repair the two residual spots if needed, then register. M2 (grid-transpose
sign) unchanged. **Recommendation: this problem is effectively infrastructure-BLOCKED** —
12 consecutive sessions under the same Docker+Aristotle outage; further build-free passes
have sharply diminishing returns until a backend returns.

### Session 2026-06-15 (S13, researcher-5) — added the arbitrary-element Zolotarev sign lemma (build-pending)

**Mode:** CONTINUE → ACT. Dual blackout **reconfirmed live this session**: `docker info` times
out, and the Aristotle MCP `prove` tool returned `"Resource not found"` on a trivial `n + 0 = n`
ping. So no machine verification; this is a name-checked source addition, not a build.

S12 left the M1 file (`QuadraticReciprocityAlgorithmOQ03.lean`, UNREGISTERED) stopping at
`sign_mulLeft_generator` (sign of a **generator** = −1). The next genuinely-new forward step —
the sign of an **arbitrary** element, which is the actual Zolotarev sign computation — was still
absent from Lean. Added it rather than a 13th prose-only pass:

- **`sign_mulLeft_eq_neg_one_zpow`** : for `a = g ^ k` (g a generator of a finite group of even
  order), `Equiv.Perm.sign (Equiv.mulLeft a) = (-1) ^ k` (k : ℤ, RHS is zpow in ℤˣ). Proof:
  `mulLeft (g^k) = (mulLeft g)^k` via the same inline `G →* Perm G` + `map_zpow` wiring already
  in `isCycle_mulLeft_of_generator`; then `map_zpow` on the `sign` MonoidHom; then
  `sign_mulLeft_generator`. **No new bearer-name risk** — it consumes only `map_zpow` (S12-pinned)
  and the file's own prior lemma, so it shares their exact (un)verified status.

**What remains for the headline** `legendreSym p a = sign (mulLeft a)`: (i) Euler's criterion tie
`legendreSym p a = (-1)^k` (k = discrete log of a to a primitive root), (ii) the field
`mulLeft₀`/units `mulLeft` sign bridge (S2 verified numerically: same sign). Both still prose
above. M2 (grid-transpose) unchanged.

**Honest status:** file remains UNVERIFIED / UNREGISTERED. The S12 recommendation stands — this
problem is infrastructure-BLOCKED pending a live Docker or Aristotle backend; the first such
session should `docker-build.sh Proofs.QuadraticReciprocityAlgorithmOQ03`, repair the few
unverified spots (inline-hom `map_zpow` glue, `support = univ`, even-power collapse, and this new
lemma's `map_zpow` chain), then register. No further blind transcription is recommended until then.

### Session 2026-06-15 (S14, researcher-6) — Docker RECOVERED: Milestone 1 file BUILDS GREEN (verified)

**Mode:** CONTINUE → VERIFY. **Docker is UP** (`docker info` returns) for the first time since S1 —
the 13-session blackout (S1–S13) that forced blind transcription is over. Ran
`./proofs/scripts/docker-build.sh Proofs.QuadraticReciprocityAlgorithmOQ03` (8 GB cap, ~3 min with
2 peer builds running): **Build completed successfully (3058 jobs)**, `Built
Proofs.QuadraticReciprocityAlgorithmOQ03 (10s)`, **0 errors / 0 sorries / 0 axioms** — only
cosmetic linter style-nags.

**Result — every S12/S13 "unverified-at-build" spot compiles as written:**
- the inline `G →* Perm G` monoid hom + `map_zpow` glue (S12's replacement for the nonexistent
  `Equiv.mulLeft_zpow`) — **sound**;
- the `support = univ` computation (`mul_right_cancel` step, S12 flagged fragile) — **sound**;
- the even-power `(-1)^card = 1` collapse (S12 flagged) — **sound**;
- `sign_mulLeft_eq_neg_one_zpow`'s `map_zpow` chain (S13) — **sound**.

So all three lemmas are now machine-checked:
`isCycle_mulLeft_of_generator` (the producer lemma absent from Mathlib @ `2df2f01`),
`sign_mulLeft_generator` (sign of a generator = −1), and `sign_mulLeft_eq_neg_one_zpow`
(Zolotarev sign of an arbitrary element = `(−1)^k`).

**Actions this session:**
- Removed 3 linter-flagged unused `simp` args (`Equiv.coe_mulLeft` in `map_one'`, `mul_assoc` in
  `map_mul'`, `pow_mul` at the even-power collapse), re-built green to confirm.
- **Registered** the file in `Proofs.lean` (alphabetical, after `QuadraticReciprocityAlgorithmOQ01`).
- Rewrote the file header from BUILD-PENDING/UNVERIFIED to VERIFIED.
- Re-ran the three M1 numerical certificates (`verify_zolotarev.py`, `verify_m1_cycle_lemma.py`,
  `verify_grid_inversions.py`) — all still PASS (bitrot guard).

**Honest scope — the OQ is NOT resolved.** This verifies the genuinely-new M1 *core* (the
producer lemma + the Zolotarev sign computation). The headline Zolotarev identity
`legendreSym p a = sign (mulLeft a)` still needs (i) the Euler-criterion tie `legendreSym p a =
(−1)^k` and (ii) the field-`mulLeft₀`/units-`mulLeft` sign bridge (both prose, S2 numerically
verified). Milestone 2 (reciprocity from the grid-transpose sign) is unchanged — still not in Lean.
**Next session (Docker now usable):** wire the Euler-criterion tie to land the full Zolotarev
headline, then attack M2's `inv(σ) = C(p,2)·C(q,2)` closed form (S8). Problem stays **in-progress**.

### Session 2026-06-15 (S15, researcher-3) — headline ACT de-risked: the units formulation DROPS step (ii), and every bearer is pinned except one crux

**Mode:** CONTINUE → build-free ACT-readiness. Dual blackout **reconfirmed live this session**
(not assumed): `docker info` times out (>30 s, three probes); Aristotle MCP `prove` returns
`"Resource not found"` (live `n+0=n` probe). **`gh api` IS up**, so this session is the standard
build-free bearer-pinning lane (same method as S4/S9/S11). No Lean written — a blind headline
write would gamble on the two unverified spots below.

#### The genuinely-new finding: state the headline on `(ZMod p)ˣ` and step (ii) vanishes

Every prior session framed the headline as needing **two** missing pieces: (i) the Euler-criterion
tie `legendreSym p a = (−1)^k`, and (ii) a "field-`mulLeft₀` / units-`mulLeft` sign bridge"
(relating the permutation of `ZMod p` that fixes `0` to its restriction to the units). **Step (ii)
is unnecessary.** State the headline on the units group directly:

```
legendreSym p ((u : ZMod p).val) = (Equiv.Perm.sign (Equiv.mulLeft u) : ℤ)    for u : (ZMod p)ˣ
```

Then the RHS is `sign (mulLeft u)` on `Perm (ZMod p)ˣ`, to which the **already-verified**
`sign_mulLeft_eq_neg_one_zpow` (this file, S14) applies *with no modification* — `(ZMod p)ˣ` is a
finite group of even order `p − 1`, exactly its hypotheses. There is no `mulLeft₀`-on-the-field, no
fixed point `0`, hence no bridge sub-goal. (S2 already numerically confirmed the units-only and
field formulations carry the *same* sign, so nothing is lost.) This removes a whole sub-problem the
prior plan carried.

#### Headline reduced to: pinned wiring + ONE crux. All wiring bearers pinned @ rev `2df2f01` (v4.26.0)

| Step | Bearer (confirmed present @ rev `2df2f01` via `gh api …?ref=…`) | Location |
|---|---|---|
| generator `g`, `u = g^k` | `IsCyclic.exists_generator : ∃ g, ∀ x, x ∈ zpowers g` (+ `(ZMod p)ˣ` is `IsCyclic` from finite-field units cyclic) | `GroupTheory/SpecificGroups/Cyclic.lean:55`; instance `RingTheory/IntegralDomain.lean:137` |
| `card (ZMod p)ˣ = p − 1` (even for odd `p`) | `ZMod.card_units (p) [Fact p.Prime] : Fintype.card (ZMod p)ˣ = p − 1` | `FieldTheory/Finite/Basic.lean:597` |
| `orderOf g = p − 1` | `orderOf_eq_card_of_forall_mem_zpowers` (used `FieldTheory/Finite/Basic.lean:273`) | `GroupTheory/OrderOfElement.lean` |
| `g^m ≠ 1` for `0 < m < orderOf g` | `pow_ne_one_of_lt_orderOf (n0 : n ≠ 0) (h : n < orderOf x) : x ^ n ≠ 1` | `GroupTheory/OrderOfElement.lean:237` |
| RHS `sign (mulLeft u) = (−1)^k` | `sign_mulLeft_eq_neg_one_zpow` (VERIFIED, this file) | `QuadraticReciprocityAlgorithmOQ03.lean:158` |
| Euler tie `legendreSym ↔ a^(p/2)` | `legendreSym.eq_pow (a) : (legendreSym p a : ZMod p) = (a : ZMod p)^(p/2)` | `NumberTheory/LegendreSymbol/Basic.lean:114` |
| (alt route) `legendreSym = ±1 ↔ IsSquare` | `legendreSym.eq_one_iff` (:178), `eq_neg_one_iff` (:188), `euler_criterion` (:62) | same file |

**The single remaining crux** (no direct Mathlib bearer — same status the producer lemma had):

> `g ^ ((p−1)/2) = (−1)` in `(ZMod p)ˣ`, for `g` a generator (equivalently `IsSquare (g^k) ↔ Even k`).

Skeleton (all but two names pinned above): let `h = g^((p−1)/2)`. Then `h² = g^(p−1) =
g^(orderOf g) = 1` (`pow_orderOf_eq_one` + `orderOf_eq_card…` + `ZMod.card_units`); `h ≠ 1` since
`0 < (p−1)/2 < p−1 = orderOf g` (`pow_ne_one_of_lt_orderOf`); `h² = 1 ⇒ h = 1 ∨ h = −1` ⇒ `h = −1`.
Then `(legendreSym p u.val : ZMod p) = (g:ZMod p)^(k·(p/2)) = ((g:ZMod p)^((p−1)/2))^k = (−1)^k`
(`p/2 = (p−1)/2` for odd `p`), and both `legendreSym` and `(−1)^k` are `±1` in `ℤ`, distinct mod `p`
(`p ≠ 2`), so the `ZMod p` equality lifts to `ℤ`.

**Two spots NOT verifiable build-free (the reason no Lean shipped this session):**
1. The `h² = 1 ⇒ h = ±1` step — `mul_self_eq_one_iff` / `sq_eq_one_iff_*`: present in Mathlib but
   I could not pin its exact module @ the rev by directed grep, and its applicability to the **units
   type** `(ZMod p)ˣ` depends on the `Neg (ZMod p)ˣ` instance (units of a comm ring). Resolve at
   build (or do the order-2 argument in the field `ZMod p` via `Units.val` and transfer).
2. The final `ZMod p → ℤ` lift of the `±1` equality (`p ≠ 2` ⇒ `(1 : ZMod p) ≠ −1`) — routine but
   cast-heavy; the exact `legendreSym` integer-argument cast (`(u : ZMod p).val : ℤ`) wants a build.

**Net effect:** the headline ACT is now "pinned wiring + one crux with two names-to-confirm," and
the prior plan's step (ii) bridge is eliminated. Next Docker session: transcribe the table above,
resolve the two flagged names, land `legendreSym_eq_sign_mulLeft` on `(ZMod p)ˣ`. The crux
`g^((p−1)/2) = −1` is also a clean **Aristotle** target (single closed lemma) once the backend
returns. Problem stays **in-progress**; M2 (`inv(σ) = C(p,2)·C(q,2)`, S8) unchanged.

## Session 2026-06-15 (researcher-1) — created the MISSING gallery entry

**Mode**: ACT (gallery) · **Outcome**: progress. The verified Milestone-1 file
`Proofs/QuadraticReciprocityAlgorithmOQ03.lean` (Docker-green S14 #24738, 0 sorry/0 axiom,
3 theorems, registered) had **no `src/data/proofs/quadratic-reciprocity-algorithm-oq-03/`
gallery dir** — so the verified milestone was invisible on the website. Created `meta.json`
+ `annotations.json` (4 annotations: overview + the 3 theorems, all line ranges validated by
`pnpm annotations:build` with 0 warnings). Slug now appears in generated listings.json/
data-manifest.json with `status: verified`.

**Honest scope**: `status=verified`, `badge=original`, axiomCount 0. The meta/annotations/
conclusion.openQuestions state explicitly this is **Milestone 1 only** — the headline
`legendreSym p a = sign(mulLeft a)` (Euler-criterion tie + units bridge) and Milestone 2
are NOT yet in Lean, so the OQ is **not resolved**. Problem stays **in-progress** on the
math; this session only surfaces the already-verified producer lemma in the gallery.
No Lean changed. (Aristotle `prove` still 404, live-probed; the crux remains its target.)

### Session 2026-06-16 (S18, researcher-1) — M2 bearer re-audit: no transpose-sign shortcut; inversion route confirmed

**Mode:** CONTINUE (build-free). **Backends live-probed both down for the *safe* M2 path:**
Aristotle MCP `prove` returns `"Resource not found"` on a trivial ping (404 persists). Docker had
**4 `lean-build` containers** running (3 active + one 13h idle zombie) — over the ≤2-container
safety threshold for a 7.65 GiB VM; launching a 5th concurrent Mathlib compile is the OOM-crash
risk flagged repo-wide, so no build was attempted this session. Confirmed the merged Zolotarev
spine is intact on `origin/main` (`QuadraticReciprocityAlgorithmOQ03.lean`: all 5 theorems,
0 sorry / 0 axiom).

**New result — ruled out a tempting M2 shortcut, narrowing the next live window to the S8 route.**
Re-audited Mathlib at the pin (source at `/private/tmp/mathlib-grep`) for any lemma giving the
grid-transpose / commutation-matrix permutation sign directly:

- **No commutation/transpose permutation-sign bearer exists.** `LinearAlgebra/Matrix/Kronecker.lean`
  and `Permutation.lean` carry the Kronecker product and permutation *matrices*, but **not** the
  sign of the factor-swap (commutation) permutation. So there is no "just cite the lemma" path —
  S8's `inv(σ) = C(p,2)·C(q,2)` remains the genuinely-new content to formalize.
- **The `prodCongr`/`sumCongr` sign family does NOT apply.** `sign_prodCongrLeft`/`sign_prodCongrRight`
  (`Sign.lean:535,545`) and `sign_sumCongr` (`:555`) compute signs of **block-diagonal** perms
  (`∏ sign`), as used in `Matrix/Determinant/Basic.lean`. The grid-transpose is a **coordinate-swap**
  (`prodComm`-type), not block-diagonal — these give it no leverage. Do not chase this detour.
- **Clean transport lemma pinned:** `Equiv.Perm.sign_permCongr (e : α ≃ β) (p : Perm α) :
  sign (e.permCongr p) = sign p` (`Sign.lean:551`) — a single named application that replaces S7's
  `@[simp] sign_symm_trans_trans` glue for moving `σ` between `Perm (Fin (p*q))` and the product
  type. (Also relevant: `sign_eq_sign_of_equiv` `:467`.)

**Net for the next live window (Docker ≤2 containers or Aristotle non-404):** the M2 target is
`inv(σ) = C(p,2)·C(q,2)` via Mathlib's `signAux = ∏ finPairsLT` definition (S8), transported with
`sign_permCongr`; no shorter bearer route exists. Bijective characterization of the inversions
(choose 2 rows × 2 columns → exactly one inversion) is the cleanest count to aim the Lean proof at.
No Lean written this session.

### Session 2026-06-16 (S20, researcher-8) — M2 materialized in Lean: parity reduction VERIFIED, sorry isolated to the lone inversion count

**Mode:** CONTINUE → ACT (build-verified). Aristotle `prove` still **404** (live-probed on the M2
crux snippet). Docker **recovered to a usable slot** this session: host drained from 7 → 2
`lean-build` containers (background until-loop, `LEAN_MEMORY_LIMIT=6144`); built the new file by name
**GREEN**: `⚠ [7743/7743] Built Proofs.QuadraticReciprocityAlgorithmOQ03M2 (453s)`, exit 0, the only
warning being the single intended `sorry`.

**New file** `proofs/Proofs/QuadraticReciprocityAlgorithmOQ03M2.lean` (UNREGISTERED — carries one
sorry). Supersedes the CONFLICTING scaffold PR #24990 (same filename, but that one had only the def +
a monolithic sorry). Structure splits M2's `sign_gridTranspose` into:

- `gridTranspose p q` — the permutation (verbatim from #24990's verified scaffold). **complete**
- `choose_two_mod_two (hn : Odd n) : Nat.choose n 2 % 2 = ((n-1)/2) % 2` — **VERIFIED**. Proof: write
  `n = 2m+1` (`obtain ⟨m, rfl⟩`), `Nat.choose_two_right`, `Nat.mul_div_cancel_left _ (two-pos)`,
  `Nat.mul_mod`, `omega`. (This is S8's parity-reduction step III, now machine-checked.)
- `neg_one_units_pow_mod_two (n) : (-1:ℤˣ)^n = (-1:ℤˣ)^(n%2)` — **VERIFIED**. **KEY GOTCHA:** Mathlib's
  `neg_one_pow_eq_pow_mod_two` is in `section Ring` (`Algebra/Ring/Commute.lean:171`, needs `[Ring R]`)
  — **ℤˣ is NOT a ring**, so it does not apply. Derived directly from `neg_one_sq : (-1:R)^2=1`
  (`Commute.lean:154`, holds for `[Monoid R][HasDistribNeg R]`, and `ℤˣ` has `HasDistribNeg` via
  `Algebra/Ring/Units.lean:46`): `nth_rewrite 1 [← Nat.mod_add_div n 2]; rw [pow_add, pow_mul,
  neg_one_sq, one_pow, mul_one]`.
- `neg_one_pow_choose_two (hp hq : Odd) : (-1:ℤˣ)^(C(p,2)*C(q,2)) = (-1:ℤˣ)^((p-1)/2*((q-1)/2))` —
  **VERIFIED**. `Nat.mul_mod` + the two `choose_two_mod_two` rewrites give the exponents are ≡ mod 2,
  then the units helper. **This is the entire elementary half of M2, now proven.**
- `sign_gridTranspose_eq_choose (p q) : sign (gridTranspose p q) = (-1)^(C(p,2)*C(q,2))` — **the ONE
  remaining sorry**. Primality-free; the genuinely-new combinatorial content (no upstream bearer, S18).
- `sign_gridTranspose (hp hq : Odd) : sign (gridTranspose p q) = (-1)^((p-1)/2*((q-1)/2))` —
  **VERIFIED assembly** of the two above.

**Net:** M2's open obligation is now a *single isolated, build-verified-context* lemma —
`sign_gridTranspose_eq_choose` — exactly the inversion count `inv(σ)=C(p,2)·C(q,2)` via
`signAux=∏finPairsLT` (S8). Everything around it (parity reduction + assembly) compiles. This is the
ideal self-contained Aristotle target the moment the backend stops 404'ing; until then it needs the
explicit `card_bij` (inversions ↔ {row-pairs i<i′} × {col-pairs j>j′}) — finicky but the cleanest count.
M1/headline unchanged (merged #24903). PR opened with `research` label.

### Session 2026-06-16 (S21, researcher-5) — FieldBridge build-pending file audited: every bearer pinned, repair points classified low-risk

**Mode:** CONTINUE → build-free bearer audit. **Dual blackout reconfirmed live this session**
(not assumed): `docker info` times out (>20s); Aristotle MCP `prove` returned `"Resource not
found"` on a trivial `n+0=n` ping. So no build, no Aristotle. Used the **full offline mathlib4
checkout at the exact pin** (`/Users/rwalters/GitHub/mathlib4` @ `2df2f0150c` / v4.26.0) for the
audit.

**State of the OQ (re-confirmed):** M1 + the units-form headline `legendreSym_eq_sign_mulLeft`
(merged #24903, on `(ZMod p)ˣ`) are done/verified/galleried. M2 file
`QuadraticReciprocityAlgorithmOQ03M2.lean` (merged #25053, UNREGISTERED) still carries its lone
sorry `sign_gridTranspose_eq_choose` (`sign σ = (-1)^(C(p,2)·C(q,2))`). The field-form completion
`QuadraticReciprocityAlgorithmOQ03FieldBridge.lean` (merged #25101, UNREGISTERED, 0 sorry/0 axiom)
was BUILD-PENDING/UNVERIFIED with three flagged-but-unconfirmed `rfl` repair points.

**This session's deliverable — FieldBridge converted from "UNVERIFIED, repair points unknown" to
"all bearers pinned & signature-checked, repair points classified low-risk" (same category as the
S11/S12 M1 audits).** Confirmed at the pin via the offline checkout (file:line + exact signature +
hypothesis direction):
- `sign_subtypePerm (f) (h₁ : ∀ x, p (f x) ↔ p x) (h₂ : ∀ x, f x ≠ x → p x) : sign (subtypePerm f h₁) = sign f` — `Sign.lean:453`. FieldBridge's `h₁ : ∀ x, mulLeft₀ a ha x ≠ 0 ↔ x ≠ 0` is exactly `∀ x, p (f x) ↔ p x` with `p = (· ≠ 0)`. ✓
- `sign_eq_sign_of_equiv (f) (g) (e) (h : ∀ x, e (f x) = g (e x)) : sign f = sign g` — `Sign.lean:467`. ✓
- `subtypePerm (f) (h : ∀ x, p (f x) ↔ p x)` — `Algebra/Group/End.lean:373` (NOT `∀ x, p x ↔ p (f x)` — direction matches FieldBridge). ✓
- `unitsEquivNeZero : G₀ˣ ≃ {a // a ≠ 0}`, `@[simps]`, `a ↦ ⟨↑a, a.ne_zero⟩` ⇒ `.val = ↑a` by rfl — `GroupWithZero/Units/Equiv.lean:27`. ✓
- `Equiv.mulLeft₀ a ha := (Units.mk0 a ha).mulLeft`, `@[simps! -fullyApplied]` (so the apply lemma exists for the `happ` fallback) — same file `:33`. ✓
- `Units.val_mk0 : (mk0 a h : G₀) = a` (rfl-level) — `GroupWithZero/Units/Basic.lean:173`. ✓
- parent `legendreSym_eq_sign_mulLeft (hp : 2 < p) (u : (ZMod p)ˣ)` — call `legendreSym_eq_sign_mulLeft hp u` is exact. ✓

**Risk classification of the 3 documented repair points:** all LOW. (1) `happ : mulLeft₀ a ha x = a * x := rfl` reduces through `(mk0 a ha).mulLeft x = ↑(mk0 a ha) * x` and `val_mk0` (rfl-level), fallback `simp [Equiv.mulLeft₀]`/`Equiv.mulLeft₀_apply` exists. (2)/(3) the `Subtype.ext`/`show` step in `hstep2` relies on `unitsEquivNeZero`'s `@[simps]` defeq and `subtypePerm`'s val reduction — both definitional, fallback `simp` documented in-file. **No dead names; no signature mismatches; no wrong-direction hypotheses.** Updated the FieldBridge header to record the audit (BUILD-PENDING → BUILD-PENDING, BEARERS AUDITED).

**M2 sorry — confirmed NOT blackout-safe to write, and why (re-audited this session).** Searched
the offline checkout for any public `sign = (-1)^(inversion count)` / `sign = (-1)^card` lemma for a
general (non-cycle) permutation: **none exists** — `Sign.lean` exposes only `signAux`/`signBijAux`/
`finPairsLT` machinery (private-ish) and the cycle-specific `IsCycle.sign`. The block-diagonal
family (`sign_prodCongrRight/Left` = `∏ sign`, `sign_sumCongr`) does NOT apply (S18: transpose is a
coordinate-swap, not block-diagonal). `finProdFinEquiv` packs `(i,j) ↦ j + q*i` (row-major; `i`
slow) — confirmed at `Logic/Equiv/Fin/Basic.lean:329`. So the only route is the `card_bij`
inversion count (inversions `↔ {i<i′} × {j>j′}`, card `C(p,2)·C(q,2)`) unfolded from `signAux` —
genuinely ~100+ LOC and intricate. Blind-writing it under blackout risks a non-compiling file
mislabeled as ACT (the standing prior-session prohibition). It remains the ideal single-lemma
**Aristotle** target the moment the backend stops 404'ing; until then it stays a sorry.

**Net:** FieldBridge is now build-ready with high confidence — the first Docker session can
`docker-build.sh Proofs.QuadraticReciprocityAlgorithmOQ03FieldBridge`, then register it (it lands
the exact OQ-pinned field-form statement `legendreSym p a.val = sign (mulLeft₀ a ha)`, completing
the Milestone-1 headline in the field form the OQ asks for). M2's lone sorry is unchanged and
correctly deferred to Aristotle/Docker. Problem stays **in-progress** (M2 open). No Lean proof
written this session (the only edit is the FieldBridge status header).
