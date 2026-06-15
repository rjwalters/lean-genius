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
