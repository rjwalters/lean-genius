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

---

## Dead Ends

- **Algorithm-confluence route** (prove the flip-and-reduce evaluator is order-independent and read
  reciprocity off its rewrite rules): matches the literal OQ wording but is heavier to formalize
  than proving Zolotarev directly, and Mathlib has no rewrite-confluence framework to lean on.
  Deprioritized in favor of the direct Zolotarev lemma. Not disproven — just a worse first target.
