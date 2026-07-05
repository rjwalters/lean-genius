# Knowledge Base: cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-02-oq-05

Multi-block rational canonical form (RCF) via the K[X]-module structure theorem.

---

## Problem Understanding

**Goal.** For any field `K` and `A ∈ Mₙ(K)`, prove `A` is similar to a direct sum of
companion matrices of its invariant factors `p₁ ∣ p₂ ∣ … ∣ p_r` (the rational canonical
form). The single-block (nonderogatory) case is fully proved in the gallery scaffold
`cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-02` (688 lines, 0 sorries, 0 axioms).

**Honest scope verdict (this session).** Full multi-block RCF is a **Mathlib-PR-scale**
contribution (>1000 lines): Mathlib has the abstract PID structure theorem but has **no
companion matrix, no companion↔module bridge, and no RCF**. Delivering the whole thing in
one build-enabled session is not realistic. The right research move is to isolate the
**first genuinely self-contained increment** that (a) reuses the existing scaffold as a
black box and (b) is buildable at ~400–600 lines. This session identifies that increment
precisely, grounds every API reference, and hands the next session a lemma dependency
chain. (Build tooling — Docker + Aristotle — is in a blackout, so no new Lean was
compiled; deliverable is the ORIENT design + statement skeleton.)

---

## Mathlib API Map (verified against /Users/rwalters/GitHub/mathlib4, v4.26-era)

| Need | Mathlib provides? | Symbol |
|------|-------------------|--------|
| PID structure theorem (prime-power form) | ✅ | `Module.equiv_directSum_of_isTorsion` (`Mathlib/Algebra/Module/PID.lean:233`) |
| PID structure theorem (free × torsion) | ✅ | `Module.equiv_free_prod_directSum` (`…/PID.lean:259`) |
| K[X]-module structure via an endomorphism | ✅ | `Module.AEval'` (`Mathlib/Algebra/Polynomial/Module/AEval.lean`) |
| minpoly = annihilator generator of `AEval'` | ✅ | `Mathlib/LinearAlgebra/AnnihilatingPolynomial.lean:167` |
| block-diagonal is a ring hom (⇒ `aeval` distributes) | ✅ | `Matrix.blockDiagonalRingHom`, `Matrix.blockDiagonal_pow` (`Mathlib/Data/Matrix/Block.lean:435,445`) |
| block-triangular charpoly = ∏ block charpolys | ✅ | `Matrix.BlockTriangular.charpoly`, `charpoly_fromBlocks_zero₁₂/₂₁` (`…/Charpoly/Basic.lean:179–199`) |
| `minpoly ∣ charpoly` | ✅ | `Matrix.minpoly_dvd_charpoly` (`…/Charpoly/Minpoly.lean:47`) |
| **companion matrix** | ❌ | *gallery-local* `companionMx` only (Mathlib has none — all "companion" hits are `QuadraticForm.exists_companion`) |
| **companion charpoly = p** | ❌ | not in Mathlib, not yet in gallery |
| **minpoly of a block-diagonal matrix = lcm** | ❌ | not in Mathlib |
| **RCF / block-companion similarity** | ❌ | not in Mathlib |

**Reusable scaffold lemmas** (from `CayleyHamiltonCyclicVectorAllFieldsOQ01OQ02.lean`,
namespace `CayleyHamiltonCyclicVectorAllFieldsOQ01OQ02`, `open GeneralCyclicVector`):

- `minpoly_companionMx_eq (p) (hp_monic) (hp_deg : p.natDegree = n) (hn) : minpoly K (companionMx p) = p`  (L:635)
- `nonderogatory_iff_similar_to_companion (M) (hn) : IsNonderogatory M ↔ ∃ P, IsUnit P ∧ P⁻¹*M*P = companionMx (minpoly K M)`  (L:395)
- `aeval_companionMx_p_eq_zero`  (L:581)

---

## The First Increment: CRT / elementary-divisor block-merge

**Theorem (block-merge, coprime case).** For monic `p, q ∈ K[X]` with `IsCoprime p q`
(and positive degrees), the block matrix
`D = fromBlocks (companionMx p) 0 0 (companionMx q)` (over `Fin dₚ ⊕ Fin d_q`) is
similar — after the reindexing `finSumFinEquiv : Fin dₚ ⊕ Fin d_q ≃ Fin (dₚ+d_q)` — to
`companionMx (p*q)`. This is the Chinese-Remainder step
`K[X]/(pq) ≅ K[X]/(p) ⊕ K[X]/(q)` realized at the matrix level, i.e. the bridge between
the **elementary-divisor** form (coprime prime-power blocks) and the **invariant-factor**
form (single companion block). It is the mathematical heart of "multi-block."

**Why this is the right first target.** It is the smallest theorem that (i) is genuinely
about *more than one block*, (ii) reuses the entire single-block scaffold as a black box,
and (iii) produces upstream-worthy lemmas (companion charpoly, block-diagonal minpoly)
that every later RCF step also needs.

### Proof strategy (reduces the merge to nonderogatory-ness via the scaffold)

`nonderogatory_iff_similar_to_companion` already gives: any nonderogatory `M` is similar
to `companionMx (minpoly K M)`. So it suffices to prove **`D` is nonderogatory with
`minpoly K D = p*q`**; then `D ~ companionMx (p*q)` follows immediately. Chain:

1. **L2 `charpoly_companionMx` : `(companionMx p).charpoly = p`** (monic `p`, deg `n`).
   *Not in Mathlib.* Classical companion charpoly. Buildable independently (~120 lines)
   via cofactor expansion, or bootstrapped from `minpoly_companionMx_eq` + the fact that
   a nonderogatory matrix has `charpoly = minpoly` (companion is cyclic at `e₀`).

2. **L3 `charpoly_fromBlocks` : `(fromBlocks A 0 0 B).charpoly = A.charpoly * B.charpoly`.**
   Direct from `Matrix.charpoly_fromBlocks_zero₂₁` (already in Mathlib). ⇒
   `D.charpoly = p*q` using L2. (~30 lines.)

3. **L1 `minpoly_fromBlocks = lcm` : `minpoly K (fromBlocks A 0 0 B) = lcm (minpoly K A) (minpoly K B)`.**
   *The lynchpin, not in Mathlib.* Argument: `f` annihilates `fromBlocks A 0 0 B` ⟺ `f`
   annihilates `A` and `f` annihilates `B`, because `aeval` distributes over the block
   ring hom (`fromBlocks` is block-multiplicative:
   `(fromBlocks A 0 0 B)^k = fromBlocks (A^k) 0 0 (B^k)`, so
   `aeval (fromBlocks A 0 0 B) f = fromBlocks (aeval A f) 0 0 (aeval B f)`). Hence the
   annihilator ideal of the block matrix is `(minpoly A) ⊓ (minpoly B)` in the PID `K[X]`,
   whose monic generator is `lcm`. Use `minpoly.dvd` for both directions plus the PID
   ideal-intersection = lcm fact and `Polynomial`'s `GCDMonoid`. (~150–200 lines; the real
   work of the increment.)

4. **L5 coprime monic ⇒ `lcm p q = p*q`.** `IsCoprime p q` ⇒ `gcd p q` is a unit ⇒
   `lcm = normalize (p*q) = p*q` (both monic ⇒ `normalize` fixes it). Mathlib
   `GCDMonoid`/`normalize_eq_self` for monic polynomials. (~30 lines.)

5. **Assemble.** `minpoly K D = lcm p q = p*q` (L1+L5). `D.charpoly = p*q` (L2+L3). Over a
   field, `minpoly D = charpoly D` ⇒ `D` nonderogatory (Cayley–Hamilton gives
   `minpoly ∣ charpoly` always; equality of the two monic polys of equal degree ⇒ the
   scaffold's degree criterion for `IsNonderogatory`). Then
   `nonderogatory_iff_similar_to_companion` + `minpoly K D = p*q` ⇒
   `D ~ companionMx (p*q)`. (~60 lines + reindex bookkeeping.)

**Buildability estimate:** ~400–600 lines total. Decision: **BUILD (high value)** in a
future build-enabled session — the lemmas L1, L2 are independently upstream-worthy and are
prerequisites for *any* RCF route.

### The r-block generalization (after the coprime merge)

- **Elementary → invariant divisors:** iterate the coprime merge across distinct prime
  factors; group prime powers with the same prime into a single companion via repeated
  L1/L3. Standard, but heavy index bookkeeping.
- **Existence of the decomposition:** apply `Module.equiv_directSum_of_isTorsion` to
  `Module.AEval' (Matrix.toLin' A)` (finite + torsion since `Kⁿ` is finite-dimensional and
  `minpoly` annihilates), giving `⨁ K[X]/(pᵢ^{eᵢ})`; each summand is `A`-cyclic ⇒ companion
  block via the scaffold; assemble block-diagonal + change of basis
  (`LinearMap.toMatrix` / `Matrix.reindex`). This is the >1000-line remainder — deferred.

---

## Insights

- Mathlib has the *abstract* PID cyclic decomposition but **nothing connecting it to
  companion matrices**; the entire matrix ↔ module bridge (companion charpoly/minpoly,
  block minpoly = lcm, block-companion similarity) is a green field. This is why RCF is a
  standing Mathlib gap despite the structure theorem being present.
- The single-block scaffold is *more reusable than it looks*: because
  `nonderogatory_iff_similar_to_companion` turns "similar to a companion" into the purely
  local property "nonderogatory," the multi-block coprime merge collapses to a
  minpoly/charpoly *computation* (`minpoly D = charpoly D = p*q`) rather than an explicit
  change-of-basis construction. The change of basis is supplied by the scaffold.
- The CRT/elementary-divisor merge is the correct decomposition point: it is the minimal
  multi-block statement, and its two novel lemmas (companion charpoly, block minpoly=lcm)
  are on the critical path of every subsequent RCF step.
- `fromBlocks` (not `blockDiagonal`) is the correct constructor for two companion blocks:
  the blocks have *different* sizes `Fin dₚ`, `Fin d_q`, which `blockDiagonal` forbids;
  `fromBlocks` lives over `Fin dₚ ⊕ Fin d_q`, and `charpoly_fromBlocks_zero₂₁` already
  handles its charpoly.

## Dead Ends / Cautions

- **Smith normal form route (problem.md Approach B):** Mathlib's Smith-normal-form support
  over `K[X]` is thin; extracting invariant factors of `XI − A` constructively is likely a
  larger gap than the module-transport route. Not recommended as the entry point.
- Do **not** start with the full abstract module-transport for general RCF — the reindex /
  block-basis assembly bookkeeping dominates and yields no reusable sub-lemmas until the
  very end. Start with the coprime merge, which produces upstream lemmas immediately.

## Next Steps

1. (Build-enabled) Implement **L2 `charpoly_companionMx`** — companion charpoly = p.
   Self-contained; upstream-worthy on its own.
2. Implement **L1 `minpoly_fromBlocks = lcm`** via block-multiplicativity of `aeval` +
   PID annihilator-ideal = `⊓` = `lcm`. The lynchpin.
3. Assemble **L3 charpoly_fromBlocks**, **L5 coprime⇒lcm=product**, and the merge theorem
   `companion_blockmerge_coprime` using `nonderogatory_iff_similar_to_companion`.
4. Only then tackle the r-block invariant-factor assembly + `Module.equiv_directSum_of_isTorsion`
   transport for full RCF.

See `lean/OQ01OQ02OQ05-skeleton.lean` for the statement skeleton (WIP, not build-verified).

---

## Session Log

### Session 2026-07-04 (Session 1) — ORIENT: API map + first-increment decomposition

**Mode**: FRESH · **Outcome**: scouted/oriented (no Lean compiled — Docker+Aristotle blackout)

**What I did**
- Read the 688-line single-block scaffold; extracted the two reusable public lemmas
  (`minpoly_companionMx_eq`, `nonderogatory_iff_similar_to_companion`).
- Grounded the full Mathlib API surface against a local mathlib4 checkout (table above);
  confirmed Mathlib has the PID structure theorem + `AEval'` but **no companion matrix and
  no RCF**.
- Identified the CRT/elementary-divisor **coprime block-merge** as the correct first
  increment and wrote a 5-step proof plan (L1–L5) with buildability estimates.

**Key findings**
- The scaffold's `nonderogatory_iff_similar_to_companion` collapses the coprime merge to a
  minpoly=charpoly computation — no explicit change-of-basis needed at this stage.
- Lynchpin lemma is L1 (`minpoly_fromBlocks = lcm`), provable via block-multiplicativity of
  `aeval` (`fromBlocks A 0 0 B`'s powers are block-diagonal) + PID annihilator ideal = `⊓`.
- `fromBlocks` (over `⊕`), not `blockDiagonal`, is required (unequal block sizes).

**Files modified**: this `knowledge.md`, `state.md`, `src/data/research/problems/…json`,
`lean/OQ01OQ02OQ05-skeleton.lean` (WIP draft).

**Next steps**: implement L2 then L1 (see Next Steps above) once build tooling recovers.
