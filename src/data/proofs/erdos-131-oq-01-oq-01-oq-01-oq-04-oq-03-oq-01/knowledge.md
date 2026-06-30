# Erdős #131 — Homogeneous-Power Davenport Lower Bound `D(Gⁿ) ≥ n·(D(G) − 1) + 1`

**Slug:** `erdos-131-oq-01-oq-01-oq-01-oq-04-oq-03-oq-01`
**Lean file:** `proofs/Proofs/Erdos131DavenportPower.lean` (namespace `Erdos131DavenportPower`)
**Status:** verified · 0 axioms · 0 sorries · 7 theorems · 3 definitions · 210 lines

## Summary

The **Davenport constant** `D(G)` of an additive group `G` is the least `d` such that
every length-`d` sequence over `G` has a nonempty zero-sum subsequence. The cyclic value
`D(ℤ/nℤ) = n` is elementary (companion `erdos-131-oq-01-oq-01-oq-01-oq-03`); the binary
direct-sum lower bound `D(G₁ ⊕ G₂) ≥ D(G₁) + D(G₂) − 1` (companion
`erdos-131-oq-01-oq-01-oq-01-oq-04-oq-03`) proves the structural concatenation principle
behind it.

This entry proves the **homogeneous-power** lower bound for the `n`-fold direct power
`Gⁿ = (Fin n → G)`:

> `davenport_pow_lower : IsLeast (DavenportSet G) d → IsLeast (DavenportSet (Fin n → G)) dₙ → n·(d − 1) + 1 ≤ dₙ`.

It is the homogeneous case of the iterated Olson–Davenport lower bound, and it directly
advances the open question `oq-04-oq-03-oq-01` of the binary companion (lifting the binary
concatenation to a k-fold direct sum). The key design choice: it is proved in **one shot**
with a single explicit extremal construction, so it needs only `IsLeast` for `G` and for
`Gⁿ` — **not** the per-stage `IsLeast` for every intermediate power `Gᵏ` that an induction
on the binary bound would require (which in turn would need a separate finiteness argument).

Specializing `D(ℤ/pℤ) = p` gives `D((ℤ/pℤ)ⁿ) ≥ n·(p − 1) + 1`, the **lower-bound half of
Olson's theorem** for elementary abelian `p`-groups (equality holds; the matching upper
bound — Olson's Chevalley–Warning argument — is not formalized).

## The engine: power-concatenation principle

`powerseq_not_hasZeroSum`: if `f : Fin ℓ → G` is zero-sum-free, then so is
`powerSeq n f : Fin (n·ℓ) → (Fin n → G)`, where

    powerSeq n f x = Pi.single (finProdFinEquiv.symm x).1 (f (finProdFinEquiv.symm x).2)

i.e. the index `x` is decoded as `(i, k) : Fin n × Fin ℓ` and mapped to the vector with
`f k` in coordinate `i` and `0` elsewhere.

Proof outline:
1. Reindex a candidate zero-sum set `s ⊆ Fin (n·ℓ)` along `finProdFinEquiv` to
   `t ⊆ Fin n × Fin ℓ`; the total becomes `∑_{(i,k) ∈ t} Pi.single i (f k) = 0`.
2. Read off coordinate `j` (`congrFun` + `Finset.sum_apply` + `Pi.single_apply`): the
   `j`-th coordinate keeps only terms with `i = j`, giving (after `Finset.sum_filter`)
   `∑_{x ∈ t.filter (j = ·.1)} f x.2 = 0` for every `j`.
3. The slice maps injectively under `Prod.snd` (first coordinate fixed `= j`), so
   `Finset.sum_image` turns the slice sum into `∑_{k ∈ K} f k = 0` over a genuine
   `K : Finset (Fin ℓ)`; zero-sum-freeness of `f` forces `K = ∅`, hence the slice empty.
4. Every slice empty ⟹ `t = ∅` ⟹ `s = ∅`, contradicting nonemptiness.

`davenport_pow_lower` then takes `f` of length `D(G) − 1` (exists since `D(G)` is least),
notes `powerSeq n f` is a zero-sum-free sequence of length `n·(D(G) − 1)` over `Gⁿ`, so
that length is not a Davenport length; upward closure (`davenport_set_mono`) forces
`dₙ ≥ n·(D(G) − 1) + 1`.

## Corollaries

- `davenport_elementary_abelian_lower`: `D((ℤ/pℤ)ⁿ) ≥ n·(p − 1) + 1` (sharp; Olson).
- `davenport_pow_two_lower`: `D(G²) ≥ 2·D(G) − 1` (matches the binary diagonal case).

## Session log

### Session 2026-06-21 (s01) — FRESH-style follow-up (pool empty → REVISIT)

**Mode:** REVISIT (candidate pool has no `available` status). Chosen as a depth follow-up
to my merged binary direct-sum entry (`oq-04-oq-03`, PR #27295), answering its open
question `oq-04-oq-03-oq-01` for the homogeneous case.

**What I did**
- Wrote `Erdos131DavenportPower.lean` from scratch (self-contained, `import Mathlib`),
  reproducing the three small `DavenportSet` helpers from the binary companion.
- New construction `powerSeq` + new engine lemma `powerseq_not_hasZeroSum` using a
  product reindexing (`finProdFinEquiv`) and coordinatewise slice analysis
  (`Pi.single_apply`, `Finset.sum_apply`, `Finset.sum_filter`, `Finset.sum_image`).
- Built clean via docker wrapper; verified `#print axioms` shows only
  `propext, Classical.choice, Quot.sound` for both headline theorems (0-axiom).

**Key findings / gotchas**
- `simp only [Equiv.coe_toEmbedding, powerSeq, Equiv.symm_apply_apply]` cleanly unfolds the
  reindexed summand to `Pi.single x.1 (f x.2)` (def `powerSeq` unfolds under `simp only`).
- `Finset.sum_image` wants the `∀ a ∈ s, ∀ b ∈ s, g a = g b → a = b` membership form (not
  `Set.InjOn`); injectivity of `Prod.snd` on the slice comes from the fixed first coord.
- v4.26.0 deprecations: use `Finset.eq_empty_iff_forall_notMem` and `Finset.notMem_empty`.

**Outcome:** completed — shipped verified 0-axiom entry.

**Next steps**
- The fully general indexed direct sum `⨁_{i:Fin k} Gᵢ` (distinct factors) via a Σ-type
  index `Σ i, Fin (ℓ i)` and dependent `Pi.single` over `finSigmaFinEquiv` — does the
  one-shot argument lift? (open question `…-oq-01-oq-01`).
- Upper half for elementary abelian groups via Mathlib's Chevalley–Warning
  (open question `…-oq-01-oq-02`).
