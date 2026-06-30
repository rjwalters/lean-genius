# elementary-quadratic-reciprocity-oq-01-oq-01-oq-01-oq-01

**Question**: Can the Frobenius step τ^q ≡ (p/q)·τ (mod q) be formalized?

**Resolution: ALREADY FORMALIZED (duplicate candidate).**

## Summary

This candidate was seeker-selected on 2026-06-15 as the next step of the
Gauss-sum proof of Quadratic Reciprocity. The direct parent
`ElementaryQuadraticReciprocityOQ01OQ01OQ01.lean` proves Step 2
(τ² = χ(-1)·p) and lists "Step 3: τ^q ≡ (p/q)·τ (mod q) [Frobenius step]" as
future work. That Step 3 is the question posed here.

A survey of adjacent gallery files shows **Step 3 is already formalized and
verified on `main`**. The candidate is a duplicate of existing work; its own
pool note even cites the answer location, "(OQ-01-OQ-01-OQ-02)".

## Where the Frobenius step is proved

- `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ01OQ02.lean`
  (slug `elementary-quadratic-reciprocity-oq-01-oq-01-oq-02`,
  meta status `verified`, badge `mathlib`, 0 sorry / 0 axiom,
  registered at `proofs/Proofs.lean:681`):
  - `frobenius_step` — τ^q = χ(q)·τ in a field `F` of characteristic `q`,
    via the freshman's-dream Frobenius endomorphism and Mathlib's
    `gaussSum_frob`.
  - `qr_via_frobenius`, `qr_gauss_sums_identity`, `gauss_qr_pathway_complete`.

- `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ01OQ01OQ02.lean`
  (slug `elementary-quadratic-reciprocity-oq-01-oq-01-oq-01-oq-02`,
  `verified`/`mathlib`, registered at `proofs/Proofs.lean:680`) re-exposes it as
  `step3_frobenius {F : Type*} [Field F] [Fintype F] [CharP F q] ...` inside the
  complete four-step assembly `gauss_sum_qr_assembled`.

## Key technical point (why it is not a trivial restatement of Step 2)

Step 2 (τ² = χ(-1)·p) was proved in ℂ. The Frobenius step **cannot** live in ℂ:
it requires a ground ring of characteristic `q` so that `(Σ xₐ)^q = Σ xₐ^q`
(freshman's dream) holds. The existing formalization correctly works in a finite
field `F` with `[CharP F q]`, matching Mathlib's `gaussSum_frob` /
`Char.card_pow_card` infrastructure. This domain shift (ℂ → char-`q` field) is
the only real content beyond invoking Mathlib, and it is handled.

## Disposition

- Registry (`research/registry.json`): `active`/`NEW` → `graduated`/`COMPLETED`.
- Runtime pool (`.lean/state/candidate-pool.json`): → `completed`.
- No Lean changes: the mathematics is already verified on `main`.

## Session note (2026-06-16, researcher-11)

Conducted under a dual-backend blackout (Docker daemon hung — `docker version`
server query times out; Aristotle `prove_file` erroring), so no build/proof-search
was possible. This disposition required neither backend. The two top MODERATE
available candidates were both ACT-blocked by the blackout:
- `cayley-hamilton-cyclic-vector-all-fields-oq-03`: operator half complete
  (0/0, registered `Proofs.lean:442`), badge `wip` pending a green build (no
  green-build evidence exists — both prior build logs contain only headers);
  PID-module half is a documented >500-line gap. Not flippable without Docker.
- `brouwer-fixed-point-oq-01-oq-03-oq-01`: sole frontier (Gap 1 slice-volume
  continuity) is an Aristotle `prove_file` target — Aristotle down.
