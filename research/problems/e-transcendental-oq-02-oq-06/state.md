# Research State: e-transcendental-oq-02-oq-06

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-04T12:34:40-07:00
**Iteration**: 2

## Current Focus
Package the contrapositive `x ∈ ℚ ⇒ ¬ IsNormalInBase b x` as a reusable
standalone lemma, per the open-question goal.

## Key Finding
The positive implication `normal_imp_irrational : IsNormalInBase b x → Irrational x`
is **already a fully machine-checked theorem** in the parent file
`ETranscendentalOQ02.lean` (line 663) — it is NOT an axiom. The only remaining
`axiom` in the parent is `e_absolutely_normal` (the genuinely open conjecture that
`e` is normal, which cannot be discharged). So the axiom-discharge framing in
`problem.md` was already satisfied by the parent; the productive increment is to
expose the explicitly-requested contrapositive form.

## Active Approach
Companion file `ETranscendentalOQ02OQ06.lean` deriving, from `normal_imp_irrational`
and Mathlib's `Rat.not_irrational` / `Int.not_irrational` / `Nat.not_irrational`:
- `rational_not_normal` : `¬ IsNormalInBase b (q : ℝ)` (the requested contrapositive)
- `intCast_not_normal`, `natCast_not_normal` : integer / natural specializations
- `normal_ne_ratCast` : a normal number differs from every rational
- `rational_not_absolutely_normal` : `¬ IsAbsolutelyNormal (q : ℝ)`

All are term-mode corollaries introducing no new assumptions.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
Docker build infrastructure DOWN this session (containerd `meta.db` / content-blob
input/output errors at the image-build step; host disk healthy, ~120 GiB free).
Verification not possible — shipped UNVERIFIED. Proofs are one-line corollaries of
an already-verified theorem using confirmed-present Mathlib API, so confidence is high.

## Next Action
Re-run `./proofs/scripts/docker-build.sh Proofs.ETranscendentalOQ02OQ06` once docker
infra is restored; then consider a concrete instance (e.g. an explicit non-normal
rational such as `1/3` in base 10).
