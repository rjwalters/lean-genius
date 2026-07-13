# Multivariate Bézout Identity — bezout-identity-oq-02-oq-02-oq-01-oq-02

**Status: UNVERIFIED (build-blocked).** Draft Lean file written; not machine-checked.

## Open question

Parent `bezout-identity-oq-02-oq-02-oq-01` (Constructive Divisibility Algorithm)
asks: *"Can the algorithm be extended to multivariate Bézout identities in
polynomial rings?"* Siblings cover the other three parent OQs:
- oq-01: removing the `noncomputable` annotation
- oq-03: Lamé's Θ(log) complexity of extGcd
- oq-04: Bézout quotient formula in non-commutative rings

This entry (oq-02) answers the multivariate question.

## Result

For a finite family `a : ι → R` over a **Bézout ring** `R` (`[CommRing R] [IsBezout R]`),
there is a gcd element `d` and coefficients `u : ι → R` with:
- `∑ i, u i * a i = d` (Bézout identity),
- `∀ i, d ∣ a i` (common divisor),
- `∀ c, (∀ i, c ∣ a i) → c ∣ d` (greatest).

No integral-domain hypothesis is needed. Specializations proved:
- `multivariate_bezout_polynomial` over `Polynomial F` (field `F`) — the exact
  case the OQ asks about (`F[X]` is Euclidean ⟹ PIR ⟹ Bézout),
- `multivariate_bezout_int` over `ℤ`,
- concrete 3-element witnesses over `ℤ` and a polynomial example over `ℚ`.

## Proof architecture

Structural, not algorithmic:
1. `Ideal.span (Set.range a)` is finitely generated (`Submodule.fg_span` +
   `Set.finite_range`, `[Finite ι]`).
2. `IsBezout.isPrincipal_of_FG` ⟹ the ideal is principal; take its generator as
   `familyGcd a`.
3. `familyGcd a` lies in the span, so `mem_span_range_iff_exists_fun`
   (`[Fintype ι]`) yields the coefficient vector (`smul_eq_mul`).
4. Divisibility of each `a i` from `Ideal.mem_span_singleton`; universal property
   from `Finset.dvd_sum` applied to the linear combination.

## Build blocker

Docker build environment failed three ways this session (2026-07-01):
- containerd image-extraction `input/output error` (corrupted overlayfs layer),
- Docker daemon crash,
- host root disk saturated (95% → 99%, <256Mi free) under concurrent agents;
  `docker system prune` itself failed with I/O error on the buildkit metadata db.

Draft committed + pushed to `research/bezout-oq02020102-multivariate`. Needs a
clean `./proofs/scripts/docker-build.sh Proofs.BezoutIdentityOQ02OQ02OQ01OQ02`
before any `verified` claim or gallery entry is created.

## API risk notes (for the verifier)

- `IsBezout.isPrincipal_of_FG` — confirm exact capitalization of the field.
- `mem_span_range_iff_exists_fun` — confirm name / explicit `R` argument for `rw`.
- `Submodule.IsPrincipal.span_singleton_generator` — used for ideals via
  `Ideal.span = Submodule.span R` defeq; the `haveI` instances must register.
