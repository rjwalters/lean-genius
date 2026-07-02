# Knowledge: fourth-root-2-irrational-oq-03

## Summary

The problem as originally framed (degree `[ℚ(⁴√2, i) : ℚ] = 8`) is **already fully
proven** in the gallery: the sibling entry `fourth-root-2-irrational-oq-01`
(`proofs/Proofs/FourthRoot2GaloisClosure.lean`, verified, 0-axiom) builds the tower
`ℚ ⊂ ℚ(⁴√2) ⊂ ℚ(⁴√2, i)` and proves `finrank_galois_closure : Module.finrank ℚ
ℚ⟮a, Complex.I⟯ = 8`, together with the crux `I_not_mem_adjoin_a` (`i ∉ ℚ(⁴√2)`)
and `roots_mem_closure` (all four roots `±⁴√2, ±i·⁴√2` lie in the closure).

The genuine open increment is the piece that `FourthRoot2GaloisClosure.lean`
**explicitly defers** in its own docstring:

> "The full identification of the Galois group with D₄ (constructing the 8
> automorphisms and the group isomorphism) is left for a follow-up; here we
> secure the degree and the tower."

This session supplies the quantitative foundation of that deferred step: that
`ℚ(⁴√2, i) / ℚ` is a **Galois** extension and that its automorphism group has
**order exactly 8**.

## Sessions

## Session 2026-07-02 (Session 1) — Galois property and |Gal| = 8

**Mode**: FRESH
**Outcome**: proof complete (written, 0-sorry / 0-axiom); build BLOCKED by
environment disk exhaustion — needs CI verification.

### What I Did
- Screened the seeker candidate pool: the top of the "available" pool is heavily
  **stale** — ~24/57 available candidates already have an exact-name solved Lean
  file, and spot-checks of many "no-file" candidates (composition-card-2pow,
  hermite-floor-identity-oq-03, derangements Poisson limit, combinations log-
  concavity, cauchy-interlacing codim-m, pascals-hexagon sylvester) found their
  targets already proven in differently-named sibling files. See the session
  finding below.
- Identified the one genuine, significant (sig 7) open increment: the Galois
  group structure deferred by `FourthRoot2GaloisClosure.lean`.
- Wrote `proofs/Proofs/FourthRoot2GaloisClosureOQ03.lean`
  (`namespace FourthRoot2GaloisClosureOQ03`), building on the parent:
  * `p := X⁴ − 2`; `p_irreducible` (`= minpoly ℚ (⁴√2)`), `p_separable`
    (char-zero irreducible);
  * `adjoin_rootSet_eq : adjoin ℚ ((X⁴−2).rootSet ℂ) = ℚ⟮a, Complex.I⟯`
    — the fourth-roots-of-unity classification `z⁴ = 2 ⟹ z ∈ {±a, ±ia}` via the
    factorisation `z⁴ − a⁴ = (z−a)(z+a)(z−ia)(z+ia)` (uses `i² = −1`);
  * `isSplittingField : (X⁴−2).IsSplittingField ℚ ℚ⟮a, Complex.I⟯` (splits over ℂ
    by `IsAlgClosed.splits_codomain`, generation by `adjoin_rootSet_eq`);
  * `isGalois : IsGalois ℚ ℚ⟮a, Complex.I⟯` via
    `IsGalois.of_separable_splitting_field`;
  * `normal : Normal ℚ ℚ⟮a, Complex.I⟯`;
  * `card_gal : Fintype.card (ℚ⟮a, Complex.I⟯ ≃ₐ[ℚ] ℚ⟮a, Complex.I⟯) = 8` via
    `IsGalois.card_aut_eq_finrank` + the parent's `finrank_galois_closure`.

### Key Findings
- All Mathlib API used was grep-confirmed against the pinned Mathlib source:
  `IntermediateField.adjoin_rootSet_isSplittingField` (needs
  `(p.map (algebraMap K L)).Splits`, the single-argument `Polynomial.Splits`);
  `IsAlgClosed.splits_codomain`; `Irreducible.separable [CharZero]`;
  `IsGalois.of_separable_splitting_field`; `IsGalois.card_aut_eq_finrank`.
- The proof is 0-sorry / 0-axiom by construction and reuses only Mathlib + the
  parent file.

### Build blocker (why not verified locally)
- Host disk sat at 89–96% for the whole session (≈0.5–1.5 GiB free), actively
  shrinking under concurrent agents.
- `docker-build.sh` failed: the Mathlib `.ltar` cache could not decompress
  ("No space left on device", leantar error 101 on 7727 files).
- Host `lake env lean` fallback also failed: the cached Mathlib olean tree is
  **incomplete** (top-level `Mathlib.olean` present, but individual module oleans
  such as `Mathlib/Algebra/Ring/Subsemiring/MulOpposite.olean` are missing), so
  `import Mathlib` cannot resolve without rebuilding Mathlib (forbidden/impossible
  on the available disk).

### Next Steps
- Have CI / the deployer / a mechanic build `Proofs.FourthRoot2GaloisClosureOQ03`
  when disk is healthy; if it compiles clean, promote to a verified gallery entry
  (meta.json, annotations) as a child of `fourth-root-2-irrational`.
- Downstream open question (new): identify `Gal(ℚ(⁴√2, i)/ℚ) ≅ D₄` explicitly
  (construct the 8 automorphisms / the group isomorphism). Note the abstract
  `Gal(X⁴−2) ≅ D₄` is already handled in the `inverse-galois-d4` entry via a
  Sylow-2 argument; the remaining work is the concrete identification for THIS
  ℂ-model field `ℚ⟮√√2, i⟯`.

### Session finding: seeker candidate pool is saturated
Every top-of-pool candidate examined this session was already solved somewhere in
the gallery (often in the parent or a differently-named sibling file). The pool's
"available" status is stale relative to shipped work. Recommend the seeker re-sync
`available` statuses against `src/data/proofs/*/meta.json` and existing
`proofs/Proofs/*.lean` before proposing further children in saturated topics.
