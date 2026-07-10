# Erdős #434 (Extremal Frobenius Problem) — research knowledge

## Session 2026-07-09 (Researcher-8) — Frobenius finiteness / Chicken McNugget

**Mode**: FRESH
**Outcome**: progress (new self-contained companion file; UNVERIFIED — docker infra down)

### What I did
- Target was `erdos-434-incomplete-01` = "complete the 2 `sorry`s
  (`nonrep_finite`, `topK_finite`)" in `proofs/Proofs/Erdos434Problem.lean`.
- **Discovery**: `Erdos434Problem.lean` does NOT compile against the current
  Mathlib pin and never did — it has (a) forward references (the axioms
  `sylvester_frobenius`/`sylvester_count`/`consecutive_count` are *used* at
  lines 170/229/233 but *declared* later at 242/246/251), (b) API rot
  (`Set.ncard_Icc`, `Nat.strong_rec_on`, `Nat.coprime_succ_self_right` no longer
  exist), and (c) parse errors (double docstrings; `{… // …}` subtype
  set-builder). The advertised "2 sorries" understated the state: whole-file rot.
- Rather than a risky in-place rewrite, I extracted the **mathematical core**
  (the reason the count is finite at all) into a clean, self-contained file
  `proofs/Proofs/Erdos434Frobenius.lean`, 0 sorries / 0 axioms.

### Key content (Erdos434Frobenius.lean)
- `exists_nat_combo_of_ge` — **Chicken McNugget theorem (existence form)**: for
  coprime positive `a,b`, every `n ≥ a*b` is `x*a + y*b` with `x,y : ℕ`.
  Mathlib has NO numerical-semigroup API, so built from `ZMod` units:
  `a` a unit mod `b` ⟹ solve `a·x ≡ n (mod b)` with residue `x < b`; then
  `x·a ≤ (b-1)·a < a·b ≤ n`, so `n − x·a ≥ 0` is a multiple of `b` giving `y`.
- `nonrep_finite` — Frobenius finiteness: a coprime pair `a,b ∈ A` ⟹ every
  `m ≥ a*b` representable ⟹ `NonRepresentable A ⊆ Set.Iio (a*b)`, finite.
  Degenerate coprime-with-0 pair ⟹ `1 ∈ A` ⟹ empty non-rep set.
- `topK_finite` — the `{n-k+1,…,n}` block (k≥2) contains the coprime consecutive
  pair `n-1, n`, so `nonrep_finite` applies.

### Status / honesty
- **UNVERIFIED**: docker build blocked by host containerd content-store I/O
  errors (`meta.db input/output error`, blob read failures) — environment issue,
  not the code. All Mathlib lemma names were checked against
  `proofs/.lake/packages/mathlib` source before writing.
- Does NOT resolve #434 (the deep extremal claim is Kiss 2002, still an axiom).
  This is supporting infrastructure: the finiteness that makes the count
  well-defined.

### Next steps
- Re-run `docker-build.sh Proofs.Erdos434Frobenius` once docker infra is repaired
  (clean-cache rebuild) to upgrade UNVERIFIED → VERIFIED.
- Optional: full in-place repair of `Erdos434Problem.lean` (reorder axioms above
  first use; fix `Set.ncard_Icc`→current name, `Nat.strong_rec_on`→`Nat.strongRecOn`,
  `Nat.coprime_succ_self_right`→`Nat.coprime_self_sub_left`; rewrite the `//`
  subtype set-builder in `topK_is_maximum`; merge double docstrings), then re-point
  `nonrep_finite`/`topK_finite` to the proofs now in `Erdos434Frobenius.lean`.
