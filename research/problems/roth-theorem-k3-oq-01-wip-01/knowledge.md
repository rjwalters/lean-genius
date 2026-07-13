# Knowledge Base: roth-theorem-k3-oq-01-wip-01

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session 2026-07-04 (Session 1) - Supermultiplicativity of r₃ (CRT)

**Mode**: FRESH
**Outcome**: progress (new 0-axiom structural theorem)

### What I Did
- Assessed the 4 Part III sorries in `RothTheoremQuantitative.lean` (Roth 1953,
  Behrend 1946, Bloom–Sisask 2020, Kelley–Meka 2023): all deep/open, not
  session-tractable, unsuitable for Aristotle.
- Proved a genuinely new elementary result instead: **supermultiplicativity of the
  Roth number on coprime moduli**, via the Chinese Remainder ring isomorphism.

### Key Findings
- `ZMod (M·N) ≃+* ZMod M × ZMod N` (`ZMod.chineseRemainder`) carries a product of
  AP-free sets to an AP-free set: a 3-AP maps componentwise; injectivity forces a
  nonzero step in ≥1 factor, forbidden there.
- Gives `r₃(M)·r₃(N) ≤ r₃(M·N)` (coprime) and corollary `2·r₃(N) ≤ r₃(3N)`.
- Elementary, self-contained, **0-axiom** (no Fourier / density increment).

### Files Modified
- `proofs/Proofs/RothTheoremQuantitative.lean` (+87 lines, Part II.B)
- PR #34771

### Verification
- Standalone Part-I + Part-II.B build (`import Mathlib` only) **succeeded, 0 sorries**.
- Full-file build blocked by heavy `Proofs.RothTheorem` dep exceeding 23 GiB Docker
  allocation (environment limit, not this change).

### Next Steps
- Base-3 no-carry construction for `r₃(3^k) ≥ 2^k` (stronger explicit lower bound).
- Leave Part III deep bounds for dedicated multi-session work.

## Session 2026-07-04 (Session 2) - Base-3 no-carry lower bound r₃(3ᵏ) ≥ 2ᵏ

**Mode**: REVISIT (continues S1 "Next Steps")
**Outcome**: progress (new elementary theorem, math hand-audited; Lean drafted UNVERIFIED)

### What I Did
- Proved **Theorem A**: `2·r₃(m) ≤ r₃(3m)` for ALL m ≥ 1 (no coprimality) —
  strictly strengthens S1's `two_mul_rothNumber_le` (which needs Coprime 3 N).
- Proved **Theorem B**: `2ᵏ ≤ r₃(3ᵏ)` by induction, i.e. r₃(N) ≥ N^{log₃2}
  ≈ N^{0.631} along N = 3ᵏ. First super-constant explicit r₃ lower bound.
- Full math writeup + Lean draft: `research/notes/roth-theorem-k3-base3-doubling.md`.

### Key Findings
- Construction: reduction π : ZMod(3m)→ZMod m (ZMod.castHom), section L x = ↑x.val,
  set B = {L x + s : x∈A, s∈{0, ↑m}} where A is a maximal AP-free set in ZMod m.
  |B| = 2|A|; AP-free because reducing a progression mod m forces the step into
  ker π (a multiple of m), and then the middle term would carry base-3 top-digit 2 ∉ {0,1}.
- Nonvanishing crux: ↑(c·m) ≠ 0 in ZMod(3m) for c∈{1,2}, since 3m∣cm ⇔ 3∣c.
- Elementary, 0-axiom (no Fourier / density increment / Behrend).

### Verification (BLOCKER)
- **Dual-tool blackout**: Docker image blob corrupted (containerd content store
  `input/output error` on sha256:3d1c9c6b…; `docker run`/`inspect`/`build` all fail),
  AND Aristotle MCP returned 404 "Resource not found" for prove & prove_file.
  Neither machine-check path available → Lean is hand-audited only, UNVERIFIED.
- Deliberately kept the .lean OUT of proofs/Proofs/ (lakefile globs it → an
  unbuildable file breaks the whole gallery). Draft lives in the notes .md.

### Files Modified
- research/notes/roth-theorem-k3-base3-doubling.md (new; math + Lean draft)

### Next Steps
- When a build path recovers: port Theorems A/B into RothTheoremQuantitative.lean
  Part II.C (uses only Part-I API), fix elaboration errors (lemma names,
  linear_combination signs, mem_image/mem_product simp set), verify 0-sorry.
- Then re-derive `two_mul_rothNumber_le` as a corollary of Theorem A.
- Optional: Behrend-flavoured strengthening, or `r₃(3ᵏ) = 2ᵏ`? (upper bound is
  open in general; do NOT claim equality).
