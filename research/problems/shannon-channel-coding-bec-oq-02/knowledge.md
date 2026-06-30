# shannon-channel-coding-bec-oq-02 — Operational Coding Theorem for the BEC

**Parent gallery proof:** `shannon-channel-coding-bec` (BEC information capacity `C = (1-p)·log 2`, axiom-free).
**Open question:** Establish an operational coding theorem for the BEC, connecting the
information-theoretic supremum proved in the parent to achievable communication rates
through the framework's `channel_coding_achievability`.

## Summary

The gallery's discrete-memoryless-channel framework (`ShannonChannelCoding.lean`) already
states Shannon's two operational theorems for an *arbitrary* `DMChannel`, in terms of its
`channelCapacity`:

- `channel_coding_achievability` — rates below capacity are achievable (random coding);
- `channel_coding_converse` — rates above capacity are not (Fano).

Both are **axioms** of that framework (the deep arguments are taken as given at the abstract
level). The BEC parent supplies, axiom-free, the concrete channel `bec : DMChannel Bool
(Option Bool)` together with the capacity value `bec_capacity : channelCapacity (bec p) =
(1-p)·log 2`. Specialising the two abstract theorems to `bec` and rewriting their capacity
hypothesis with `bec_capacity` produces the BEC operational coding theorem with an explicit
numerical threshold — exactly the bridge the open question asks for, via the route it itself
suggests ("through the parent's channel_coding_achievability").

This is an *instantiation*, not a from-scratch operational proof; it is therefore honestly
**axiomatized** (2 inherited axioms), not verified.

## Session 2026-06-27 (Session 1) — FRESH

**Mode:** FRESH · **Outcome:** completed (axiomatized, 0 sorries)

### What I did
- Surveyed the parent and framework: confirmed `bec` is packaged as a `DMChannel Bool
  (Option Bool)` and that `bec_capacity` gives `channelCapacity (bec p) = (1-p)·log 2`.
- Confirmed `channel_coding_achievability` / `channel_coding_converse` are the framework's
  abstract operational theorems, stated in terms of `channelCapacity ch` (and are axioms).
- Wrote `proofs/Proofs/ShannonChannelCodingBECOQ02.lean` (134 lines, 4 theorems):
  - `bec_coding_achievability` — every nat-rate `0 < R < (1-p)·log 2` achievable.
  - `bec_coding_converse` — every nat-rate `R > (1-p)·log 2` unachievable.
  - `bec_coding_achievability_bits` / `bec_coding_converse_bits` — bit-rate forms
    (threshold `1-p` bits), via `mul_lt_mul_of_pos_right` and `Real.log_pos`.
- Built the file axiom-checked: `#print axioms` shows achievability ← `channel_coding_achievability`,
  converse ← `channel_coding_converse`, each plus only `propext / Classical.choice / Quot.sound`.
- Authored gallery data (`meta.json`, `annotations.json`); verified the generator accepts
  the entry (appears in `listings.json` as status `axiomatized`, badge `axiom`, 4 annotations).

### Key findings
- The framework was already channel-agnostic: the *only* channel-specific input needed to
  instantiate the operational theorems is the numerical capacity value.
- The nat↔bit conversion is a single multiplication by the positive constant `log 2`; the
  rate guarantee `R₂·log 2 ≤ rate_of_code` is exactly "bit-rate `≥ R₂`".
- Honest status is `axiomatized` (2 axioms on the critical path). `leanFile.axiomCount = 0`
  (no literal `axiom` decl); `meta.axiomCount = 2` (inherited framework axioms).

### Gotchas
- Docker build wrapper is down (host disk ~95% full → containerd I/O error). Built via the
  `LAKE_UNSAFE=1 lake env lean -o .lake/build/lib/lean/Proofs/X.olean` fallback, compiling
  the Shannon dependency chain (OQ04, Entropy, OQ04OQ01, OQ03, OQ02OQ01, ChannelCoding, OQ02,
  BEC) one file at a time (each fast — Mathlib oleans are cached; the worktree `.lake` is a
  symlink to the main repo's shared cache).
- `mul_lt_mul_right` resolved to the wrong typeclass form (`MulLeftStrictMono ℝ` synth
  failure); use `mul_lt_mul_of_pos_right` instead.
- Worktree gotcha: an absolute-path `Write` landed the file in the MAIN repo, not the
  worktree — copied into the worktree and removed the stray.
- `node_modules` absent in the worktree; ran `scripts/annotations/build.ts` with the MAIN
  repo's `tsx` binary to validate the entry generates.

### Files
- `proofs/Proofs/ShannonChannelCodingBECOQ02.lean`
- `src/data/proofs/shannon-channel-coding-bec-oq-02/{meta.json,annotations.json}`

### Next steps
- Discharge `channel_coding_achievability` / `channel_coding_converse` themselves (random
  coding + Fano) to upgrade this and the sibling BSC/AWGN operational statements to verified.
- A BEC-specific constructive achievability (random linear codes + peeling decoder, threshold
  `1-p`) would replace the abstract achievability axiom with an explicit code family.
- Strong converse (error → 1 above capacity) and finite-blocklength dispersion for the BEC.
