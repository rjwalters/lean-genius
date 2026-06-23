# S35 (researcher-3, 2026-06-16) — IntFractPair.stream bridge (open question #1)

**Mode:** BUILD (new orphan file) — Docker DOWN, Aristotle 404, so build-pending.
Deliberately chose the slug's *structurally significant* carried open question
over the convergent-ladder treadmill.

## Why not another convergent rung

At claim time this slug was heavily swarmed: open PRs adding the 17th (#24516),
18th (#24538), 20th (#24612), 23rd (#24635), 26th (#24767), 28th (#24802 +
#24809) CF convergent bounds, all touching the *same* helper file
(`CubeRoot3IrrationalOQ04Helpers.lean`) and therefore mutually conflicting, plus
two contesting the `a₁₂ = 8` main quotient (#23388 DRAFT, #23983 OPEN). main
already has convergents through the 29th merged (S34). Adding a 30th rung would
be a two-line `norm_num` treadmill step: routine, low marginal value, and
conflict-prone. Per the honesty standard ("do not describe trivial results as
significant"), I did not pile on.

## What I did instead

Open question **#1**, carried since S5 (~30 sessions) and never attempted:
connect the per-`aᵢ` nested-floor lemmas to Mathlib's *canonical* CF API
`IntFractPair.stream`. Mathlib's `GenContFract.of` is built on

    IntFractPair.of v       = ⟨b := ⌊v⌋, fr := Int.fract v⟩
    IntFractPair.stream v 0  = some (of v)
    IntFractPair.stream v (n+1)
        = (stream v n).bind (fun p => if p.fr = 0 then none else some (of p.fr⁻¹))

so the n-th partial quotient is `(stream v n).get.b`. None of the slug's
`cbrt3_aₙ` lemmas were tied to this.

### Verification cert (PASS, build-free)

`verify_intfractpair_stream.py` independently reimplements `IntFractPair.stream`
at 120-digit precision and confirms:

* **(A)** `stream.b[n]` equals the proven prefix `a₀..a₁₁ = [1,2,3,1,4,1,5,1,1,6,2,5]`
  for n = 0..11 (the indices the gallery has machine-checked as
  `cbrt3_a0 … cbrt3_a11`).
* **(B)** the fract-chain identity `xᵢ(stream) = 1/(…-a) nest` and
  `fract xᵢ = xᵢ - aᵢ` — i.e. the value whose floor each `cbrt3_aᵢ` computes is
  *exactly* the stream's `xᵢ`. All residuals `< 10⁻⁸⁰`.

This nails the mathematics regardless of Lean API drift.

### Lean (orphan, build-pending)

New file `proofs/Proofs/CubeRoot3IrrationalOQ04Stream.lean` (UNREGISTERED — not
in `Proofs.lean`, so it cannot affect the gallery build; the standard
"register-orphan" pattern). Contents:

* `cbrt3_stream_succ` — reusable one-reciprocation step lemma: from
  `stream cbrt3 n = some (of x)`, `Irrational x`, `⌊x⌋ = a`, derive
  `stream cbrt3 (n+1) = some (of (x - a)⁻¹)`. Makes every further index
  mechanical (reuse with `cbrt3_a3, …` + the matching irrationality witness).
* `cbrt3_stream_zero / _one / _two` — the explicit stream values at n=0,1,2.
* `cbrt3_stream_b_zero / _b_one / _b_two` — `(stream cbrt3 n).map (·.b) = some aₙ`
  for a₀=1, a₁=2, a₂=3, each discharged by the existing `cbrt3_floor_eq_one /
  cbrt3_a1 / cbrt3_a2`.
* `cbrt3_stream_prefix` — the bundled conjunction (the headline bridge).

Irrationality at each level via `irrational_cbrt3` then `Irrational.sub_int` /
`Irrational.inv`; `fract ≠ 0` via `Irrational.ne_int` + `sub_ne_zero`; the
floor/`1/·` alignment via `inv_eq_one_div`.

**Not Docker-verified.** API names to re-check at v4.26.0 (listed in the file
header): `GenContFract.IntFractPair`, `IntFractPair.stream_zero`,
`IntFractPair.stream_succ_of_some`, `Irrational.ne_int/.sub_int/.inv`,
`Int.fract` simp-unfold. The proof *structure* is correct (cert-backed); if a
name drifted only that lemma swaps.

## Next action (S36, when Docker is up)

1. `./proofs/scripts/docker-build.sh Proofs.CubeRoot3IrrationalOQ04Stream`
   (build by name — the file is an orphan). Fix any API-name drift.
2. Add `import Proofs.CubeRoot3IrrationalOQ04Stream` to `proofs/Proofs.lean`
   (register the orphan) and rebuild the registered closure.
3. Extend the bridge with `cbrt3_stream_b_three … _b_eleven` by reusing
   `cbrt3_stream_succ` (mechanical — each needs `cbrt3_aₙ` + an `Irrational`
   witness for the n-th nested reciprocal). The cert already covers n=0..11.
4. (Stretch) Bundle into a single `Fin 12 → ℤ` / list statement, then connect
   to `GenContFract.of cbrt3` partial denominators (`(GenContFract.of cbrt3).s`).

This is the first real progress on OQ #1 in ~30 sessions; it does not touch the
contended helper/main files, so it is conflict-free with every open PR.
