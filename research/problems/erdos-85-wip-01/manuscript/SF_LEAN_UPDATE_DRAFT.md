# Draft: update to the SF Lean group (Robb's voice) — HOLD until the paper's DOI and article links exist

Placeholders to fill at release: [CHECKING.md link — GitHub release tag], [DOI], [rjwalters.info article].
Numbers are from paper v13 (anvil/erdos85-drop.13/main.tex, 12 October 2026) or the pinned receipts it links.

---

**Erdős 85 update: we didn't solve it, but we found a drop**

Earlier I was pretty bullish here that we might crack Erdős Problem 85, which asks whether the
minimum-degree threshold f(n) for forcing a 4-cycle is eventually nondecreasing. We didn't. Here is what we
did get, and exactly what it rests on.

**1. A strict drop: f(48) = 8 and f(49) = 7.**
- Both lower bounds are explicit graphs checked in Lean (via `native_decide`).
- For the upper bound, Lean splits any counterexample on 49 vertices into cases, excludes all but two
  families outright, and reduces those two to SAT: 13,351 formulas for one stratum, and 28 cover plus
  377,776 leaf formulas for part of another.
- Lean derives f(49) ≤ 7 from exactly two hypotheses: that all of those formulas are unsatisfiable.
- The CakeML-verified checker `cake_lpr` accepted an unsatisfiability proof for every one of them: about
  28 TB and 20 TB of LRAT, checked as it streamed, keeping only hashes.
- So it is **not** a Lean theorem: the checks run outside Lean and aren't admitted into it, the checked files
  are tied to the Lean formulas by emitters rather than a kernel proof, and the Lean side uses `native_decide`
  (601 axioms printed: the 3 standard ones plus 598 `native_decide`).
- We rebuilt the whole 893-module project from source and audited it. The first attempt failed in our build
  runner, and that record is published too. A second rebuild, fetching the certificate files with the public
  script, gave byte-identical objects.
- To our knowledge it's the first strict drop of f on the problem's domain at this level of evidence. In
  Boza's Ramsey table it amounts to selecting r(42) = 49.
- One drop is compatible with either answer to the problem. We claim nothing about Erdős 85 itself.

**2. A one-proposition reduction.**
- Lean proves, from the standard axioms only, that a single statement implies a negative answer to
  Erdős 85. That statement, A-REG, says there is no C₄-free 2ᵏ-regular graph on 4ᵏ vertices for k ≥ 3.
- A-REG is open, and we don't claim it. Its q = 4 analogue is false: Lean exhibits a C₄-free 4-regular graph
  on 16 vertices, and f(15) = f(16) = 5.

**You can check the main part yourself.** There's a public AMI (`ami-05697724475f2e748`, us-east-1).
`e85-check` regenerates each formula of the big stratum with our Lean-compiled emitter and streams the
published proofs through `cake_lpr`, or re-solves instances and confirms you get our byte-identical proof.
Guide: [CHECKING.md link]. Paper: [DOI]. Write-up: [rjwalters.info article].

**How it was done:** several months of collaboration between frontier models (Claude and GPT, as the state
of the art moved) and me. The models did most of the formalization, auditing and fleet work. The most
useful discipline was distrust: cold rebuilds, independent re-checks, and one review that caught us
claiming more than our certificates covered, which we fixed by re-checking 22.55 TB of older proofs with
`cake_lpr`.

Happy to talk about any of it, including what didn't work.
