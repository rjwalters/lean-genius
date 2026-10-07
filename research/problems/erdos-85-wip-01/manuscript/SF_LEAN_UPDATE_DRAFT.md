# Draft: update to the SF Lean group (Robb's voice) — HOLD until the paper's DOI and article links exist

Placeholders to fill at release: [CHECKING.md link — GitHub release tag], [DOI], [rjwalters.info article].
Re-check every number against the final audited paper before posting.

---

**Erdős 85 update: we didn't solve it, but we found a drop, and anyone can check it**

A month ago I was pretty bullish here that we might crack Erdős Problem 85, which asks whether the
minimum-degree threshold f(n) for forcing a 4-cycle is eventually nondecreasing. We didn't. But we got two
results I'm proud of, and I wanted to report back honestly.

**1. A strict drop: f(48) = 8 and f(49) = 7.**
- Both lower bounds are explicit graphs checked in Lean.
- For the upper bound, Lean proves that any counterexample on 49 vertices falls into one of four strata.
- Lean also reduces the largest stratum to 13,351 symmetry-reduced SAT instances. Every one of them has an
  unsatisfiability proof accepted by a formally verified checker, mostly the CakeML-verified `cake_lpr`.
- That's about 28 TB of LRAT, checked as it streamed and then discarded, for roughly $225 of AWS compute.
- It's a certificate-checked computational result, **not** a Lean theorem: the external checks aren't
  admitted into Lean, and two smaller strata rest on reviewed arguments.
- To our knowledge it's the first strict drop of f established on the problem's stated domain. In Boza's
  Ramsey table it amounts to selecting r(42) = 49.
- One drop says nothing about the eventual behaviour the problem asks about.

**2. A one-proposition reduction.**
- Lean proves, from the standard axioms only, that a single uniform statement implies a negative answer to
  Erdős 85. That statement, A-REG, says there is no C₄-free 2ᵏ-regular graph on 4ᵏ vertices for k ≥ 3.
- A-REG is open, and we don't claim it. Its q = 4 analogue is false, since f(15) = f(16) = 5.

**You can check it yourself.** There's a public AMI (`ami-05697724475f2e748`, us-east-1). `e85-check`
regenerates each formula with our Lean-compiled emitter and streams the published proofs through
`cake_lpr`, or re-solves instances and confirms you get our byte-identical proof.
Guide: [CHECKING.md link]. Paper: [DOI]. Write-up: [rjwalters.info article].

**How it was done:** several months of collaboration between frontier models (Claude and GPT, as the state
of the art moved) and me. The models did most of the formalization, auditing and fleet work. The most
useful discipline was distrust: cold rebuilds, independent re-checks, and one review that caught us
claiming more than our certificates covered, which we then fixed by checking 22 TB more proofs.

Happy to talk about any of it, including what didn't work.
