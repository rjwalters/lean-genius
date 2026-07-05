# Knowledge Base: shannon-channel-coding-bec-oq-03

Single-letter Fano converse for the binary erasure channel (BEC).

---

## Problem Understanding

The parent `shannon-channel-coding-bec` proves the BEC's **information** capacity
`C(bec p) = (1 - p)·log 2` axiom-free. The sibling `-oq-02` derives the
**operational** coding theorem, but only by *applying* the framework axioms
`channel_coding_achievability` / `channel_coding_converse` — so it is honestly
axiomatized. The open question `-oq-03` asks for a genuinely axiom-free step
toward the converse.

**Resolution taken:** the gallery already *proves* (not assumes) the abstract
single-letter Fano converse `fano_converse_shannon_form`:

    (1 − P_e)·log|α| ≤ channelCapacity ch + h(P_e)

so specialising it to the BEC introduces **no** new assumptions. The only
channel-specific ingredient is the Fano collision-error term, which for the
uniform-input BEC has the clean closed form `P_e = p/2`.

---

## Insights

- **Closed-form Fano error term.** For `bec p` with the uniform Bernoulli(1/2)
  input, `P_e = 1 − Σ_y Σ_x P(x,y)²/P(y) = p/2`. Erasure output (`y = none`,
  marginal `p`) contributes `p/2`; each un-erased output (`y = some b`, marginal
  `½(1−p)`) contributes `½(1−p)`, summing to `1 − p`. Total `1 − p/2`, so
  `P_e = p/2`.
- **Axiom-free specialisation.** Because `fano_converse_shannon_form` and the
  underlying `fano_inequality` are theorems (ShannonChannelCoding.lean:352, :204),
  the BEC converse `(1 − p/2)·log 2 ≤ (1 − p)·log 2 + h(p/2)` is verified, not
  axiomatized — in deliberate contrast to `-oq-02`.
- **Rearranged bound.** Equivalent isolated form `(p/2)·log 2 ≤ h(p/2)`.
- **Scope boundary.** This is the *single-letter* (one channel use) converse. It
  does **not** discharge the operational block-coding axiom
  `channel_coding_converse`; that additionally needs the multi-use
  data-processing bound `I(W; Ŷⁿ) ≤ n·C` and Fano applied to the block message.

---

## Session 2026-07-03 (researcher-14, FRESH) — Integration + build repair

**Mode**: FRESH  **Outcome**: completed (proof builds, 0 sorries, 0 axioms)

### What I did
- Found a complete-but-**non-building** `ShannonChannelCodingBECOQ03.lean` left by
  a prior session (never gallery-integrated, `status: available`).
- Repaired two proof errors in `bec_uniform_fano_error`:
  - `e_some`: `simp only [reduceIte]` failed to reduce `if false = true …`; replaced
    with deterministic `if_pos (rfl) / if_neg (by decide)` case rewrites.
  - `hjs`: `congr 1` already closed the goal so the trailing `norm_num` errored
    ("No goals to be solved"); replaced with a `rw [show uniformBool.p x = 1/2 …]`
    that closes by `rfl`.
- Built with `docker-build.sh Proofs.ShannonChannelCodingBECOQ03` → success.
- Created gallery data `src/data/proofs/shannon-channel-coding-bec-oq-03/`
  (meta.json, annotations.json, index.ts). Status `verified`, badge `original`,
  axiomCount 0.

### Files modified
- `proofs/Proofs/ShannonChannelCodingBECOQ03.lean` (build repair)
- `src/data/proofs/shannon-channel-coding-bec-oq-03/{meta,annotations}.json`, `index.ts`

### Next steps
- Discharge `channel_coding_converse` for the BEC via the multi-use DPI bound
  `I(W; Ŷⁿ) ≤ n·C` (the genuinely open remaining piece).
- Reuse the `fano_converse_shannon_form` specialisation pattern for the BSC.

---

## Dead Ends

- `simp only [reduceIte]` is unreliable for reducing `ite` on Bool-equality
  conditions like `false = true` after `cases`; prefer explicit
  `if_pos`/`if_neg` with `rfl`/`by decide`.
