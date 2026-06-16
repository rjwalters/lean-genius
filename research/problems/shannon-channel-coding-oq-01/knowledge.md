# Knowledge Base: shannon-channel-coding-oq-01

Concrete channel capacities beyond placeholder `True` statements (BSC / BEC / AWGN).

---

## Problem Understanding

The slug broad-matches the whole `ShannonChannelCoding*` proof family. The real
question: can specific named-channel capacities be formalized (not placeholders)?

State as of 2026-06-16 (researcher-8 session):

- **BSC** — DONE. `ShannonChannelCodingOQ02.lean` proves
  `bsc_capacity_proved : channelCapacity (bsc p) = log 2 - h(p)` from first
  principles, 0 axioms. The parent file `ShannonChannelCoding.lean` still
  *declares* `axiom bsc_capacity_eq`, but that is only a forward-declaration:
  it is discharged downstream in OQ02. It cannot be inlined into the parent
  because OQ02 imports the parent (inlining would create an import cycle).
  So the parent's axiom count (3) is not reducible without a structural
  refactor that moves `bsc`/`channelCapacity` upstream — not attempted.
- **BEC** — the genuinely-open item ("audit BEC/AWGN separately"). Addressed
  this session (see Insights).
- **AWGN** — still open; continuous channel, needs measure-theoretic capacity
  (much harder than the finite-alphabet BSC/BEC). Not attempted.

---

## Insights

### BEC capacity = (1 - p) · log 2  (researcher-8, 2026-06-16)

New file `proofs/Proofs/ShannonChannelCodingBEC.lean` (orphan/unregistered,
**build-pending** — full Docker blackout this session, load ~26, daemon
unresponsive rc=124). Models directly on the OQ02 BSC development.

- Channel: `bec : DMChannel Bool (Option Bool)`, `none` = erasure.
  `W x (some y) = if x = y then 1-p else 0`, `W x none = p`.
- **Engine identity** `bec_conditional_entropy : H(X|Y) = p · H(X)` for ANY
  input distribution. When the output is un-erased (prob 1-p) it determines X
  exactly (the `some y` summands vanish: off-diagonal joint = 0, diagonal
  conditional = 1 so log 1 = 0); when erased (prob p) the full input entropy
  remains. This is the clean way to do BEC — it is NOT weakly symmetric (erasure
  column sums to 2p, others to 1-p) so the symmetric-channel machinery in the
  parent does not apply.
- Chain rule (`chain_rule` in ShannonEntropy) → `bec_mi_eq : I(X;Y) = (1-p)·H(X)`
  for all inputs. Converse `I ≤ (1-p)·log 2` is then immediate from
  `H(X) ≤ log|Bool| = log 2`; achievability from uniform input giving
  `H(X) = log 2`. Hence `bec_capacity : channelCapacity (bec p) = (1-p)·log 2`,
  plus `bec_capacity_bits = 1-p`, nonneg, ≤ log 2. 0 axioms, 0 sorries.
- Numeric certificate: `research/certs/verify_bec_capacity.py` (PASS, both
  identities + capacity, p ∈ {0.05..0.99}, several input dists).

Reused from OQ02: `BSCCapacity.uniformBool`, `BSCCapacity.entropy_uniform_bool`,
and the general `chain_rule`, `entropy_le_log_card`, `channelMI_le_log_card`,
`csSup_le`/`le_csSup` capacity-sup idioms.

### API / build notes

- `set ch := bec ... with hch` BREAKS `rw [marginal_lemma]` because the goal
  then holds `ch` while the lemma produces `bec p hp0.le hp1.le` (rw needs a
  syntactic match). Write the full channel term throughout instead of `set`.
- `Fintype.sum_option : ∑ i : Option α, f i = f none + ∑ i, f (some i)`.
- card Bool cast: `simp only [Fintype.card_bool, Nat.cast_ofNat]`.

---

## Dead Ends

- Eliminating the parent's `bsc_capacity_eq` axiom in place — blocked by the
  parent↔OQ02 import direction (would need an upstream structural move).
- Building anything this session — Docker daemon blackout (load ~26).

---

## Next Steps

1. When Docker is back: build `ShannonChannelCodingBEC.lean`; fix any
   simp/lemma-name drift; then register it (add to the import graph / gallery).
2. Optional: a gallery entry `src/data/proofs/shannon-channel-coding-bec/`.
3. AWGN capacity (continuous) remains the only untouched concrete channel.
