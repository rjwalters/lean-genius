# Generated leaf native-axiom contract

The frozen pilot generator uses `native_decide` for three obligations:
the capacity-table index bound (`Table`), nonzero DIMACS literals (`Nonzero`),
and the LRAT check (`Check`). A local compilation of the exact pilot
Table/Nonzero fragment in `lean4-arm64:v4.31.0` confirmed that both earlier
obligations appear in its axiom report. The historical manifest permits only
`Check`, so the generated leaf and its audit contract are inconsistent.

`replay_common.GENERATED_LEAF_AXIOM_PATTERN` is an **explicit opt-in**:

```text
^Erdos85\.h1V2P[0-4]I[0-9]{5}(?:Table|Nonzero|Check)\._native\.native_decide\.ax_[0-9]+(?:_[0-9]+)*$
```

A new manifest selects it as the sole `allowed_axiom_patterns` entry.
An omitted/empty entry continues to allow only the three foundational axioms.
The original `NATIVE_AXIOM_PATTERN` and its Check-only behavior are unchanged.
Mixing contracts, adding arbitrary patterns, and widening the foundational
axiom list are rejected. No existing manifest is automatically upgraded.

The global pattern is combined with the exact profile/index ownership prefix
derived from the manifest-selected contract and the job. Compilation, replay
resumption, and independent receipt validation enforce ownership; another
leaf's native axioms are rejected. Independent validation also requires the
receipt's entire axiom audit to equal the hashed replay-ready audit. A new
contract does not permit shortening an old ownership prefix.

This explicitly discloses two additional native proof obligations; it does
not turn their native axioms into ordinary kernel proofs. Native-free tactic
substitution probes failed for the table, but this does not prove that a
structural kernel proof is impossible. The source generator is unchanged.
Local transaction tests use simulated compilation to test the acceptance and
publication rules; they do not certify an LRAT payload.

Deployment requires a separately reviewed and frozen manifest selecting the
contract, updated repository/tool hashes, and actual full replay evidence.
The current pilot freight is not changed by adding support for this contract.
