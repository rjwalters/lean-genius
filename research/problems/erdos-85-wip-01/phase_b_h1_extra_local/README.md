# Additional local H1 historical case

Case `4ee646ca0ec3e2f0` (profile 1) is the one member of the historical 164-tag list with a local `.v2.cnf` outside the original remote-sweeps comparison set. The bounded native materializer emitted the frozen table and checked the result; the generated input matches the existing local CNF at SHA256 `061a1aa2ac9a984079fc328b21923c930bc4c40dbf806deb690afec9c37cdeb5`, 41,554 variables, 611,820 clauses and 12,478,506 bytes.

The paired verdict has a short format: `UNSAT 214.0s drat:VERIFIED mode:MONO arm:v2 lean-exact:MATCH profile:1`, with the tag first. It has no inline table, so the original 95-case validator correctly does not accept it. Instead, the local `manifest.tsv` supplies a unique tag/profile/table row equal to the frozen manifest, and the paired DRAT log reports `s VERIFIED` with matching variable/clause counts. Exact metadata bytes and hashes are retained in `extra-local-audit.json`; native input/validation receipts are in `extra-local-result.json`.

This supports a separately reviewed historical evidence candidate. It does not alter the frozen 95-case overlay, replay a proof, or establish a kernel theorem. A compact LRAT file is present, but only its path and size were observed. Historical proof validity remains inherited from the recorded verification, not freshly established.

The original comparison harness is banked under `phase_b_h1_historical_identity/compare.py`; this case was selected from the original all-path index rather than its remote-only subset. Its generated temporary CNF was removed after matching and rehashing, while all historical files remain untouched. The new source-check script performs only read-only receipt/metadata/CNF verification; it needs the original local archives and the banked frozen H1 manifest.

Independent review 2014 passed: Claude rehashed the archived CNF, checked all 611,820 clause lines with strict framing, and independently joined the local manifest, frozen table/tag, verdict and verification log. This approves historical evidence for a candidate 96th row; the existing 95-row parser and overlay remain unchanged.
