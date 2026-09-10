# Six additional partial historical H1 cube archives

A bounded scan of the historical 164-tag set, excluding the 99 root-input comparisons and the editor's 45-row local-DRAT inventory, found six more nonempty cube directories. They retain 58 cube CNFs (7, 11, 8, 9, 11 and 12 per tag) and partial DRAT files. These six tags are current frozen H1 targets, disjoint from those earlier evidence groups; their frozen rows have no CNF hash.

Every retained cube consists of a common base plus exactly two final unit clauses. Reconstructing each base gives one consistent hash per tag. A fresh native canonical emission and native check for each frozen table, with two workers and a 120-second per-call cap, matched all six derived hashes. Thus all 58 retained cube inputs are bound to their current canonical base plus the recorded units. Native receipts, input hashes and per-cube hashes are preserved. Generated temporary root CNFs were removed only after matching and rehashing; historical files were untouched.

`results.json` is the initial reconstruction pass: `frozen_base_sha256` and `base_matches` are null because no frozen hash existed. Its zero known matches and zero known mismatches are not the final outcome. `native-results.json` supplies all six successful canonical comparisons; joining by tag shows that every `derived_base_sha256` equals its fresh `native_receipt.cnf_sha256`.

These are incomplete 25-cube archives. No proof bytes were read or replayed, no solver was launched, and no historical overlay eligibility or closed-case status is asserted. Proof availability is filename observation only. The other 39 historical tags outside the earlier root/45 groups had no cube CNF in this bounded scan; this is not an assertion about every possible archive location.

The scripts preserve local experiment paths. The first attempted native invocation failed before emission because its parent output directory did not exist; this was fixed before the six successful emissions. The first reconstruction attempted a frozen-hash comparison and stopped on absent hashes; the revised pass records missing hashes explicitly. No failed attempt launched a solver or produced a comparison result presented as successful.

Independent review 2021 passed after rehashing all 58 cube CNFs and checking exact framing, native receipts, frozen table/tag/profile joins, successful emitter/check logs, and source identities. The reviewer’s result and read-only checker are retained. Scope remains partial input identity only.
