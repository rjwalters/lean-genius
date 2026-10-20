# H7 `source_cnf_sha256`: what the hash identifies

This note answers external review jhpvtq (erdosproblemaday.com). It changes no
Lean module. The released closure is byte-for-byte unchanged.

## The point

The docstring of `proofs/Proofs/Erdos85OrderFortyNineSevenHighCnf.lean` calls
the module "the Lean counterpart of `generate_h7_canonical_cnfs.py`". To be precise:

* **Clause list and order match.** The Lean formula has the same clauses in the
  same order as `sat49/generate_h7_canonical_cnfs.py` (`build`):
  1. 21 high-high zero units.
  2. 42 x 7 = 294 high-low support units.
  3. The C4 clauses, in `itertools.combinations` order.
  4. 49 `CardEnc.equals` sequential-counter blocks (bound 8 for vertices 0..6,
     bound 7 for the others).
  5. The 42 x 7 partition clauses.
* **Edge variable numbering differs.** Lean numbers the edge variable
  `{a,b}` (a < b) lexicographically, as
  `orderFortyNineEdgeIndex a b + 1 = 1176 - (49-a)(48-a)/2 + (b-a)`
  (`Erdos85OrderFortyNineBooleanTerminal.lean`,
  `Erdos85OrderFortyNineDimacsRows.lean`). The Python generator uses a pysat
  `IDPool`, which numbers edges in the order they are first used.
  * The first 315 clauses are unit clauses. They use 315 distinct edges, and
    pysat numbers those edges 1..315 in clause order. Every other edge is first
    used in the C4 loop.
  * Under the two numberings, **307 of the 1,176 edge variables get different
    numbers.** All 307 are among the 315 edges first used by the leading unit
    clauses. The other 869 edge variables, and all 28,588 counter auxiliaries
    (variables 1177..29764), get the same numbers in both.
  * The renumbering applies to every occurrence of those 307 variables, in all
    clause families.
* **What `source_cnf_sha256` is.** In the 13 generated certificate modules
  `Erdos85OrderFortyNineSevenHighT{t}Rep{r}Certificate.lean`, the header field
  `source_cnf_sha256` is the SHA-256 of the original pysat DIMACS file written
  on 2026-08-15 (`artifacts/erdos85-sat49/h7-canonical/h7_t*_rep*.cnf`).
  * It is a provenance hash only.
  * It is **not** the hash of any rendering of the Lean formula
    `orderFortyNineGeneratedH7SatCnf`.
  * Lean never reads or checks it. Each module's LRAT check runs against the
    Lean-generated, lexicographically numbered formula.

## Hashes

All 14 files have header `p cnf 29764 1329041`, 1,329,041 clauses, and no
comment lines. The t = 0 file has no certificate module (t = 0 is handled
structurally), so it is listed separately.

* **pysat SHA-256** is the SHA-256 of the original file. For every
  t >= 1 row it equals the module header's `source_cnf_sha256`.
* **Lean-numbered SHA-256** is the SHA-256 of the same file after mapping each
  edge variable to its lexicographic number. Everything else is kept the same:
  the `p` line, one clause per line, literals separated by single spaces, a
  closing `0`, and `\n` line endings.

| Instance | pysat SHA-256 (= header `source_cnf_sha256`) | Lean-numbered SHA-256 |
|---|---|---|
| h7_t1_rep0 | `6699c73daa88c3911597cf54251627584c6f0f32474ba6c52cff460d36778b9a` | `4fc61de93baa194451e75c255aa0669a92dc39475d7c81670ac1927799ab76d9` |
| h7_t2_rep0 | `c70e7d20d07705107748b92c85820ff7a6a9e2832028103917459c7357dc6b6d` | `ec513acc07711cba71ba6aa2b5c3b92fc77a434a945856464e99a84fb5118bf3` |
| h7_t2_rep1 | `12498caa61c8a62fcb94eac04213eda2e71eda60975598458ad37737b9ae671d` | `ecd1b4b1b8a5145072e84ebd2b496425266e1c47e713c359cff8f280cc2bc90e` |
| h7_t3_rep0 | `2f189eae275291b2fb217a3ab0c80421f105e86b396ac91c2b992b9536b2b7ec` | `38eb4dee71c3b8aff1ad59ae14e554d1d6d76c3686fc3441f34e23380f7a1a26` |
| h7_t3_rep1 | `ccf36d58acb43047488c0206d10261751569fbd2c3bd85a65d7f8593a1b5c890` | `53f2021e55bc96741274f8b54739ce1a8eaabb8c6aaa9db4848694a821c875d2` |
| h7_t3_rep2 | `06d60da77f9bc80d6e32367e0cebafbb024a7c7f4bd97bb0ad0d43862122dabb` | `c9ca91901c1c18fa85c153ed7bb2e88df20e02e18ab02a517b2850ea82b4848b` |
| h7_t4_rep0 | `f14d3eb5faad3605ac8bdc5ec0b376edf0d7c56ea2000764b396c63cc770c17a` | `b79bf0480aac049a7be39033c5d13b226a1ca2135d6bae4f23e0889ab6cc369f` |
| h7_t4_rep1 | `5bbd6a69f22e6ba5093fa8ec431f5ffb5c23b972f4a98d729aa4a7adb730a82c` | `846580ea30ca3f4bee195ecb015b62c91d5deca5a42d9c5b24837c20a55e6343` |
| h7_t4_rep2 | `9fa93084d09800cda1e4d6e44570f6f0126f82b323da9e3c28bd305dce64601a` | `30f36fae422f1cc60ca8e8ce1ed68bf02c88c830a1a2f02bbf5cb926d1cd5e5e` |
| h7_t5_rep0 | `c79b3293d51914c5ee06a609f011903322467db5bfc06da1b26bacf5a35e65c1` | `dc1aafae0b5cb13264a80da37055db91e6da1221cc4ac59e6c3d67d92f6db48c` |
| h7_t5_rep1 | `999d879a94dced8f45efcd31ffea4cd0987e8fc3876f4fcc77807ce3b0ae5a31` | `6fdcf4f248d65cc3fefc6445e1cf476724ffb54c0125418bb1de21a40a77de0f` |
| h7_t6_rep0 | `16825dda98f4945fadd04c2e30428dd2df832be5432d78e82e7d06264c9a8470` | `4c463a9582484e6c0cc5bab2a83d8f68aa639685cecaacaa1820f9c3bfcff468` |
| h7_t7_rep0 | `a2a409bc957ffe391805a4df1154a6f0a8ef091f1a888bc870effb63a6ffa1f2` | `e3c55d7502c4605d3a97a466dedf94e9b6300bcc71504a72bd650e1e7347582c` |
| h7_t0_rep0 (no module) | `a51e3e57bebcd6cfaefa06d73f85c56500e50e4156d9c606ef7e32a62ee80bab` | `4a5a38a1af8b01e3733e8ae53162b9ff7dbb2d2f96795de2bcc8a73b193a8e6d` |

## How these were computed

The pysat first-use numbering was rebuilt by replaying the generator's edge
calls in order: units, then the C4 loop. Every file was hashed in a streaming
pass on 2026-10-20. Two cross-checks hold:

* All 13 t >= 1 pysat hashes equal the `source_cnf_sha256` headers.
* The h7_t7_rep0 Lean-numbered hash equals a separate, earlier rendering of the
  same file.

The script is not part of the repository. It needs the original DIMACS files,
about 29 MB each, which are not tracked.
