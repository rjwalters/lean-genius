# Erdős 85: preliminary literal Lean axiom audit (2026-09-16)

This is a literal `#print axioms` readout from a pinned compiled overlay, not
a fresh cold build of the current integration branch. It covers Theorem B and
the checked witness/conditional finite-drop endpoints; it does not discharge
the order-49 nonexistence hypothesis or prove Erdős Problem 85.

## Provenance and command

- Lean: `4.31.0`, arm64 macOS, commit `68218e876d2a38b1985b8590fff244a83c321783`.
- Overlay source commit: `4c7cbb515934254e0795916001617150587559f5`.
- Overlay receipt: `/Users/rwalters/lean-genius-h1-pilot-consume-000202d67bf3c583/complete-overlay-4c7cbb5159-import-data/receipt.json`, SHA-256 `bd53ce093e53654fdb32d97b66c6251cd3aafdcacaffb65dd1f67bbe2d02657a`.
- Overlay `.olean` SHA-256 values: `Erdos85BinarySquareRegularCapstone` = `bc1a12fd6d72457fdebc240e4590e5e451fd9c536a2ceba1f2c75dd84858b3e6`; `Erdos85FiniteDropWitnesses` = `77ebb758c061fca8a20b37e7ff5a9f354ad8e14e2b603d2b37b7c93af5347555`.
- The two target Lean source blobs at the overlay commit exactly match current integration `HEAD`: capstone blob `580930c0d9c900529bf623a752c04b700abebc1a`, finite witness blob `5b0585c41353b006c2dc74cfaa2813417288227e`. The `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` SHA-256 values also match the overlay receipt control files: `efac0b94923b2d8b6840cd35be9177ad0fc5ab2332f4f4311c98712cee92fdee`, `e39bd404385477992a2a22621fb21ffcb571e855242ff7fb19f0fbcb500f9d23`, and `f243fb1348183fbb95612c9c97beea1620651a55441b3e78fbc6bc3bfd26da01`.
- Audit input SHA-256 `f75243048b73c5b4b8eb880bdbc4084f0b0e34955f85f50c83ca9e9d64f32c21`; output SHA-256 `5319237249875a9369e10d91213e9cccf9aa7df18adde8cd80e2e14e61270f6f`.

The temporary input was:

```lean
import Proofs.Erdos85BinarySquareRegularCapstone
import Proofs.Erdos85FiniteDropWitnesses

#print axioms Erdos85.not_erdos85Question_of_binarySquareRegularExclusion
#print axioms Erdos85.minDegreeForC4_fortyEight_eq_eight_checked
#print axioms Erdos85.seven_le_minDegreeForC4_fortyNine_checked
#print axioms Erdos85.minDegreeForC4_fortyEight_fortyNine_exact_checked
#print axioms Erdos85.minDegreeForC4_fortyNine_lt_fortyEight_checked
```

From `proofs/`, the command was:

```sh
lake env sh -c 'LEAN_PATH="/Users/rwalters/lean-genius-h1-pilot-consume-000202d67bf3c583/complete-overlay-4c7cbb5159-import-data/overlay:$LEAN_PATH" lean /tmp/erdos85-axioms-sol1.lean'
```

## Literal output

```text
'Erdos85.not_erdos85Question_of_binarySquareRegularExclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos85.minDegreeForC4_fortyEight_eq_eight_checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Erdos85.boza48Graph._native.native_decide.ax_1,
 Erdos85.boza48Graph_common_le_one._native.native_decide.ax_1_1,
 Erdos85.boza48Graph_degree._native.native_decide.ax_1_1]
'Erdos85.seven_le_minDegreeForC4_fortyNine_checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Erdos85.orderFortyNineDegreeSixGraph._native.native_decide.ax_1,
 Erdos85.orderFortyNineDegreeSixGraph_common_le_one._native.native_decide.ax_1_1,
 Erdos85.orderFortyNineDegreeSixGraph_degree_ge._native.native_decide.ax_1_1]
'Erdos85.minDegreeForC4_fortyEight_fortyNine_exact_checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Erdos85.boza48Graph._native.native_decide.ax_1,
 Erdos85.boza48Graph_common_le_one._native.native_decide.ax_1_1,
 Erdos85.boza48Graph_degree._native.native_decide.ax_1_1,
 Erdos85.orderFortyNineDegreeSixGraph._native.native_decide.ax_1,
 Erdos85.orderFortyNineDegreeSixGraph_common_le_one._native.native_decide.ax_1_1,
 Erdos85.orderFortyNineDegreeSixGraph_degree_ge._native.native_decide.ax_1_1]
'Erdos85.minDegreeForC4_fortyNine_lt_fortyEight_checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Erdos85.boza48Graph._native.native_decide.ax_1,
 Erdos85.boza48Graph_common_le_one._native.native_decide.ax_1_1,
 Erdos85.boza48Graph_degree._native.native_decide.ax_1_1]
```

Theorem B's endpoint depends only on Lean's standard axioms in this overlay.
The finite witness endpoints additionally depend on named `native_decide`
axioms: three for the order-48 graph, three for the order-49 graph. Thus the
witnesses have been checked through Lean's native decision procedure, with its
extra trust assumptions; a claim of a standard-axiom-only kernel proof for
these endpoints would be inaccurate. The current target source files were
also individually elaborated against this overlay with `lean
Proofs/Erdos85BinarySquareRegularCapstone.lean` and `lean
Proofs/Erdos85FiniteDropWitnesses.lean`; both exited zero. They reused the
overlay's transitive imports. A fresh current-branch cold build and the
release endpoint audit are separate work.
