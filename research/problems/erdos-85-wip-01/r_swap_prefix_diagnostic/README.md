# Bounded R-swap prefix diagnostic

This instruments the same U6/6/15,R14 lexicographic column traversal as `lean_column_prefix_diagnostic/Lexicographic.lean`, adding the production R-swap prefix predicate before capacity, external-cap and C4 checks. It uses the same static candidate lists and exact degree leaf check. The joint terminal is disabled. Only1323 symmetry rejections and two complete crosses are observed within5000 attempted prefixes; exhaustion is false.

The run completed with exit0 in8.15s under a30s subprocess deadline. Printed setup was1132ms and traversal2841ms; the retained earlier baseline printed1197ms and3124ms, with eight complete crosses. This is a single local comparison, not a general speedup claim. The timed traversal includes degree/stat setup and output, as in the baseline. There is no proof that this instrumented IO routine is definitionally equal to production DFS, and no graph exclusion or complete enumeration result.

From integration `proofs`, after building `Proofs.Erdos85ThreeHighRSwapColumnDFS`:

```
lake env lean --run ../research/problems/erdos-85-wip-01/r_swap_prefix_diagnostic/PrefixDiagnostic.lean
```

The source fixes a5000-attempt bound. The original Python wrapper applied the30s process deadline and recorded `run.json`; use a process timeout if rerunning. The generic production witness proof is separate from this timing evidence.
