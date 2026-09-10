# A terminal obstruction for one admissible completion

`Certificate.lean` fixes full compact U parameters `(6,6,15)`, secondary
representative14, and an explicit15-row cross matrix. It proves that this cross
belongs to the cross domain and satisfies the external block cap, but has no
`ThreeHighJointWitness`.

An explicit24-row adjacency table is checked equal to the original block
adjacency. Three supplied lists cover every eligible block-capped initial triple.
After one simultaneous support pass, every color0 triple meets
`{9,11,12,13,14,17,19}` at most once. These seven vertices lie in the color0
residual set, so six triples cannot cover them. The general selected-separated
certificate theorem converts these finite checks into the joint-witness
contradiction. All finite facts use ordinary kernel `decide`.

This rejects exactly the supplied cross completion. It does not reject all
crosses for this U/R pair, discharge any remaining-pair search obligation, or
solve Erdős85. It demonstrates that the terminal family condition adds a real
constraint beyond cross-domain membership and the external block cap.

From the repository `proofs` directory, run:

```
lake env lean ../research/problems/erdos-85-wip-01/terminal_canary/Certificate.lean
```

`compile.log` and `RECEIPT.json` retain the final source-check result and hashes.
No compiled binaries or diagnostic evaluation are used as proof certificates.
