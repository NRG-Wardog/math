# Lean formalizations

Toolchain: Lean 4.19.0. Only Lean's built-in library is required.

```sh
cd lean
lake build
lean -DwarningAsError=true Math/AdmissibilityOfCostPartitionedBellmanPotentials.lean
```

Each proof has a named module in `Math/`. No `sorry` or unapproved axiom dependencies are accepted by CI. The scope and hypotheses of each theorem appear in its proof notes.
