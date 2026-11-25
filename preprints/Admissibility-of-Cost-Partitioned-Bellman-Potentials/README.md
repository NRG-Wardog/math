# Admissibility of Cost-Partitioned Bellman Potentials

## Statement

Let a transition system have nonnegative integer edge costs, a goal predicate, and a finite family of nonnegative potentials. Suppose every potential vanishes at every goal. For each concrete transition, assign a nonnegative charge to each potential so that (i) its decrease is at most its charge and (ii) the sum of charges is at most the concrete edge cost. Then the sum of the potentials is admissible: it is at most the cost of every path to a goal.

The maximum of any finite family of admissible estimates is likewise admissible. An abstract Bellman potential can be transported back to a concrete state space when concrete goals map to abstract goals and each concrete edge maps to an abstract edge of no greater cost, or to an identity.

## Proof

For a legal transition from s to t of cost c, sum the local decrease inequalities. The partition inequality yields H(s) <= c + H(t). Induct on the length of an arbitrary goal-reaching path; the potential at the last state is zero. Thus H(s) is no larger than that path's cost. The maximum result follows by applying the individual estimates to the same path. For abstraction, the edge simulation hypothesis gives the same local inequality on the concrete space.

These are general, standard mathematical results, not a claim of novelty. The hypotheses must be independently established for a particular algorithm.

## Formalization

[Lean module](../../lean/Math/AdmissibilityOfCostPartitionedBellmanPotentials.lean), Lean 4.19.0, no Mathlib dependency. The module proves the path telescope, abstraction theorem, finite sum step and zero lemmas, additive admissibility, and the maximum rule. The CI job checks the listed declarations' axiom dependencies.

**Scope:** the general theorems only. The mathematical statements do not verify any particular solver or its implementation.

**Status:** [Kernel verified](https://github.com/NRG-Wardog/math/actions/runs/45700830958), Lean 4.19.0; seven audited declarations and successful Lake build.
