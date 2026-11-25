# Floyd–Warshall distance bounds and in-place sweep equivalence

For a matrix of nonnegative integer distances with explicit infinity and a zero diagonal, the Floyd–Warshall update at pivot k preserves the triangle inequalities for previously processed pivots and establishes the triangle inequality through k. The pivot row and column do not change. Thus a complete in-place sweep has the same entries as the functional update, independently of the order in which the cells are visited.

If the initial matrix is no larger than the cost of every directed graph edge and every edge destination occurs in the pivot list, then the final entry between the endpoints of any finite path is finite and no larger than that path's cost.

The Lean development proves these facts by structural induction; it does not assume that the computed matrix is an exact shortest-path oracle. Exact realization of each finite label by a concrete path is a separate property not claimed here.

[Lean source](../../lean/Math/FloydWarshallDistanceBounds.lean). Theorems are generic and independent of any external implementation. Status: [Lean 4.19.0 kernel verified](https://github.com/NRG-Wardog/math/actions/runs/45701291726); six audited declarations, successful Lake build. This verifies the generic model, not a Python implementation.
