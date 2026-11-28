# Island Logistics proof closure ledger — 2026-11-27

**Status: PARTIAL.** This is a proof audit of the unchanged Python candidate whose SHA-256 is `93264524bbcb06648351c5c012a18ea228784bcf085266c287d131d3bacaf456`. No assignment source, identifiers or private test data are published here. The public kernel is not a proof of the Python interpreter or NumPy.

## Targets and model

For every legal finite instance, every physical state reachable under the full legal transition relation, and every finite goal completion of that state with movement cost M and handling cost A, prove 0 <= h(s) <= M+A. The minimum of these costs is h*. For an unsolvable state, a finite nonnegative estimate is below infinity.

A separate target is minimum-cost solution by the supplied graph-search A*. It needs admissibility, a sound canonical state quotient, legal successors and preservation of at least one optimal completion by successor reduction, plus termination.

The exact course PDF was not available; the formal domain is the supplied checker semantics and the finite, nonnegative integer input format. Clipping truck capacity by total weight and ferry capacity by truck count is safe for these states. No claim of a proof for arbitrary malformed input or arbitrary machine-sized NumPy allocations.

## Verified kernel

Checked revision: `561cb66f6bca2b5c0a131994152e78df76f14001`.
[Lean 4.19.0 successful run](https://github.com/NRG-Wardog/math/actions/runs/46042294266).
238 printed axiom-dependency records; no sorryAx and no custom axioms in these records. Permitted ordinary axioms: propext, Quot.sound, Classical.choice. This is a count of printed checks, not a claim that every source statement is independently audited.

New results since the previous green revision fdf23789572a4ab8f0749dbc68954e56a54ccdc9:
- Feedback-mask witness: feedback_rank_accepted, feedback_maximal_kept, causal_feedback_from_trace.
- Keyed cache invariants: key_cache_get, key_cache_insert, key_cache_evict, key_factors_projection.
- Abstract optimal goal-pop with reopens: astar_frontier_witness, astar_goal_pop_optimal.
- Effective completed-ride projection: effective_anchor_step, effective_parcel_step, effective_trace_hub_walk, hub_actual_simple_path.
- Port accounting: effective_port_local, effective_mint_bound, effective_port_step_budget, effective_trace_exists, effective_completed_port_budget.
- Actual cargo witnesses: hub_simple_event_witness, effective_event_capacity, hub_event_groups_perm, hub_arc_bin_from_real_trace.
- Class-preserving world automorphisms: wr_step, wr_path, wr_optimal.

## Closure matrix

| ID | Source area | Status and remaining proof obligation |
|---|---|---|
| 1 | Constructor / INIT | Model invariants proved. Prove tuple decoder, ID sorting, capacity clipping and every preprocessed array implement the model. |
| 2 | Full legal transitions | Six bounded actions modeled; carrier and capacity preservation proved. Exact checker-to-model and retained successor enumeration refinement remains. |
| 3 | Handling, weighted transport, bin packing | Mathematical path and partition bounds proved. Verify graph/distance builders, all integer cases and Python/NumPy recurrence correspondence. |
| 4 | Bridge / identity / tree / projections | Crossing, inventory, assignment and projection lemmas exist. Verify all detected cuts, all guarded tree and compressed-edge constructors, scope stocks and chosen DP rows. |
| 5 | causal_choices | Chronological rank and minimal-feedback witness now proved. Verify actual leaf-zone construction and exact subset recurrence/bit-mask implementation. |
| 6 | PassengerCycles / HubFlow | Cycle lemmas, actual simple-path and per-arc cargo witnesses, per-ferry/port credits now proved. Verify fleet grouping, actual port sums and conservation, full DFS and Gray-code enumeration against the model, and integrate with component budgets. |
| 7 | Pattern / SailingPattern / StockRide | Projection and abstract fixed-point admissibility proved. Verify concrete state encoding, all generated transition tables, goal zero labels and the numeric kernels against the certificate, including aborted construction. |
| 8 | RouteDP / ArrayRouteDP / direct assignment | Milestone, route, transfer and convolution witness lemmas proved. Verify every array recurrence and packing/assignment enumeration. |
| 9 | Numeric / indexing | Mixed-radix and histogram lemmas exist. Audit every dtype and overflow/sentinel guard, shape, indexing and integer conversion. |
| 10 | Caches | Generic cache safety proved. Full tuple keys and exact factorization are addressed below; each projected cache key requires its own value-factorization theorem. |
| 11 | h_state / bounds | Source-level composition argument below; exact evaluator refinement remains. |
| 12 | successor | Final delivery, delivered parcel freezing and isolated-port retraction proved in model. Remaining commute/erase/collapse proofs for all priority, bridge, component, capacity, ferry and deduplication rules, and Python integration. |
| 13 | wrap symmetry | Class-preserving relabeling is now a verified cost-preserving automorphism. Source-level reconstruction argument below; full machine-checked exact key-to-renaming construction remains. |
| 14 | search.py | Abstract reopen/optimal-frontier theorem now proved. Verify actual queue/closed-table invariant, actual key relation, retained-child completeness and termination against source. |
| 15 | End-to-end | OPEN. Compose all of the above without leaving assumptions about the exact executable unproved. |

## Mathematical reconstruction of the canonical key (source-level)

Fix a world, with P packages. The class of a package is its (weight, goal), the class of a truck is its clipped capacity, and the class of a ferry is its (clipped slots, normalized served-port set).

The base b = 2^max(1, bit_length(P)) is strictly greater than P, including P=0. Every cargo digit or ground count digit is at most P. Hence its positional encoding is injective: decode by repeated remainder and division by b. This applies to the ground count indexed by class and location as well as the cargo count indexed by class. Truck signatures use cargo_code*cbase + capacity_class; every capacity-class index is strictly below cbase, so remainder and quotient recover both values.

If two valid states have identical canonical keys, their sorted ferry signatures coincide with multiplicity. Match ferry instances of the same class, same port, and identical multiset of aboard truck signatures. Within each matched ferry pair match the passenger trucks of the same signature; match ground trucks by location and signature. This gives a bijection of trucks preserving capacity and the enclosing ferry or ground location. Within each matched truck match packages classwise using the equal decoded cargo counts. For unmatched ground packages away from their goals, equal decoded ground counts give a classwise bijection at each location. In each package class the total count is fixed by the world. Subtracting the matched unfinished counts leaves equal delivered counts, and their ground location is the class goal. Match those remaining packages at their goals.

The three bijections are disjoint within each entity type and cover every legal index. They extend by the identity outside the finite index domains. Consequently the states are related by a class-preserving relabeling. By wr_optimal, their optimal completion costs agree. In the non-canonical fallback, equality of keys is literal equality of physical tuples. The reverse direction also follows because class-preserving relabeling preserves the sums and sorted multisets.

This mathematical argument does not require the heuristic to be invariant under the permutation; admissibility at each representative is sufficient. It does require the implemented integer arithmetic, sorting and state representation to obey the described semantics. The matching construction itself has not yet been mechanized in Lean.

The deduplication case has equal action cost: a SAIL changes exactly one ferry's physical port to a distinct port, changing the multiset of (ferry class, port). Non-SAIL actions leave that multiset unchanged. Thus a SAIL successor cannot collide with a unit-cost successor under the key. Two colliding SAIL successors both cost 3; any two other successors both cost 1.

## Top-level composition (source-level)

For an arbitrary legal completion, let A be the count of handling actions, R the number of road drives, F the ferry-action cost, M=R+F. H counts 2 per unfinished ground package, 1 per carried package. If a relaxation omits r packages that require additional intermediate handling in the chosen completion, H+2r <= A (charge the nonfinal unload and subsequent reload).

All pure movement bounds must be <= M. Each disjoint road/ferry combination must count each real action cost at most once. In the direct-assignment and route-option relaxations choose the column induced by the same actual completion; the admitted omission count r has H+2r<=A and the option movement term plus its disjoint extra budget is <=M. For that column, H+2r+max(movement, option+extra)<=A+M. The minimum over columns is no larger. The maximum of valid full estimates is still <=A+M. The geographic branch partitions charges over ferry groups, roads and any assigned extra handling, and its fast path uses only that partition bound. The stock-ride branch uses its movement witness and the same option argument. Returning 0 at goal, a statically impossible instance, or an infinite sentinel is safe. Any finite numeric conversion must preserve a nonnegative integer bound.

For the top-level hcache and wrapcache, the exact labeled physical tuple is the key; eviction discards knowledge, not correctness. A per-object cached heuristic must belong to this same tuple and fixed initialized world. Projected keys for road, ferry, route and fleet subcaches need stronger individual factorization proofs.

These are proof arguments, not an exact executable refinement. The existing private source-level audit gives additional details on the individual movement formulas. Its conclusions must not be promoted to machine-verified Python correctness.

## Verification decision

Do not mark the universal target complete, and do not merge this research PR as an end-to-end certificate. Intermediate failed proof elaborations were repaired; the checked revision above is green. The Python candidate and original course search remain unchanged. Finite oracle tests are evidence, never the universal proof.

## 2026-11-28 — additional checked constructor, arithmetic, trace and pruning results

Checked proof revision: `ae72ab85c7069d5053e4aa896557682b638c934e`.
[Successful Lean 4.19.0 run](https://github.com/NRG-Wardog/math/actions/runs/46130802947): 265 printed axiom-dependency records, no sorryAx or nonstandard axioms. These supersede the earlier count, not the PARTIAL status.

- Floyd-Warshall phase/cap and in-place scan equivalence; flood reachability/completeness; true bridge cut and disjoint road-cut charge certificates. Exact source adjacency and all tree/geo constructors still need refinement.
- Explicit Bellman path certificate, injective/reversible count transfers, capped min-plus, conditional DirectCut signed-integer guards, load-proposal guard, and conditional evaluator branch composition. The complete Python-generated arc sets, array recurrences and all dtype guards remain to be related to these definitions.
- Full loaded ferry priority: independent actions commute with the first selected ferry movement/service in a goal path, preserving cost and final state in the model. Other priority rules and the composition of all successor filters remain open.
- Fleet completed-port capacity budget, exact port-stock conservation and actual-trace instantiation of the HubPortTrace bound. The per-port cargo/bin premises, global fleet/road/service partition and actual DFS/Gray-code integration still require exact linking.
- Signed truck/parcel encoding round trips and injectivity; capacity clipping preserves every legal step and path (including zero weight/capacity). Finite state tuple equality and the actual canonical-key reconstruction and projected cache keys still require full formal refinement.

The original Python candidate is unchanged. No universal admissibility or end-to-end A* certificate is claimed. This PR must remain unmerged as an end-to-end certificate.
