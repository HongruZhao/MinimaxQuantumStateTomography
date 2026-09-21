import TomographyOracleCore.ChoKimGluingArithmetic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace TomographyOracleCore

open SimpleGraph

/-!
# The periodic two-layer overlap cycle

After alternating first- and second-layer gates around the periodic chain,
the gate-overlap graph of `m` staggered blocks per layer is the cycle on
`2m` vertices.  This module closes the graph-theoretic part of the
Cho--Kim specialization: connectedness, existence of a spanning tree, and
the exact `2m - 1` gluing-edge count.

The analytic two-unitary relative-design gluing inequality is separate.
-/

/-- Periodic two-layer gate-overlap graph with `m` gates in each layer.
The alternating enumeration is
`A₀, B₀, A₁, B₁, ..., Aₘ₋₁, Bₘ₋₁`. -/
def choKimPeriodicOverlapGraph (m : ℕ) : SimpleGraph (Fin (2 * m)) :=
  cycleGraph (2 * m)

/-- The periodic overlap graph has exactly two gate vertices per block. -/
theorem card_choKimPeriodicOverlapGraph_vertices (m : ℕ) :
    Fintype.card (Fin (2 * m)) = 2 * m := by
  exact Fintype.card_fin _

/-- With at least one block, the periodic gate-overlap cycle is connected. -/
theorem choKimPeriodicOverlapGraph_connected
    {m : ℕ} (hm : 0 < m) :
    (choKimPeriodicOverlapGraph m).Connected := by
  have htwo : 2 * m ≠ 0 := Nat.ne_of_gt (Nat.mul_pos (by norm_num) hm)
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero htwo
  rw [choKimPeriodicOverlapGraph, hr]
  simpa [Nat.succ_eq_add_one] using (cycleGraph_connected (n := r))

/-- Removing a suitable edge from the connected overlap cycle gives a
spanning tree with exactly `2m - 1` edges. -/
theorem choKimPeriodicOverlapGraph_exists_spanningTree
    {m : ℕ} (hm : 0 < m) :
    ∃ T : SimpleGraph (Fin (2 * m)),
      T ≤ choKimPeriodicOverlapGraph m ∧ T.IsTree ∧
        Nat.card T.edgeSet = 2 * m - 1 := by
  obtain ⟨T, hle, htree⟩ :=
    (choKimPeriodicOverlapGraph_connected hm).exists_isTree_le
  refine ⟨T, hle, htree, ?_⟩
  have hedge := (SimpleGraph.isTree_iff_connected_and_card.mp htree).2
  rw [Nat.card_fin] at hedge
  omega

/-- The periodic Cho--Kim block condition guarantees a positive number of
blocks `n / K`. -/
theorem ChoKimBlockCondition.blockQuotient_pos
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) :
    0 < n / K := by
  exact Nat.div_pos (h.block_le_qubits hn) h.block_pos

/-- Concrete overlap graph for the `n`-qubit, `K`-qubit-block circuit. -/
def choKimCircuitOverlapGraph (n K : ℕ) :
    SimpleGraph (Fin (choKimGateVertices n K)) :=
  choKimPeriodicOverlapGraph (n / K)

/-- The concrete periodic circuit's overlap graph is connected. -/
theorem ChoKimBlockCondition.circuitOverlapGraph_connected
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) :
    (choKimCircuitOverlapGraph n K).Connected := by
  simpa [choKimCircuitOverlapGraph, choKimGateVertices] using
    choKimPeriodicOverlapGraph_connected (h.blockQuotient_pos hn)

/-- Exact spanning-tree interface used by the iterative gluing theorem:
there are `choKimGateVertices n K - 1` gluing steps. -/
theorem ChoKimBlockCondition.exists_circuitOverlapSpanningTree
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) :
    ∃ T : SimpleGraph (Fin (choKimGateVertices n K)),
      T ≤ choKimCircuitOverlapGraph n K ∧ T.IsTree ∧
        Nat.card T.edgeSet = choKimGateVertices n K - 1 := by
  obtain ⟨T, hle, htree⟩ :=
    (h.circuitOverlapGraph_connected hn).exists_isTree_le
  refine ⟨T, hle, htree, ?_⟩
  have hedge := (SimpleGraph.isTree_iff_connected_and_card.mp htree).2
  rw [Nat.card_fin] at hedge
  omega

end TomographyOracleCore
