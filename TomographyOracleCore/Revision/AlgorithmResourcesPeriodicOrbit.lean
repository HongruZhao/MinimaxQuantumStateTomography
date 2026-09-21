import TomographyOracleCore.BinaryCliffordFiniteThirdMoment
import TomographyOracleCore.BinaryCliffordPeriodicPhysicalChannel

/-! Compress the finite first-layer Clifford average to its Pauli-label orbit.
The orbit has at most d² elements; this proof does not enumerate the group.
-/

namespace TomographyOracleCore.Revision.AlgorithmResources

open scoped BigOperators

noncomputable section
set_option maxHeartbeats 1000000

theorem uniform_action_average
    {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω]
    [MulAction G Ω] [MulAction.IsPretransitive G Ω]
    (x : Ω) (f : Ω → ℝ) :
    (∑ g : G, f (g • x)) / Fintype.card G = (∑ y : Ω, f y) / Fintype.card Ω := by
  letI : Nonempty Ω := ⟨x⟩
  letI : Nonempty (ActionFiber (G := G) x x) := ⟨⟨1, one_smul G x⟩⟩
  have hf : (Fintype.card (ActionFiber (G := G) x x) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have ho : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc := uniform_action_sum (G := G) x (fun _ : Ω => (1 : ℝ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hc
  rw [uniform_action_sum x f, nsmul_eq_mul, hc]
  field_simp

variable {m K : ℕ}

abbrev SupportTuple (P : Fin m → PauliLabel K) :=
  {Q : Fin m → PauliLabel K // ∀ j, Q j = 0 ↔ P j = 0}

def supportPoint (P : Fin m → PauliLabel K) : SupportTuple P := ⟨P, fun _ => Iff.rfl⟩

theorem generated_smul_eq_zero (g : binaryTransvectionGroup K) (p : PauliLabel K) :
    g • p = 0 ↔ p = 0 := by
  constructor
  · intro h
    apply g.1.1.injective
    simpa only [binaryTransvectionGroup_smul_apply, map_zero] using h
  · rintro rfl
    exact map_zero g.1.1

instance supportTupleAction (P : Fin m → PauliLabel K) :
    MulAction (Fin m → binaryTransvectionGroup K) (SupportTuple P) where
  smul g Q := ⟨fun j => g j • Q.1 j, fun j => (generated_smul_eq_zero _ _).trans (Q.2 j)⟩
  one_smul Q := by
    apply Subtype.ext
    funext j
    exact one_smul (binaryTransvectionGroup K) (Q.1 j)
  mul_smul g h Q := by
    apply Subtype.ext
    funext j
    exact mul_smul (g j) (h j) (Q.1 j)

@[simp] theorem supportTupleAction_apply (P : Fin m → PauliLabel K)
    (g : Fin m → binaryTransvectionGroup K) (Q : SupportTuple P) (j : Fin m) :
    (g • Q).1 j = g j • Q.1 j := rfl

instance supportTupleTransitive (P : Fin m → PauliLabel K) :
    MulAction.IsPretransitive (Fin m → binaryTransvectionGroup K) (SupportTuple P) where
  exists_smul_eq X Y := by
    classical
    have hj (j : Fin m) : ∃ g : binaryTransvectionGroup K, g • X.1 j = Y.1 j := by
      by_cases hx : X.1 j = 0
      · have hy : Y.1 j = 0 := (Y.2 j).mpr ((X.2 j).mp hx)
        exact ⟨1, by simp [hx, hy]⟩
      · have hy : Y.1 j ≠ 0 := by
          intro hy
          exact hx ((X.2 j).mpr ((Y.2 j).mp hy))
        obtain ⟨g, hg⟩ := binaryTransvectionGroup_exists_smul_eq K ⟨X.1 j, hx⟩ ⟨Y.1 j, hy⟩
        exact ⟨g, congrArg Subtype.val hg⟩
    choose g hg using hj
    refine ⟨g, ?_⟩
    apply Subtype.ext
    funext j
    exact hg j

/-- Uniform independent block actions have a uniform image on precisely
the tuples preserving the zero/nonzero pattern of the input blocks. -/
theorem block_action_uniform_average (P : Fin m → PauliLabel K)
    (f : (Fin m → PauliLabel K) → ℝ) :
    (∑ g : Fin m → binaryTransvectionGroup K, f (fun j => g j • P j)) /
      Fintype.card (Fin m → binaryTransvectionGroup K) =
      (∑ Q : SupportTuple P, f Q.1) / Fintype.card (SupportTuple P) := by
  classical
  exact uniform_action_average (supportPoint P) (fun Q => f Q.1)

abbrev GlobalSupportOrbit (m K : ℕ) (p : PauliLabel (m * K)) :=
  {q : PauliLabel (m * K) // ∀ j,
    pauliLabelBlockEquiv m K q j = 0 ↔ pauliLabelBlockEquiv m K p j = 0}

def globalSupportOrbitEquiv (m K : ℕ) (p : PauliLabel (m * K)) :
    GlobalSupportOrbit m K p ≃ SupportTuple (pauliLabelBlockEquiv m K p) where
  toFun q := ⟨pauliLabelBlockEquiv m K q.1, q.2⟩
  invFun Q := ⟨(pauliLabelBlockEquiv m K).symm Q.1, by
    intro j
    simpa only [Equiv.apply_symm_apply] using Q.2 j⟩
  left_inv q := by apply Subtype.ext; exact Equiv.symm_apply_apply _ _
  right_inv Q := by apply Subtype.ext; exact Equiv.apply_symm_apply _ _

/-- A global word orbit replaces all first-layer Clifford choices by at
most d² Pauli labels, for any subsequent real-valued calculation. -/
theorem global_block_action_uniform_average
    (m K : ℕ) (p : PauliLabel (m * K)) (f : PauliLabel (m * K) → ℝ) :
    (∑ g : Fin m → binaryTransvectionGroup K, f (blockPauliAction m K g p)) /
      Fintype.card (Fin m → binaryTransvectionGroup K) =
      (∑ q : GlobalSupportOrbit m K p, f q.1) / Fintype.card (GlobalSupportOrbit m K p) := by
  classical
  have h := block_action_uniform_average (pauliLabelBlockEquiv m K p)
    (fun Q => f ((pauliLabelBlockEquiv m K).symm Q))
  have hs : (∑ Q : SupportTuple (pauliLabelBlockEquiv m K p),
      f ((pauliLabelBlockEquiv m K).symm Q.1)) =
      ∑ q : GlobalSupportOrbit m K p, f q.1 := by
    simpa only [globalSupportOrbitEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply] using
      (Equiv.sum_comp (globalSupportOrbitEquiv m K p)
        (fun Q => f ((pauliLabelBlockEquiv m K).symm Q.1))).symm
  rw [hs, ← Fintype.card_congr (globalSupportOrbitEquiv m K p)] at h
  exact h

#print axioms global_block_action_uniform_average

end
end TomographyOracleCore.Revision.AlgorithmResources
