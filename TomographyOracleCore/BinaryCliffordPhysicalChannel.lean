import TomographyOracleCore.BinaryCliffordGeneratedEnsemble

namespace TomographyOracleCore

open scoped BigOperators

/-!
# Literal physical measurement channel for the generated Clifford ensemble

This module connects the concrete unitary lifts to the Born trace/projector
dephasing channel.  On every Pauli matrix, conjugating into the computational
basis, dephasing, and conjugating back is exactly the indicator that the
symplectic image is Z-type.  The arbitrary Clifford phase cancels.
-/

/-- A unitary matrix satisfies `U† U = I`. -/
theorem unitary_conjTranspose_mul_self {K : ℕ}
    (U : Matrix.unitaryGroup (PauliBinaryWord K) ℂ) :
    U.1.conjTranspose * U.1 = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using
    (Matrix.UnitaryGroup.star_mul_self U)

/-- Undo a unitary sandwich. -/
theorem unitary_unsandwich {K : ℕ}
    (U : Matrix.unitaryGroup (PauliBinaryWord K) ℂ)
    {A B : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ}
    (h : (U.1 * A) * U.1.conjTranspose = B) :
    (U.1.conjTranspose * B) * U.1 = A := by
  rw [← h]
  have hunit := unitary_conjTranspose_mul_self U
  calc
    (U.1.conjTranspose * ((U.1 * A) * U.1.conjTranspose)) * U.1 =
        ((U.1.conjTranspose * U.1) * A) *
          (U.1.conjTranspose * U.1) := by
      noncomm_ring
    _ = A := by rw [hunit]; simp

/-- Physical measurement/dephasing channel in the basis selected by `U`. -/
noncomputable def conjugatedComputationalBasisMeasurementChannel (K : ℕ)
    (U : Matrix.unitaryGroup (PauliBinaryWord K) ℂ)
    (A : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ) :
    Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ :=
  (U.1.conjTranspose *
    computationalBasisMeasurementChannel K
      ((U.1 * A) * U.1.conjTranspose)) * U.1

/-- A unitary lift turns literal Born dephasing into the exact symplectic
Z-hit indicator on each Pauli. -/
theorem conjugatedComputationalBasisMeasurementChannel_binaryPauli_of_lift
    (K : ℕ) (g : binarySymplecticGroup K)
    (U : Matrix.unitaryGroup (PauliBinaryWord K) ℂ)
    (hU : IsUnitaryPauliLift K g U) (p : PauliLabel K) :
    conjugatedComputationalBasisMeasurementChannel K U
        (binaryPauliMatrix K p) =
      if (g.1 p).1 = 0 then binaryPauliMatrix K p else 0 := by
  obtain ⟨phase, hphase, hconj⟩ := hU p
  unfold conjugatedComputationalBasisMeasurementChannel
  rw [hconj, computationalBasisMeasurementChannel_smul,
    computationalBasisMeasurementChannel_binaryPauliMatrix]
  by_cases hz : (g.1 p).1 = 0
  · rw [if_pos hz, if_pos hz]
    exact unitary_unsandwich U hconj
  · rw [if_neg hz, if_neg hz]
    simp

/-- The chosen concrete unitary lift realizes the exact per-gate Pauli hit
indicator. -/
theorem conjugatedBinaryTransvectionMeasurementChannel_binaryPauli
    (K : ℕ) (g : binaryTransvectionGroup K) (p : PauliLabel K) :
    conjugatedComputationalBasisMeasurementChannel K
        (binaryTransvectionUnitaryLift K g) (binaryPauliMatrix K p) =
      if (g.1.1 p).1 = 0 then binaryPauliMatrix K p else 0 :=
  conjugatedComputationalBasisMeasurementChannel_binaryPauli_of_lift K g.1
    (binaryTransvectionUnitaryLift K g)
    (binaryTransvectionUnitaryLift_spec K g) p

/-! ## Uniform finite physical ensemble -/

/-- Uniform average of the literal conjugated Born-dephasing channels over
the finite transvection-generated unitary ensemble. -/
noncomputable def averagedBinaryTransvectionMeasurementChannel (K : ℕ)
    (A : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ) :
    Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ :=
  ((Fintype.card (binaryTransvectionGroup K) : ℂ)⁻¹) •
    ∑ g : binaryTransvectionGroup K,
      conjugatedComputationalBasisMeasurementChannel K
        (binaryTransvectionUnitaryLift K g) A

/-- The uniform physical channel is Pauli diagonal, with eigenvalue equal
to the exact finite Z-hit ratio. -/
theorem averagedBinaryTransvectionMeasurementChannel_binaryPauli
    (K : ℕ) (p : PauliLabel K) :
    averagedBinaryTransvectionMeasurementChannel K
        (binaryPauliMatrix K p) =
      (((Fintype.card
          {g : binaryTransvectionGroup K // (g.1.1 p).1 = 0} : ℕ) : ℂ) /
        Fintype.card (binaryTransvectionGroup K)) •
          binaryPauliMatrix K p := by
  classical
  have hsum :
      (∑ g : binaryTransvectionGroup K,
        if (g.1.1 p).1 = 0 then binaryPauliMatrix K p else 0) =
      ((Fintype.card
          {g : binaryTransvectionGroup K // (g.1.1 p).1 = 0} : ℕ) : ℂ) •
        binaryPauliMatrix K p := by
    calc
      (∑ g : binaryTransvectionGroup K,
          if (g.1.1 p).1 = 0 then binaryPauliMatrix K p else 0) =
        ∑ g : binaryTransvectionGroup K,
          (if (g.1.1 p).1 = 0 then (1 : ℂ) else 0) •
            binaryPauliMatrix K p := by
          apply Finset.sum_congr rfl
          intro g _
          split_ifs <;> simp
      _ = (∑ g : binaryTransvectionGroup K,
          if (g.1.1 p).1 = 0 then (1 : ℂ) else 0) •
            binaryPauliMatrix K p := by
          rw [Finset.sum_smul]
      _ = ((Fintype.card
          {g : binaryTransvectionGroup K // (g.1.1 p).1 = 0} : ℕ) : ℂ) •
            binaryPauliMatrix K p := by
          rw [Finset.sum_boole, ← Fintype.card_subtype]
  unfold averagedBinaryTransvectionMeasurementChannel
  simp_rw [conjugatedBinaryTransvectionMeasurementChannel_binaryPauli]
  rw [hsum, smul_smul]
  apply congrArg (fun c : ℂ ↦ c • binaryPauliMatrix K p)
  rw [div_eq_mul_inv]
  ring

/-- For every nonidentity Pauli, the literal averaged physical channel has
the exact Clifford eigenvalue `1 / (2^K + 1)`. -/
theorem averagedBinaryTransvectionMeasurementChannel_binaryPauli_nonzero
    {K : ℕ} (hK : 0 < K) {p : PauliLabel K} (hp : p ≠ 0) :
    averagedBinaryTransvectionMeasurementChannel K
        (binaryPauliMatrix K p) =
      (1 / ((2 : ℂ) ^ K + 1)) • binaryPauliMatrix K p := by
  rw [averagedBinaryTransvectionMeasurementChannel_binaryPauli]
  have hreal := uniform_binaryTransvectionGroup_z_probability hK
    (⟨p, hp⟩ : NonidentityPauliLabel K)
  have hcard :
      Fintype.card
          {g : binaryTransvectionGroup K // (g.1.1 p).1 = 0} =
        Fintype.card
          {g : binaryTransvectionGroup K //
            (g • (⟨p, hp⟩ : NonidentityPauliLabel K)).1.1 = 0} := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquiv (Equiv.refl _) (by intro g; rfl)
  have hreal' :
      ((Fintype.card
          {g : binaryTransvectionGroup K // (g.1.1 p).1 = 0} : ℕ) : ℝ) /
          Fintype.card (binaryTransvectionGroup K) =
        1 / ((2 : ℝ) ^ K + 1) := by
    rw [hcard]
    exact hreal
  have hcomplex :
      ((Fintype.card
          {g : binaryTransvectionGroup K // (g.1.1 p).1 = 0} : ℕ) : ℂ) /
          Fintype.card (binaryTransvectionGroup K) =
        1 / ((2 : ℂ) ^ K + 1) := by
    have hc := congrArg (fun x : ℝ ↦ (x : ℂ)) hreal'
    push_cast at hc
    exact hc
  rw [hcomplex]

end TomographyOracleCore
