import TomographyOracleCore.FiniteUnitaryProjectiveRelativeThirdMoment

namespace TomographyOracleCore

open MatrixReduction PhysicalPOVM
open scoped CStarAlgebra ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

/-!
# C-star-matrix relative third-moment consumer

The constructive Cho--Kim gluing argument is carried out on `CStarMatrix`,
whose C-star algebra and spectral-order instances differ definitionally from
the scoped instances on the type copy `Matrix`.  This module transports only
the final positive trace test across that representation boundary.  It does
not add a mathematical assumption and does not identify the two typeclass
instances by definitional equality.
-/

/-- Positive semidefiniteness of an ordinary finite complex matrix is exactly
spectral nonnegativity of its `CStarMatrix` copy. -/
theorem cstarMatrix_nonneg_of_posSemidef
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {M : Matrix ι ι ℂ} (hM : M.PosSemidef) :
    0 ≤ (CStarMatrix.ofMatrix M : CStarMatrix ι ι ℂ) := by
  rw [StarOrderedRing.nonneg_iff]
  rw [← Matrix.nonneg_iff_posSemidef] at hM
  rw [StarOrderedRing.nonneg_iff] at hM
  exact hM

/-- Spectral nonnegativity of a `CStarMatrix` copy implies ordinary matrix
positive semidefiniteness. -/
theorem posSemidef_of_cstarMatrix_nonneg
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {M : Matrix ι ι ℂ}
    (hM : 0 ≤ (CStarMatrix.ofMatrix M : CStarMatrix ι ι ℂ)) :
    M.PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  rw [StarOrderedRing.nonneg_iff] at hM ⊢
  exact hM

/-- C-star-matrix version of the positive trace-test consequence of relative
CP order.  The input and test are stated in the ordinary matrix vocabulary
used by the tomography score calculation. -/
theorem RelativeCPApproximation.cpTracePairingOn_le_upper_cstarMatrix
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {epsilon : ℝ}
    {ensemble haar :
      CStarMatrix ι ι ℂ →ₗ[ℂ] CStarMatrix ι ι ℂ}
    (h : RelativeCPApproximation
      (A := CStarMatrix ι ι ℂ) epsilon ensemble haar)
    {input test : Matrix ι ι ℂ}
    (hinput : input.PosSemidef) (htest : test.PosSemidef) :
    cpTracePairingOn test ensemble input ≤
      (1 + epsilon) * cpTracePairingOn test haar input := by
  have hmatrix := h.apply_le_upper
    (cstarMatrix_nonneg_of_posSemidef hinput)
  have hdiff_nonneg :
      0 ≤ (CStarMatrix.ofMatrix
        ((((1 + epsilon : ℝ) : ℂ) • haar) input - ensemble input) :
          CStarMatrix ι ι ℂ) :=
    sub_nonneg.mpr hmatrix
  have hdiff :
      (CStarMatrix.ofMatrix.symm
        ((((1 + epsilon : ℝ) : ℂ) • haar) input -
          ensemble input)).PosSemidef :=
    posSemidef_of_cstarMatrix_nonneg hdiff_nonneg
  have hnonneg := trace_mul_re_nonnegative_of_posSemidef_on
    test (CStarMatrix.ofMatrix.symm
      ((((1 + epsilon : ℝ) : ℂ) • haar) input - ensemble input))
    htest hdiff
  have hsub :
      CStarMatrix.ofMatrix.symm
          ((((1 + epsilon : ℝ) : ℂ) • haar) input - ensemble input) =
        CStarMatrix.ofMatrix.symm
            ((((1 + epsilon : ℝ) : ℂ) • haar) input) -
          CStarMatrix.ofMatrix.symm (ensemble input) := by
    rfl
  have htrace :
      (test * CStarMatrix.ofMatrix.symm
          ((((1 + epsilon : ℝ) : ℂ) • haar) input)).trace.re -
        (test * CStarMatrix.ofMatrix.symm (ensemble input)).trace.re ≥ 0 := by
    rw [hsub] at hnonneg
    simpa [Matrix.mul_sub, Matrix.trace_sub] using hnonneg
  have hsmul :
      CStarMatrix.ofMatrix.symm
          ((((1 + epsilon : ℝ) : ℂ) • haar) input) =
        ((1 + epsilon : ℝ) : ℂ) •
          CStarMatrix.ofMatrix.symm (haar input) := by
    rfl
  change
    (test * CStarMatrix.ofMatrix.symm (ensemble input)).trace.re ≤
      (1 + epsilon) *
        (test * CStarMatrix.ofMatrix.symm (haar input)).trace.re
  rw [hsmul] at htrace
  simpa [Matrix.mul_smul, mul_assoc] using htrace

section RelativeCPConsumer

variable {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]

/-- A relative-CP comparison proved on the concrete `CStarMatrix` algebra
implies the same sharp cubic-overlap estimate used by the physical shallow
tomography upper bound. -/
theorem finiteUnitaryProjectiveWeightedOverlapSquare_le_twelve_of_relativeCP_cstarMatrix
    (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1)
    (epsilon : ℝ) (hepsilon : epsilon ≤ 1)
    (hrelative : RelativeCPApproximation
      (A := CStarMatrix (TripleIndex (Fin D))
        (TripleIndex (Fin D)) ℂ)
      epsilon
      (finiteUnitaryThirdTwirlLinearMap U)
      (unitaryHaarThirdTwirlLinearMap D)) :
    finiteUnitaryProjectiveWeightedOverlapSquare U rho u ≤
      12 / (((D : ℝ) + 1) * ((D : ℝ) + 2)) := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  have hhaar_nonnegative :=
    cpTracePairingOn_unitaryHaarThirdTwirl_nonnegative hD rho u hu
  have hhaar_le :=
    cpTracePairingOn_unitaryHaarThirdTwirl_le_six hD rho u hu
  calc
    finiteUnitaryProjectiveWeightedOverlapSquare U rho u =
        cpTracePairingOn (computationalDiagonalTensorCube D)
          (finiteUnitaryThirdTwirlLinearMap U)
          (densityDirectionTensor rho u) :=
      finiteUnitaryProjectiveWeightedOverlapSquare_eq_cpTracePairingOn
        U rho u
    _ ≤ (1 + epsilon) *
        cpTracePairingOn (computationalDiagonalTensorCube D)
          (unitaryHaarThirdTwirlLinearMap D)
          (densityDirectionTensor rho u) :=
      hrelative.cpTracePairingOn_le_upper_cstarMatrix
        (densityDirectionTensor_posSemidef rho u)
        (computationalDiagonalTensorCube_posSemidef D)
    _ ≤ 2 * cpTracePairingOn (computationalDiagonalTensorCube D)
          (unitaryHaarThirdTwirlLinearMap D)
          (densityDirectionTensor rho u) :=
      mul_le_mul_of_nonneg_right (by linarith) hhaar_nonnegative
    _ ≤ 2 * (6 / (((D : ℝ) + 1) * ((D : ℝ) + 2))) :=
      mul_le_mul_of_nonneg_left hhaar_le (by norm_num)
    _ = 12 / (((D : ℝ) + 1) * ((D : ℝ) + 2)) := by ring

end RelativeCPConsumer

end

end TomographyOracleCore
