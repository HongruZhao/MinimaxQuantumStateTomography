import TomographyOracleCore.BinaryCliffordFiniteThirdMoment
import TomographyOracleCore.FiniteUnitaryProjectiveThirdMomentBridge
import TomographyOracleCore.PositiveObservableVariance
import TomographyOracleCore.UnitaryHaarSphereOrbit
import TomographyOracleCore.PhysicalHaarOneCopyPointwise
import TomographyOracleCore.HaarBornScoreMoments
import TomographyOracleCore.DensityCompact

namespace TomographyOracleCore

open MeasureTheory Metric Set MatrixReduction
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
  InnerProductSpace ENNReal Kronecker

noncomputable section

/-!
# Relative third moments imply the finite-projective overlap bound

This module gives the literal consumer bridge from relative completely-positive
order of the finite-unitary third twirl to the cubic overlap used by the
finite-unitary projective score.  Both twirls below are actual conjugation
twirls on the three-replica matrix algebra; no scalar moment bound is included
in their definitions.
-/

section TensorAlgebra

variable {ι : Type*} [Fintype ι]

/-- The concrete triple tensor is the nested Kronecker product. -/
theorem matrixTensorThree_eq_kronecker
    (A B C : Matrix ι ι ℂ) :
    matrixTensorThree A B C = A ⊗ₖ (B ⊗ₖ C) := by
  ext x y
  simp [matrixTensorThree, Matrix.kronecker_apply, mul_assoc]

/-- Positivity is preserved by the concrete three-fold tensor product. -/
theorem Matrix.PosSemidef.matrixTensorThree
    {A B C : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hC : C.PosSemidef) :
    (matrixTensorThree A B C).PosSemidef := by
  rw [matrixTensorThree_eq_kronecker]
  exact hA.kronecker (hB.kronecker hC)

/-- Trace factors across the concrete three-fold tensor product. -/
theorem matrixTensorThree_trace
    (A B C : Matrix ι ι ℂ) :
    (matrixTensorThree A B C).trace = A.trace * B.trace * C.trace := by
  rw [matrixTensorThree_eq_kronecker, Matrix.trace_kronecker,
    Matrix.trace_kronecker]
  ring

/-- A trace pairing of two simple triple tensors factors into three traces. -/
theorem matrixTensorThree_mul_trace
    (A B C X Y Z : Matrix ι ι ℂ) :
    (matrixTensorThree A B C * matrixTensorThree X Y Z).trace =
      (A * X).trace * (B * Y).trace * (C * Z).trace := by
  rw [← matrixTensorThree_mul, matrixTensorThree_trace]

end TensorAlgebra

section ThirdTwirl

variable {D : ℕ}

/-- Three-replica matrix space for a `D`-dimensional system. -/
abbrev FiniteUnitaryThirdSpace (D : ℕ) :=
  Matrix (TripleIndex (Fin D)) (TripleIndex (Fin D)) ℂ

/-- Tensor cube of an arbitrary `D`-dimensional unitary. -/
noncomputable def unitaryTensorCubeGeneral
    (U : Matrix.unitaryGroup (Fin D) ℂ) : FiniteUnitaryThirdSpace D :=
  matrixTensorThree U.1 U.1 U.1

/-- Ordinary three-replica conjugation by one unitary. -/
noncomputable def unitaryThirdConjugationGeneral
    (U : Matrix.unitaryGroup (Fin D) ℂ)
    (X : FiniteUnitaryThirdSpace D) : FiniteUnitaryThirdSpace D :=
  (unitaryTensorCubeGeneral U * X) *
    (unitaryTensorCubeGeneral U).conjTranspose

theorem unitaryThirdConjugationGeneral_add
    (U : Matrix.unitaryGroup (Fin D) ℂ)
    (X Y : FiniteUnitaryThirdSpace D) :
    unitaryThirdConjugationGeneral U (X + Y) =
      unitaryThirdConjugationGeneral U X +
        unitaryThirdConjugationGeneral U Y := by
  unfold unitaryThirdConjugationGeneral
  rw [Matrix.mul_add, Matrix.add_mul]

theorem unitaryThirdConjugationGeneral_smul
    (U : Matrix.unitaryGroup (Fin D) ℂ) (c : ℂ)
    (X : FiniteUnitaryThirdSpace D) :
    unitaryThirdConjugationGeneral U (c • X) =
      c • unitaryThirdConjugationGeneral U X := by
  unfold unitaryThirdConjugationGeneral
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- Conjugation of a simple triple tensor factors slot by slot. -/
theorem unitaryThirdConjugationGeneral_matrixTensorThree
    (U : Matrix.unitaryGroup (Fin D) ℂ)
    (A B C : Matrix (Fin D) (Fin D) ℂ) :
    unitaryThirdConjugationGeneral U (matrixTensorThree A B C) =
      matrixTensorThree
        (U.1 * A * U.1.conjTranspose)
        (U.1 * B * U.1.conjTranspose)
        (U.1 * C * U.1.conjTranspose) := by
  unfold unitaryThirdConjugationGeneral unitaryTensorCubeGeneral
  rw [← matrixTensorThree_conjTranspose]
  rw [← matrixTensorThree_mul, ← matrixTensorThree_mul]

/-- The normalized third conjugation twirl of a nonempty finite ensemble. -/
noncomputable def finiteUnitaryThirdTwirlLinearMap
    {E : Type*} [Fintype E] [Nonempty E]
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) :
    FiniteUnitaryThirdSpace D →ₗ[ℂ] FiniteUnitaryThirdSpace D where
  toFun X := ((Fintype.card E : ℂ)⁻¹) •
    ∑ e : E, unitaryThirdConjugationGeneral (U e) X
  map_add' X Y := by
    simp_rw [unitaryThirdConjugationGeneral_add, Finset.sum_add_distrib]
    module
  map_smul' c X := by
    simp_rw [unitaryThirdConjugationGeneral_smul, ← Finset.smul_sum]
    simp [smul_smul, mul_comm]

theorem continuous_unitaryTensorCubeGeneral (D : ℕ) :
    Continuous (unitaryTensorCubeGeneral (D := D)) := by
  apply continuous_matrix
  intro x y
  change Continuous (fun U : Matrix.unitaryGroup (Fin D) ℂ ↦
    U.1 x.1 y.1 * U.1 x.2.1 y.2.1 * U.1 x.2.2 y.2.2)
  have hentry (i j : Fin D) :
      Continuous (fun U : Matrix.unitaryGroup (Fin D) ℂ ↦ U.1 i j) :=
    (continuous_apply_apply i j).comp continuous_subtype_val
  exact ((hentry x.1 y.1).mul (hentry x.2.1 y.2.1)).mul
    (hentry x.2.2 y.2.2)

theorem continuous_unitaryThirdConjugationGeneral
    (D : ℕ) (X : FiniteUnitaryThirdSpace D) :
    Continuous (fun U : Matrix.unitaryGroup (Fin D) ℂ ↦
      unitaryThirdConjugationGeneral U X) := by
  have hcube := continuous_unitaryTensorCubeGeneral D
  have hstar : Continuous
      (fun U : Matrix.unitaryGroup (Fin D) ℂ ↦
        (unitaryTensorCubeGeneral U).conjTranspose) := by
    apply continuous_matrix
    intro i j
    change Continuous (fun U ↦ star (unitaryTensorCubeGeneral U j i))
    exact Complex.continuous_conj.comp
      ((continuous_apply_apply j i).comp hcube)
  exact (hcube.matrix_mul continuous_const).matrix_mul hstar

theorem integrable_unitaryThirdConjugationGeneral
    (D : ℕ) (X : FiniteUnitaryThirdSpace D) :
    Integrable (fun U : Matrix.unitaryGroup (Fin D) ℂ ↦
      unitaryThirdConjugationGeneral U X)
      (unitaryHaarProbability D) := by
  simpa [IntegrableOn] using
    (continuous_unitaryThirdConjugationGeneral D X).continuousOn.integrableOn_compact
      (μ := unitaryHaarProbability D) isCompact_univ

/-- Literal normalized Haar third conjugation twirl. -/
noncomputable def unitaryHaarThirdTwirlLinearMap (D : ℕ) :
    FiniteUnitaryThirdSpace D →ₗ[ℂ] FiniteUnitaryThirdSpace D where
  toFun X := ∫ U, unitaryThirdConjugationGeneral U X
    ∂unitaryHaarProbability D
  map_add' X Y := by
    simp_rw [unitaryThirdConjugationGeneral_add]
    exact integral_add
      (integrable_unitaryThirdConjugationGeneral D X)
      (integrable_unitaryThirdConjugationGeneral D Y)
  map_smul' c X := by
    simp_rw [unitaryThirdConjugationGeneral_smul]
    exact integral_smul c _

end ThirdTwirl

section PositiveObjects

variable {D : ℕ}

/-- Sum of the tensor cubes of the computational rank-one projectors. -/
noncomputable def computationalDiagonalTensorCube (D : ℕ) :
    FiniteUnitaryThirdSpace D :=
  ∑ b : Fin D, matrixTensorThree
    (finiteComputationalBasisProjector b)
    (finiteComputationalBasisProjector b)
    (finiteComputationalBasisProjector b)

theorem computationalDiagonalTensorCube_posSemidef (D : ℕ) :
    (computationalDiagonalTensorCube D).PosSemidef := by
  classical
  unfold computationalDiagonalTensorCube
  simpa using Matrix.posSemidef_sum (Finset.univ : Finset (Fin D))
    (fun b hb ↦
      Matrix.PosSemidef.matrixTensorThree
        (finiteComputationalBasisProjector_posSemidef b)
        (finiteComputationalBasisProjector_posSemidef b)
        (finiteComputationalBasisProjector_posSemidef b))

/-- Positive input tensor carrying the density and two copies of the test
direction. -/
noncomputable def densityDirectionTensor
    (ρ : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) : FiniteUnitaryThirdSpace D :=
  matrixTensorThree ρ.matrix
    (haarDirectionProjector u) (haarDirectionProjector u)

theorem densityDirectionTensor_posSemidef
    (ρ : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) :
    (densityDirectionTensor ρ u).PosSemidef := by
  exact Matrix.PosSemidef.matrixTensorThree ρ.posSemidef
    (haarDirectionProjector_posSemidef u)
    (haarDirectionProjector_posSemidef u)

/-- Trace pairing on a matrix algebra indexed by an arbitrary finite type. -/
noncomputable def cpTracePairingOn
    {ι : Type*} [Fintype ι]
    (test : Matrix ι ι ℂ)
    (Phi : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (input : Matrix ι ι ℂ) : ℝ :=
  (test * Phi input).trace.re

/-- Generic-index positivity of the trace pairing. -/
theorem trace_mul_re_nonnegative_of_posSemidef_on
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  obtain ⟨X, hX⟩ :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [hX]
  have htrace :
      ((star X * X) * B).trace = (X * B * star X).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  rw [htrace, Matrix.star_eq_conjTranspose]
  exact (Complex.nonneg_iff.mp
    (hB.mul_mul_conjTranspose_same X).trace_nonneg).1

/-- Generic-index form of the positive trace-test consequence of relative
CP order. -/
theorem RelativeCPApproximation.cpTracePairingOn_le_upper
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {epsilon : ℝ}
    {ensemble haar : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ}
    (h : RelativeCPApproximation epsilon ensemble haar)
    {input test : Matrix ι ι ℂ}
    (hinput : input.PosSemidef) (htest : test.PosSemidef) :
    cpTracePairingOn test ensemble input ≤
      (1 + epsilon) * cpTracePairingOn test haar input := by
  have hmatrix := h.apply_le_upper hinput.nonneg
  have hdiff :
      ((((1 + epsilon : ℝ) : ℂ) • haar) input - ensemble input).PosSemidef :=
    hmatrix
  have hnonneg := trace_mul_re_nonnegative_of_posSemidef_on
    test ((((1 + epsilon : ℝ) : ℂ) • haar) input - ensemble input)
    htest hdiff
  have htrace :
      (test * ((((1 + epsilon : ℝ) : ℂ) • haar) input)).trace.re -
          (test * ensemble input).trace.re ≥ 0 := by
    simpa [Matrix.mul_sub, Matrix.trace_sub] using hnonneg
  simpa [cpTracePairingOn, mul_assoc] using htrace

end PositiveObjects

section FinitePairing

variable {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]

/-- Moving ordinary unitary conjugation through a trace pairing produces the
inverse-conjugated test. -/
theorem trace_mul_unitary_conjugation
    (U : Matrix.unitaryGroup (Fin D) ℂ)
    (A B : Matrix (Fin D) (Fin D) ℂ) :
    (A * (U.1 * B * U.1.conjTranspose)).trace =
      (B * (U.1.conjTranspose * A * U.1)).trace := by
  calc
    (A * (U.1 * B * U.1.conjTranspose)).trace =
        ((U.1 * B * U.1.conjTranspose) * A).trace :=
      Matrix.trace_mul_comm _ _
    _ = (U.1 * (B * U.1.conjTranspose * A)).trace := by
      simp only [mul_assoc]
    _ = ((B * U.1.conjTranspose * A) * U.1).trace :=
      Matrix.trace_mul_comm _ _
    _ = (B * (U.1.conjTranspose * A * U.1)).trace := by
      simp only [mul_assoc]

/-- One computational-basis summand of the third-twirl trace test is exactly
the physical Born-weighted squared overlap. -/
theorem computationalTensorCubeTerm_pairing
    (U : Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) (b : Fin D) :
    (matrixTensorThree
        (finiteComputationalBasisProjector b)
        (finiteComputationalBasisProjector b)
        (finiteComputationalBasisProjector b) *
      unitaryThirdConjugationGeneral U (densityDirectionTensor ρ u)).trace.re =
      ((haarDirectionProjector u *
        finiteUnitaryMeasurementProjector U b).trace.re) ^ 2 *
      (ρ.matrix * finiteUnitaryMeasurementProjector U b).trace.re := by
  unfold densityDirectionTensor
  rw [unitaryThirdConjugationGeneral_matrixTensorThree,
    matrixTensorThree_mul_trace]
  rw [trace_mul_unitary_conjugation,
    trace_mul_unitary_conjugation]
  change
    ((ρ.matrix * finiteUnitaryMeasurementProjector U b).trace *
      (haarDirectionProjector u *
        finiteUnitaryMeasurementProjector U b).trace *
      (haarDirectionProjector u *
        finiteUnitaryMeasurementProjector U b).trace).re = _
  rw [trace_mul_eq_re_of_isHermitian ρ.matrix
      (finiteUnitaryMeasurementProjector U b) ρ.isHermitian
      (finiteUnitaryMeasurementProjector_posSemidef U b).isHermitian,
    trace_mul_eq_re_of_isHermitian (haarDirectionProjector u)
      (finiteUnitaryMeasurementProjector U b)
      (haarDirectionProjector_isHermitian u)
      (finiteUnitaryMeasurementProjector_posSemidef U b).isHermitian]
  simp
  ring

/-- The literal finite third-twirl trace pairing equals the physical cubic
overlap, with the same uniform ensemble normalization. -/
theorem finiteUnitaryProjectiveWeightedOverlapSquare_eq_cpTracePairingOn
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) :
    finiteUnitaryProjectiveWeightedOverlapSquare U ρ u =
      cpTracePairingOn (computationalDiagonalTensorCube D)
        (finiteUnitaryThirdTwirlLinearMap U) (densityDirectionTensor ρ u) := by
  classical
  have hcard : (Fintype.card E : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcoeffENN :
      ((Fintype.card E : ℕ) : ℝ≥0∞)⁻¹.toReal =
        (Fintype.card E : ℝ)⁻¹ := by
    rw [ENNReal.toReal_inv]
    simp
  have hcoeffC :
      (Fintype.card E : ℂ)⁻¹ =
        (((Fintype.card E : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_inv]
    congr 1
  unfold finiteUnitaryProjectiveWeightedOverlapSquare cpTracePairingOn
    computationalDiagonalTensorCube finiteUnitaryThirdTwirlLinearMap
  simp only [smul_eq_mul, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Matrix.mul_smul, Matrix.trace_smul]
  simp_rw [Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum]
  rw [hcoeffENN, hcoeffC]
  change (Fintype.card E : ℝ)⁻¹ *
      (∑ e : E, ∑ b : Fin D,
        ((haarDirectionProjector u *
          finiteUnitaryMeasurementProjector (U e) b).trace.re) ^ 2 *
        (ρ.matrix * finiteUnitaryMeasurementProjector (U e) b).trace.re) =
    (((Fintype.card E : ℝ)⁻¹ : ℝ) •
      (∑ b : Fin D, ∑ e : E,
        (matrixTensorThree
            (finiteComputationalBasisProjector b)
            (finiteComputationalBasisProjector b)
            (finiteComputationalBasisProjector b) *
          unitaryThirdConjugationGeneral (U e)
            (densityDirectionTensor ρ u)).trace)).re
  rw [Complex.smul_re]
  simp only [smul_eq_mul, Complex.re_sum]
  rw [Finset.sum_comm]
  simp_rw [computationalTensorCubeTerm_pairing]

end FinitePairing

section HaarPairing

variable {D : ℕ}

/-- Continuous complex-linear trace pairing with a fixed left factor. -/
noncomputable def matrixTraceMulCLM
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) : Matrix ι ι ℂ →L[ℂ] ℂ :=
  ∑ i : ι, ∑ j : ι, A i j • complexMatrixEntryCLM ι j i

@[simp]
theorem matrixTraceMulCLM_apply
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (A X : Matrix ι ι ℂ) :
    matrixTraceMulCLM A X = (A * X).trace := by
  simp only [matrixTraceMulCLM, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp_rw [complexMatrixEntryCLM_apply]
  simp [Matrix.trace, Matrix.mul_apply]

/-- A fixed matrix trace pairing commutes with a Bochner integral. -/
theorem trace_mul_integral
    {ι Ω : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [MeasurableSpace Ω]
    (A : Matrix ι ι ℂ) (f : Ω → Matrix ι ι ℂ)
    (mu : Measure Ω) (hf : Integrable f mu) :
    (A * (∫ x, f x ∂mu)).trace =
      ∫ x, (A * f x).trace ∂mu := by
  have h := (matrixTraceMulCLM A).integral_comp_comm hf
  simpa using h.symm

/-- The Haar third-twirl trace pairing is the Haar integral of the literal
Born-weighted cubic overlap summed over computational outcomes. -/
theorem cpTracePairingOn_unitaryHaarThirdTwirl_eq_integral
    (hD : 0 < D)
    (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) :
    cpTracePairingOn (computationalDiagonalTensorCube D)
        (unitaryHaarThirdTwirlLinearMap D) (densityDirectionTensor rho u) =
      ∫ U : Matrix.unitaryGroup (Fin D) ℂ,
        ∑ b : Fin D,
          ((haarDirectionProjector u *
            finiteUnitaryMeasurementProjector U b).trace.re) ^ 2 *
          (rho.matrix * finiteUnitaryMeasurementProjector U b).trace.re
        ∂unitaryHaarProbability D := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  let test := computationalDiagonalTensorCube D
  let input := densityDirectionTensor rho u
  let f : Matrix.unitaryGroup (Fin D) ℂ → FiniteUnitaryThirdSpace D :=
    fun U ↦ unitaryThirdConjugationGeneral U input
  have hf : Integrable f (unitaryHaarProbability D) :=
    integrable_unitaryThirdConjugationGeneral D input
  have hscalar : Integrable
      (fun U ↦ (test * f U).trace) (unitaryHaarProbability D) :=
    by simpa only [matrixTraceMulCLM_apply] using
      (matrixTraceMulCLM test).integrable_comp hf
  unfold cpTracePairingOn unitaryHaarThirdTwirlLinearMap
  change (test * (∫ U, f U ∂unitaryHaarProbability D)).trace.re = _
  rw [trace_mul_integral test f (unitaryHaarProbability D) hf]
  have hre :
      (∫ U, (test * f U).trace ∂unitaryHaarProbability D).re =
        ∫ U, (test * f U).trace.re ∂unitaryHaarProbability D := by
    have h := integral_re hscalar
    simpa only [RCLike.re_eq_complex_re] using h.symm
  rw [hre]
  apply integral_congr_ae
  filter_upwards [] with U
  dsimp only [test, f, input]
  unfold computationalDiagonalTensorCube
  rw [Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
  simp_rw [computationalTensorCubeTerm_pairing]

end HaarPairing

section HaarProjectiveEvaluation

variable {D : ℕ}

/-- The `b`th computational basis vector, regarded as a point of the complex
unit sphere. -/
noncomputable def computationalBasisSphere (b : Fin D) :
    sphere (0 : EuclideanSpace ℂ (Fin D)) 1 :=
  ⟨EuclideanSpace.single b 1, by
    simp [Metric.mem_sphere, dist_zero_right]⟩

/-- A projective measurement outcome is the rank-one projector of the
inverse-oriented unitary orbit of its computational basis vector. -/
theorem finiteUnitaryMeasurementProjector_eq_complexSphereProjector_inverseOrbit
    (U : Matrix.unitaryGroup (Fin D) ℂ) (b : Fin D) :
    finiteUnitaryMeasurementProjector U b =
      complexSphereProjector
        (inverseUnitarySphereOrbit D (computationalBasisSphere b) U) := by
  rw [finiteUnitaryMeasurementProjector_eq_complexSphereProjector]
  congr 1
  apply Subtype.ext
  apply PiLp.ext
  intro i
  simp [finiteUnitaryMeasurementVector, inverseUnitarySphereOrbit,
    unitarySphereAction, unitaryVectorAction, computationalBasisSphere,
    Matrix.mulVec, dotProduct]

/-- For each fixed computational outcome, a Haar unitary produces the
literal complex-projective Haar law. -/
theorem map_finiteUnitaryMeasurementProjector_unitaryHaarProbability
    (hD : 0 < D) (b : Fin D) :
    Measure.map
        (fun U : Matrix.unitaryGroup (Fin D) ℂ ↦
          finiteUnitaryMeasurementProjector U b)
        (unitaryHaarProbability D) =
      complexProjectiveHaarLaw (Fin D) := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  simp_rw [show (fun U : Matrix.unitaryGroup (Fin D) ℂ ↦
      finiteUnitaryMeasurementProjector U b) =
      fun U ↦ complexSphereProjector
        (inverseUnitarySphereOrbit D (computationalBasisSphere b) U) by
    funext U
    exact
      finiteUnitaryMeasurementProjector_eq_complexSphereProjector_inverseOrbit
        U b]
  calc
    Measure.map
        (fun U : Matrix.unitaryGroup (Fin D) ℂ ↦
          complexSphereProjector
            (inverseUnitarySphereOrbit D (computationalBasisSphere b) U))
        (unitaryHaarProbability D) =
      Measure.map complexSphereProjector
        (Measure.map
          (inverseUnitarySphereOrbit D (computationalBasisSphere b))
          (unitaryHaarProbability D)) := by
        rw [Measure.map_map]
        · rfl
        · exact measurable_complexSphereProjector
        · exact measurable_inverseUnitarySphereOrbit D _
    _ = Measure.map complexSphereProjector
        (complexUnitSphereHaarLaw (Fin D)) := by
      rw [map_inverseUnitarySphereOrbit_unitaryHaarProbability D hD]
    _ = complexProjectiveHaarLaw (Fin D) := by
      rfl

/-- Cubic rank-one integrand: two test-direction overlaps times one Born
weight. -/
noncomputable def rankOneBornCubicIntegrand
    (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D))
    (P : Matrix (Fin D) (Fin D) ℂ) : ℝ :=
  ((haarDirectionProjector u * P).trace.re) ^ 2 *
    (rho.matrix * P).trace.re

theorem continuous_rankOneBornCubicIntegrand
    (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) :
    Continuous (rankOneBornCubicIntegrand rho u) := by
  unfold rankOneBornCubicIntegrand
  fun_prop

theorem integrable_rankOneBornCubicIntegrand_projective
    (hD : 0 < D) (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) :
    Integrable (rankOneBornCubicIntegrand rho u)
      (complexProjectiveHaarLaw (Fin D)) := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  have h := integrable_complexProjectiveHaar_trace_mul_three_re
    (Fin D) rho.matrix (haarDirectionProjector u)
      (haarDirectionProjector u) rho.isHermitian
      (haarDirectionProjector_isHermitian u)
      (haarDirectionProjector_isHermitian u)
  apply h.congr
  filter_upwards [] with P
  unfold rankOneBornCubicIntegrand
  ring

theorem integrable_rankOneBornCubicIntegrand_measurement
    (hD : 0 < D) (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) (b : Fin D) :
    Integrable
      (fun U : Matrix.unitaryGroup (Fin D) ℂ ↦
        rankOneBornCubicIntegrand rho u
          (finiteUnitaryMeasurementProjector U b))
      (unitaryHaarProbability D) := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  let f := fun U : Matrix.unitaryGroup (Fin D) ℂ ↦
    finiteUnitaryMeasurementProjector U b
  let g := rankOneBornCubicIntegrand rho u
  have hf : Measurable f := by
    rw [show f = fun U ↦ complexSphereProjector
        (inverseUnitarySphereOrbit D (computationalBasisSphere b) U) by
      funext U
      exact
        finiteUnitaryMeasurementProjector_eq_complexSphereProjector_inverseOrbit
          U b]
    exact measurable_complexSphereProjector.comp
      (measurable_inverseUnitarySphereOrbit D _)
  have hg : AEStronglyMeasurable g
      (Measure.map f (unitaryHaarProbability D)) := by
    exact (continuous_rankOneBornCubicIntegrand rho u).aestronglyMeasurable
  apply (integrable_map_measure hg hf.aemeasurable).1
  rw [map_finiteUnitaryMeasurementProjector_unitaryHaarProbability hD b]
  exact integrable_rankOneBornCubicIntegrand_projective hD rho u

theorem integral_rankOneBornCubicIntegrand_measurement
    (hD : 0 < D) (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) (b : Fin D) :
    (∫ U : Matrix.unitaryGroup (Fin D) ℂ,
        rankOneBornCubicIntegrand rho u
          (finiteUnitaryMeasurementProjector U b)
        ∂unitaryHaarProbability D) =
      ∫ P, rankOneBornCubicIntegrand rho u P
        ∂complexProjectiveHaarLaw (Fin D) := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  let f := fun U : Matrix.unitaryGroup (Fin D) ℂ ↦
    finiteUnitaryMeasurementProjector U b
  let g := rankOneBornCubicIntegrand rho u
  have hf : Measurable f := by
    rw [show f = fun U ↦ complexSphereProjector
        (inverseUnitarySphereOrbit D (computationalBasisSphere b) U) by
      funext U
      exact
        finiteUnitaryMeasurementProjector_eq_complexSphereProjector_inverseOrbit
          U b]
    exact measurable_complexSphereProjector.comp
      (measurable_inverseUnitarySphereOrbit D _)
  calc
    (∫ U : Matrix.unitaryGroup (Fin D) ℂ, g (f U)
        ∂unitaryHaarProbability D) =
      ∫ P, g P ∂Measure.map f (unitaryHaarProbability D) := by
        symm
        exact integral_map hf.aemeasurable
          (continuous_rankOneBornCubicIntegrand rho u).aestronglyMeasurable
    _ = ∫ P, g P ∂complexProjectiveHaarLaw (Fin D) := by
      rw [map_finiteUnitaryMeasurementProjector_unitaryHaarProbability hD b]

/-- The Haar third-twirl pairing is dimension times the projective-Haar
cubic rank-one integral. -/
theorem cpTracePairingOn_unitaryHaarThirdTwirl_eq_card_mul_projective
    (hD : 0 < D) (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) :
    cpTracePairingOn (computationalDiagonalTensorCube D)
        (unitaryHaarThirdTwirlLinearMap D) (densityDirectionTensor rho u) =
      (D : ℝ) *
        ∫ P, rankOneBornCubicIntegrand rho u P
          ∂complexProjectiveHaarLaw (Fin D) := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  rw [cpTracePairingOn_unitaryHaarThirdTwirl_eq_integral hD rho u]
  change (∫ U : Matrix.unitaryGroup (Fin D) ℂ,
      ∑ b : Fin D, rankOneBornCubicIntegrand rho u
        (finiteUnitaryMeasurementProjector U b)
      ∂unitaryHaarProbability D) = _
  rw [integral_finsetSum]
  · simp_rw [integral_rankOneBornCubicIntegrand_measurement hD rho u]
    simp
  · intro b hb
    exact integrable_rankOneBornCubicIntegrand_measurement hD rho u b

/-- Exact evaluation of the positive Haar third-twirl trace pairing. -/
theorem cpTracePairingOn_unitaryHaarThirdTwirl_exact
    (hD : 0 < D) (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1) :
    cpTracePairingOn (computationalDiagonalTensorCube D)
        (unitaryHaarThirdTwirlLinearMap D) (densityDirectionTensor rho u) =
      (2 + 4 * (rho.matrix * haarDirectionProjector u).trace.re) /
        (((D : ℝ) + 1) * ((D : ℝ) + 2)) := by
  rw [cpTracePairingOn_unitaryHaarThirdTwirl_eq_card_mul_projective
    hD rho u]
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  have hmoment :=
    card_mul_integral_complexProjectiveHaar_trace_mul_rankOne_sq_re
      (Fin D) rho.matrix (haarDirectionProjector u)
      rho.isHermitian (haarDirectionProjector_isHermitian u)
      rho.trace_eq_one (haarDirectionProjector_trace_eq_one u hu)
      (haarDirectionProjector_mul_self u hu)
  simpa [Fintype.card_fin, rankOneBornCubicIntegrand, pow_two,
    mul_comm, mul_left_comm, mul_assoc] using hmoment

/-- A density's overlap with a unit rank-one direction belongs to `[0,1]`. -/
theorem density_haarDirectionProjector_overlap_bounds
    (hD : 0 < D) (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1) :
    0 ≤ (rho.matrix * haarDirectionProjector u).trace.re ∧
      (rho.matrix * haarDirectionProjector u).trace.re ≤ 1 := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  constructor
  · exact trace_mul_re_nonnegative_of_posSemidef_on
      rho.matrix (haarDirectionProjector u) rho.posSemidef
      (haarDirectionProjector_posSemidef u)
  · have hdual :=
      norm_trace_mul_le_hermitianTraceNorm_mul_operatorNorm
        (haarDirectionProjector u) rho.matrix
        (haarDirectionProjector_isHermitian u)
    have htraceNorm :
        hermitianTraceNorm (haarDirectionProjector u)
            (haarDirectionProjector_isHermitian u) = 1 := by
      rw [hermitianTraceNorm_psd_eq_re_trace
        (haarDirectionProjector u) (haarDirectionProjector_posSemidef u),
        haarDirectionProjector_trace_eq_one u hu]
      norm_num
    have hnorm : ‖(rho.matrix * haarDirectionProjector u).trace‖ ≤ 1 := by
      calc
        ‖(rho.matrix * haarDirectionProjector u).trace‖ ≤
            hermitianTraceNorm (haarDirectionProjector u)
                (haarDirectionProjector_isHermitian u) *
              matrixOperatorNorm rho.matrix := hdual
        _ = matrixOperatorNorm rho.matrix := by rw [htraceNorm, one_mul]
        _ ≤ 1 := DensityCompact.density_matrix_operator_norm_le_one rho
    exact (Complex.re_le_norm _).trans hnorm

theorem cpTracePairingOn_unitaryHaarThirdTwirl_nonnegative
    (hD : 0 < D) (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1) :
    0 ≤ cpTracePairingOn (computationalDiagonalTensorCube D)
        (unitaryHaarThirdTwirlLinearMap D)
        (densityDirectionTensor rho u) := by
  rw [cpTracePairingOn_unitaryHaarThirdTwirl_exact hD rho u hu]
  have hov := density_haarDirectionProjector_overlap_bounds hD rho u hu
  apply div_nonneg
  · nlinarith [hov.1]
  · positivity

/-- The Haar third-twirl pairing is at most the exact constant `6` divided
by the third-moment dimension denominator. -/
theorem cpTracePairingOn_unitaryHaarThirdTwirl_le_six
    (hD : 0 < D) (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1) :
    cpTracePairingOn (computationalDiagonalTensorCube D)
        (unitaryHaarThirdTwirlLinearMap D)
        (densityDirectionTensor rho u) ≤
      6 / (((D : ℝ) + 1) * ((D : ℝ) + 2)) := by
  rw [cpTracePairingOn_unitaryHaarThirdTwirl_exact hD rho u hu]
  have hov := density_haarDirectionProjector_overlap_bounds hD rho u hu
  apply (div_le_div_iff_of_pos_right (by positivity)).2
  nlinarith

end HaarProjectiveEvaluation

section RelativeCPConsumer

variable {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]

/-- A literal relative-CP approximation of the finite third twirl to the
Haar third twirl, with relative error at most one, gives the exact positive
cubic-overlap estimate required by the shallow score theorem. -/
theorem finiteUnitaryProjectiveWeightedOverlapSquare_le_twelve_of_relativeCP
    (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1)
    (epsilon : ℝ) (hepsilon : epsilon ≤ 1)
    (hrelative : RelativeCPApproximation epsilon
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
      hrelative.cpTracePairingOn_le_upper
        (densityDirectionTensor_posSemidef rho u)
        (computationalDiagonalTensorCube_posSemidef D)
    _ ≤ 2 * cpTracePairingOn (computationalDiagonalTensorCube D)
          (unitaryHaarThirdTwirlLinearMap D)
          (densityDirectionTensor rho u) :=
      mul_le_mul_of_nonneg_right (by linarith) hhaar_nonnegative
    _ ≤ 2 * (6 / (((D : ℝ) + 1) * ((D : ℝ) + 2))) :=
      mul_le_mul_of_nonneg_left hhaar_le (by norm_num)
    _ = 12 / (((D : ℝ) + 1) * ((D : ℝ) + 2)) := by ring

/-- Direct score-second-moment consumer form of the relative-CP theorem. -/
theorem finiteUnitaryProjectiveScoreSecondMomentBoundThirteen_of_relativeCP
    (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1)
    (epsilon : ℝ) (hepsilon : epsilon ≤ 1)
    (hrelative : RelativeCPApproximation epsilon
      (finiteUnitaryThirdTwirlLinearMap U)
      (unitaryHaarThirdTwirlLinearMap D)) :
    FiniteUnitaryProjectiveScoreSecondMomentBoundThirteen U rho u := by
  apply
    finiteUnitaryProjectiveScoreSecondMomentBoundThirteen_of_weightedOverlapSquare_le
      hD U rho u
  simpa [Nat.cast_add, Nat.cast_one] using
    finiteUnitaryProjectiveWeightedOverlapSquare_le_twelve_of_relativeCP
      hD U rho u hu epsilon hepsilon hrelative

end RelativeCPConsumer

end

end TomographyOracleCore
