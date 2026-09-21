import TomographyOracleCore.Revision.MatrixSolverChannel
import TomographyOracleCore.Candidate2FeasibilityRepair
import Mathlib.Analysis.Matrix.Order

/-!
# Feasibility repair from a checked entrywise rounding error

Unlike a weak-feasibility contract, the input here is an approximation to
an actual density matrix. Positivity of the shifted matrix and positivity
of its normalization denominator are derived, rather than assumed.
-/

namespace TomographyOracleCore.Revision.FinitePrecision

open MatrixReduction MatrixSolver Matrix Candidate2FeasibilityRepair
open scoped ComplexOrder InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def entryNormSum (A : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖

theorem entryNormSum_nonneg (A : Matrix ι ι ℂ) : 0 ≤ entryNormSum A := by
  unfold entryNormSum
  positivity

theorem norm_encode_le_entryNormSum (A : Matrix ι ι ℂ) :
    ‖encode A‖ ≤ entryNormSum A := by
  apply (sq_le_sq₀ (norm_nonneg _) (entryNormSum_nonneg A)).1
  rw [norm_encode_sq]
  have h := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := (Finset.univ : Finset (ι × ι)))
    (f := fun ij => ‖A ij.1 ij.2‖) (fun _ _ => norm_nonneg _)
  simpa [entryNormSum, Fintype.sum_prod_type] using h

theorem euclidean_norm_le_entry_sum (v : EuclideanSpace ℂ ι) :
    ‖v‖ ≤ ∑ i, ‖v i‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).1
  rw [EuclideanSpace.norm_sq_eq]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)

theorem operatorNorm_le_entryNormSum (A : Matrix ι ι ℂ) :
    matrixOperatorNorm A ≤ entryNormSum A := by
  change ‖A.toEuclideanLin.toContinuousLinearMap‖ ≤ _
  apply A.toEuclideanLin.toContinuousLinearMap.opNorm_le_bound (entryNormSum_nonneg A)
  intro v
  calc
    ‖A.toEuclideanLin v‖ ≤ ∑ i, ‖(A.toEuclideanLin v) i‖ := euclidean_norm_le_entry_sum _
    _ ≤ ∑ i, ∑ j, ‖A i j‖ * ‖v j‖ := by
      apply Finset.sum_le_sum
      intro i hi
      change ‖∑ j, A i j * v j‖ ≤ _
      simpa only [norm_mul] using norm_sum_le (s := Finset.univ) (fun j => A i j * v j)
    _ ≤ ∑ i, ∑ j, ‖A i j‖ * ‖v‖ := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le v j) (norm_nonneg _)
    _ = entryNormSum A * ‖v‖ := by simp [entryNormSum, Finset.sum_mul]

theorem abs_trace_re_le_entryNormSum (A : Matrix ι ι ℂ) :
    |A.trace.re| ≤ entryNormSum A := by
  calc
    |A.trace.re| ≤ ‖A.trace‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ entryNormSum A := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.single_le_sum (fun j _ => norm_nonneg (A i j)) (Finset.mem_univ i)

/-- The Frobenius norm of a Hermitian error is at most its trace norm. -/
theorem norm_encode_le_hermitianTraceNorm
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    ‖encode A‖ ≤ hermitianTraceNorm A hA := by
  apply (sq_le_sq₀ (norm_nonneg _) (hermitianTraceNorm_nonneg A hA)).1
  rw [norm_encode_sq_eq_trace, hA.eq, trace_sq_eq_hermitianFrobeniusSq A hA]
  have h := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := (Finset.univ : Finset ι))
    (f := fun i => |hA.eigenvalues i|) (fun _ _ => abs_nonneg _)
  simpa [hermitianTraceNorm, hermitianFrobeniusSq, ← Complex.ofReal_pow] using h

/-- A Hermitian approximation within operator distance `eta` of a PSD
matrix becomes PSD after adding `eta I`. -/
theorem shifted_approximation_posSemidef
    (H X : Matrix ι ι ℂ) (hH : H.IsHermitian) (hX : X.PosSemidef)
    (eta : ℝ) (hclose : matrixOperatorNorm (H - X) ≤ eta) :
    (shiftedMatrix H eta).PosSemidef := by
  open scoped MatrixOrder Matrix.Norms.L2Operator in
    have hE : (H - X).IsHermitian := hH.sub hX.isHermitian
    have hnorm : ‖H - X‖ ≤ eta := hclose
    have hgap : ((eta - ‖H - X‖) • (1 : Matrix ι ι ℂ)).PosSemidef :=
      PosSemidef.one.smul (sub_nonneg.mpr hnorm)
    have hscalar : (‖H - X‖ : ℝ) • (1 : Matrix ι ι ℂ) ≤
        eta • (1 : Matrix ι ι ℂ) := by
      rw [Matrix.le_iff]
      simpa [sub_smul] using hgap
    have hlower : -((‖H - X‖ : ℝ) • (1 : Matrix ι ι ℂ)) ≤ H - X := by
      simpa [Algebra.algebraMap_eq_smul_one] using hE.isSelfAdjoint.neg_algebraMap_norm_le_self
    have hshift : (H - X + eta • (1 : Matrix ι ι ℂ)).PosSemidef := by
      have h := Matrix.le_iff.mp ((neg_le_neg hscalar).trans hlower)
      simpa only [sub_neg_eq_add] using h
    have hadd := hshift.add hX
    convert hadd using 1
    unfold shiftedMatrix
    abel

theorem repairDenominator_ge_one_of_entrywise_error
    {D : ℕ} (hD : 0 < D) (rho : DensityOperator (Fin D))
    (H : Matrix (Fin D) (Fin D) ℂ) (eta : ℝ) (heta : 0 ≤ eta)
    (herror : entryNormSum (H - rho.matrix) ≤ eta) :
    1 ≤ repairDenominator H eta := by
  have ht := (abs_trace_re_le_entryNormSum (H - rho.matrix)).trans herror
  rw [Matrix.trace_sub, rho.trace_eq_one, Complex.sub_re, Complex.one_re] at ht
  have hdim : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hmul := mul_le_mul_of_nonneg_right hdim heta
  have hlo := (abs_le.mp ht).1
  unfold repairDenominator
  simp only [Fintype.card_fin]
  nlinarith

/-- A single entrywise-error check is sufficient to obtain a feasible
repaired density and a quantified Frobenius error. No approximate PSD or
positive-denominator assumption is left to the caller. -/
theorem repair_from_entrywise_error
    {D : ℕ} (hD : 0 < D) (rho : DensityOperator (Fin D))
    (H : Matrix (Fin D) (Fin D) ℂ) (hH : H.IsHermitian)
    (eta : ℝ) (heta : 0 ≤ eta)
    (herror : entryNormSum (H - rho.matrix) ≤ eta) :
    (repairedMatrix H eta).PosSemidef ∧ (repairedMatrix H eta).trace = 1 ∧
      ‖encode (repairedMatrix H eta - rho.matrix)‖ ≤ (2 * (D : ℝ) + 2) * eta := by
  have hshift := shifted_approximation_posSemidef H rho.matrix hH rho.posSemidef eta
    ((operatorNorm_le_entryNormSum _).trans herror)
  have hden : 0 < repairDenominator H eta := lt_of_lt_of_le (by norm_num)
    (repairDenominator_ge_one_of_entrywise_error hD rho H eta heta herror)
  have hpsd := repairedMatrix_posSemidef H eta hshift hden
  have htrace := repairedMatrix_trace_eq_one H eta hH hden
  have htraceError := (abs_trace_re_le_entryNormSum (H - rho.matrix)).trans herror
  rw [Matrix.trace_sub, rho.trace_eq_one, Complex.sub_re, Complex.one_re] at htraceError
  have hrepair := repairedMatrix_sub_traceNorm_le H eta hH heta hshift htraceError hden
  have hnorm := norm_encode_le_hermitianTraceNorm (repairedMatrix H eta - H)
    (hpsd.isHermitian.sub hH)
  have hround := (norm_encode_le_entryNormSum (H - rho.matrix)).trans herror
  refine ⟨hpsd, htrace, ?_⟩
  have htriangle : ‖encode (repairedMatrix H eta - rho.matrix)‖ ≤
      ‖encode (repairedMatrix H eta - H)‖ + ‖encode (H - rho.matrix)‖ := by
    have hid : repairedMatrix H eta - rho.matrix =
        (repairedMatrix H eta - H) + (H - rho.matrix) := by abel
    rw [hid, encode_add]
    exact norm_add_le _ _
  simp only [Fintype.card_fin] at hrepair
  linarith

end

end TomographyOracleCore.Revision.FinitePrecision
