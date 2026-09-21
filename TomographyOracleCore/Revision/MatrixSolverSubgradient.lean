import TomographyOracleCore.Revision.MatrixSolverChannel
import TomographyOracleCore.Revision.MatrixSolverSpectral
import TomographyOracleCore.Revision.FinitePrecisionProjector

/-! Actual matrix subgradients for the finite projective forward objective. -/

namespace TomographyOracleCore.Revision.MatrixSolver

open MatrixReduction FinitePrecision
open scoped ComplexOrder InnerProductSpace BigOperators

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]

def forwardGradient (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (v : EuclideanSpace ℂ (Fin D)) (s : ℝ) : FrobeniusMatrix (Fin D) :=
  (-((D + 1 : ℕ) : ℝ) * s) •
    encode (finiteUnitaryProjectiveLinearChannel U (normalizedProjector v))

theorem signedRayleigh_eq_real_inner
    (A : Matrix (Fin D) (Fin D) ℂ) (v : EuclideanSpace ℂ (Fin D)) (s : ℝ) :
    signedRayleigh A v s = s * ⟪encode (normalizedProjector v), encode A⟫_ℝ := by
  rw [real_inner_encode_eq_trace_of_hermitian _ _ (normalizedProjector_posSemidef v).isHermitian,
    trace_mul_normalizedProjector_re_eq_rayleigh]
  rfl

theorem forwardGradient_norm_le
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (v : EuclideanSpace ℂ (Fin D)) (hv : v ≠ 0) {s : ℝ} (hs : |s| ≤ 1) :
    ‖forwardGradient U v s‖ ≤ ((D + 1 : ℕ) : ℝ) := by
  have hp2 := density_frobenius_norm_sq_le_one (normalizedProjectorDensity v hv)
  have hp : ‖encode (normalizedProjector v)‖ ≤ 1 := by
    have hn := norm_nonneg (encode (normalizedProjector v))
    change ‖encode (normalizedProjector v)‖ ^ 2 ≤ 1 at hp2
    nlinarith
  have hm := (finite_channel_frobenius_contract U (normalizedProjector v)).trans hp
  have hG : 0 ≤ ((D + 1 : ℕ) : ℝ) := by positivity
  rw [forwardGradient, norm_smul, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hG]
  calc
    ((D + 1 : ℕ) : ℝ) * |s| *
        ‖encode (finiteUnitaryProjectiveLinearChannel U (normalizedProjector v))‖ ≤
      ((D + 1 : ℕ) : ℝ) * 1 * 1 := by gcongr
    _ = ((D + 1 : ℕ) : ℝ) := by ring

theorem forwardGradient_isHermitian
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (v : EuclideanSpace ℂ (Fin D)) (hv : v ≠ 0) (s : ℝ) :
    (decode (forwardGradient U v s)).IsHermitian := by
  rw [forwardGradient, decode_smul, decode_encode]
  have hM : (finiteUnitaryProjectiveLinearChannel U (normalizedProjector v)).IsHermitian := by
    change (finiteUnitaryProjectiveLinearChannel U (normalizedProjectorDensity v hv).matrix).IsHermitian
    rw [finiteUnitaryProjectiveLinearChannel_density]
    exact finiteUnitaryProjectiveDensityForward_isHermitian U _
  exact hM.smul (isSelfAdjoint_iff.mpr (by simp))

theorem calibrated_difference_eq_negative_channel
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (rho sigma : DensityOperator (Fin D)) :
    finiteUnitaryFullCalibratedLinearChannel U (sigma.matrix - rho.matrix) =
      -(((D + 1 : ℕ) : ℝ)) •
        finiteUnitaryProjectiveLinearChannel U (rho.matrix - sigma.matrix) := by
  rw [finiteUnitaryFullCalibratedLinearChannel_apply, Matrix.trace_sub,
    sigma.trace_eq_one, rho.trace_eq_one, sub_self, zero_smul, sub_zero]
  have hd : sigma.matrix - rho.matrix = -(rho.matrix - sigma.matrix) := by abel
  rw [hd, map_neg, smul_neg, neg_smul]
  rfl

theorem forwardGradient_pairing
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (rho sigma : DensityOperator (Fin D))
    (v : EuclideanSpace ℂ (Fin D)) (s : ℝ) :
    ⟪forwardGradient U v s, encode rho.matrix - encode sigma.matrix⟫_ℝ =
      signedRayleigh
        (finiteUnitaryFullCalibratedLinearChannel U (sigma.matrix - rho.matrix)) v s := by
  rw [forwardGradient, real_inner_smul_left, ← encode_sub,
    finite_channel_frobenius_selfAdjoint, signedRayleigh_eq_real_inner,
    calibrated_difference_eq_negative_channel, encode_smul, real_inner_smul_right]
  ring

/-- The explicitly constructed matrix direction is an epsilon-subgradient
of the actual Candidate 2 objective. The only spectral premise is the local
Rayleigh accuracy certificate, which can be provided either by the exact
spectral theorem or by an approximate computational routine. -/
theorem forwardGradient_subgradient
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (rho sigma : DensityOperator (Fin D))
    (v : EuclideanSpace ℂ (Fin D)) {s epsilon : ℝ} (hs : |s| ≤ 1)
    (happrox : matrixOperatorNorm
        (Q - finiteUnitaryFullCalibratedLinearChannel U rho.matrix) - epsilon ≤
      signedRayleigh (Q - finiteUnitaryFullCalibratedLinearChannel U rho.matrix) v s) :
    matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U rho.matrix) -
        matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U sigma.matrix) ≤
      ⟪forwardGradient U v s, encode rho.matrix - encode sigma.matrix⟫_ℝ + epsilon := by
  rw [forwardGradient_pairing]
  exact approximate_rayleigh_forward_epsilon_subgradient
    (finiteUnitaryFullCalibratedLinearChannel U) Q rho.matrix v hs happrox sigma.matrix

theorem residual_isHermitian
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian)
    (rho : DensityOperator (Fin D)) :
    (Q - finiteUnitaryFullCalibratedLinearChannel U rho.matrix).IsHermitian := by
  rw [finiteUnitaryFullCalibratedLinearChannel_density]
  exact hQ.sub (finiteUnitaryCalibratedDensityChannel_isHermitian U rho)

/-- A bounded true subgradient exists at every actual density matrix.
There are no scientific, eigensolver, projection, or optimization premises. -/
theorem exists_forward_subgradient (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian)
    (rho : DensityOperator (Fin D)) :
    ∃ g : FrobeniusMatrix (Fin D), ‖g‖ ≤ ((D + 1 : ℕ) : ℝ) ∧
      ∀ sigma : DensityOperator (Fin D),
        matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U rho.matrix) -
            matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U sigma.matrix) ≤
          ⟪g, encode rho.matrix - encode sigma.matrix⟫_ℝ := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  obtain ⟨v, s, hv, hs, hspec⟩ := exists_exact_signedRayleigh
    (Q - finiteUnitaryFullCalibratedLinearChannel U rho.matrix) (residual_isHermitian U Q hQ rho)
  have hv0 : v ≠ 0 := by intro h; simpa [h] using hv
  refine ⟨forwardGradient U v s, forwardGradient_norm_le U v hv0 hs, ?_⟩
  intro sigma
  have ht := forwardGradient_subgradient U Q rho sigma v (epsilon := 0) hs
    (by simpa only [sub_zero] using hspec.ge)
  simpa only [add_zero] using ht

end

end TomographyOracleCore.Revision.MatrixSolver
