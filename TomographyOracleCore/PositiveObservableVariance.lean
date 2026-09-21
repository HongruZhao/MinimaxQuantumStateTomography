import TomographyOracleCore.RelativeDesignOrder
import TomographyOracleCore.ProjectiveHaarPOVM

namespace TomographyOracleCore

open MatrixReduction
open scoped CStarAlgebra ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

/-!
# Positive-observable variance from relative completely-positive order

This module formalizes the order-theoretic and scalar core of
Schuster--Haferkamp--Huang, Theorem 7, Eqs. (E.10)--(E.15).  In particular,
the approximate-design error is obtained from the literal relative CP order
defined in `RelativeDesignOrder`; it is not supplied as a scalar variance
premise.

The two Haar contraction estimates and the exact-Haar baseline are kept
visible as separate hypotheses of the abstract theorem.  They are elementary
Haar-moment facts and can be discharged independently by the concrete moment
twirl.  This separation makes the trust boundary explicit while retaining
the exact published constant `10` for dimensions at least four.
-/

section PositiveTracePairing

/-- Real trace pairing used to test the output of a moment twirl against a
positive observable. -/
noncomputable def cpTracePairing {N : ℕ}
    (test : Matrix (Fin N) (Fin N) ℂ)
    (Phi : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ]
      Matrix (Fin N) (Fin N) ℂ)
    (input : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  (test * Phi input).trace.re

/-- Positive trace tests preserve the matrix Loewner order. -/
theorem trace_mul_re_mono_of_posSemidef {N : ℕ} [Nonempty (Fin N)]
    {X Y test : Matrix (Fin N) (Fin N) ℂ}
    (hXY : X ≤ Y) (htest : test.PosSemidef) :
    (test * X).trace.re ≤ (test * Y).trace.re := by
  have hdiff : (Y - X).PosSemidef := hXY
  have hnonneg := trace_mul_re_nonnegative_of_posSemidef
    test (Y - X) htest hdiff
  have htrace :
      (test * (Y - X)).trace.re =
        (test * Y).trace.re - (test * X).trace.re := by
    rw [Matrix.mul_sub, Matrix.trace_sub]
    rfl
  rw [htrace] at hnonneg
  linarith

/-- The upper half of relative CP order controls every positive trace
contraction, with the same multiplicative error. -/
theorem RelativeCPApproximation.cpTracePairing_le_upper {N : ℕ}
    [Nonempty (Fin N)]
    {epsilon : ℝ}
    {ensemble haar : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ]
      Matrix (Fin N) (Fin N) ℂ}
    (h : RelativeCPApproximation
      (A := Matrix (Fin N) (Fin N) ℂ) epsilon ensemble haar)
    {input test : Matrix (Fin N) (Fin N) ℂ}
    (hinput : input.PosSemidef) (htest : test.PosSemidef) :
    cpTracePairing test ensemble input ≤
      (1 + epsilon) * cpTracePairing test haar input := by
  have hmatrix := h.apply_le_upper hinput.nonneg
  have htrace := trace_mul_re_mono_of_posSemidef hmatrix htest
  simpa [cpTracePairing, mul_assoc] using htrace

/-- The lower half of relative CP order controls every positive trace
contraction, with the same multiplicative error. -/
theorem RelativeCPApproximation.lower_cpTracePairing_le {N : ℕ}
    [Nonempty (Fin N)]
    {epsilon : ℝ}
    {ensemble haar : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ]
      Matrix (Fin N) (Fin N) ℂ}
    (h : RelativeCPApproximation
      (A := Matrix (Fin N) (Fin N) ℂ) epsilon ensemble haar)
    {input test : Matrix (Fin N) (Fin N) ℂ}
    (hinput : input.PosSemidef) (htest : test.PosSemidef) :
    (1 - epsilon) * cpTracePairing test haar input ≤
      cpTracePairing test ensemble input := by
  have hmatrix := h.lower_apply_le hinput.nonneg
  have htrace := trace_mul_re_mono_of_posSemidef hmatrix htest
  simpa [cpTracePairing, mul_assoc] using htrace

end PositiveTracePairing

section ScalarAssembly

/-- The centered third-moment expression in Eq. (E.12).  `m3`, `m2`, and
`m1` denote the positive third-, second-, and first-moment contractions.
The factor `D (D+1)^2` is the calibrated-shadow prefactor. -/
noncomputable def positiveObservableCenteredMoment
    (D : ℕ) (traceO m3 m2 m1 : ℝ) : ℝ :=
  (D : ℝ) * ((D : ℝ) + 1) ^ 2 *
    (m3 - (2 * traceO / (D : ℝ)) * m2 +
      traceO ^ 2 / (D : ℝ) ^ 2 * m1)

/-- The two symmetric-projector Haar norm estimates of Eq. (E.14) produce
at most `10 * trace(O)^2` after applying the calibrated prefactor.  The
constant is valid for `D ≥ 4`, the regime used by the shallow-qubit
specialization. -/
theorem haarMomentErrorCoefficient_le_ten
    (D : ℕ) (hD : 4 ≤ D) (traceO : ℝ) :
    (D : ℝ) * ((D : ℝ) + 1) ^ 2 *
        (6 * traceO ^ 2 /
            ((D : ℝ) * ((D : ℝ) + 1) * ((D : ℝ) + 2)) +
          (2 * traceO / (D : ℝ)) *
            (2 * traceO /
              ((D : ℝ) * ((D : ℝ) + 1)))) ≤
      10 * traceO ^ 2 := by
  have hDreal : (4 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := by positivity
  have hD1pos : (0 : ℝ) < (D : ℝ) + 1 := by positivity
  have hD2pos : (0 : ℝ) < (D : ℝ) + 2 := by positivity
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  field_simp
  nlinarith [sq_nonneg traceO]

/-- Scalar core of the positive-observable variance theorem.

The relative third-moment upper bound and relative second-moment lower bound
are exactly the two signs forced by the expansion of the centered observable.
The first moment cancels.  The remaining Haar contribution is bounded by the
exact-design shadow variance, and the two Haar moment contractions give the
published error constant `10`. -/
theorem positiveObservableVariance_le_of_relativeMoments
    (D : ℕ) (hD : 4 ≤ D)
    {epsilon traceO haarSquare variance : ℝ}
    {ensemble3 haar3 ensemble2 haar2 first : ℝ}
    (hepsilon : 0 ≤ epsilon) (htraceO : 0 ≤ traceO)
    (hthird : ensemble3 ≤ (1 + epsilon) * haar3)
    (hsecond : (1 - epsilon) * haar2 ≤ ensemble2)
    (hhaar3 : haar3 ≤
      6 * traceO ^ 2 /
        ((D : ℝ) * ((D : ℝ) + 1) * ((D : ℝ) + 2)))
    (hhaar2 : haar2 ≤
      2 * traceO / ((D : ℝ) * ((D : ℝ) + 1)))
    (hhaarBaseline :
      positiveObservableCenteredMoment D traceO haar3 haar2 first ≤
        3 * haarSquare)
    (hvariance : variance ≤
      positiveObservableCenteredMoment D traceO
        ensemble3 ensemble2 first) :
    variance ≤ 3 * haarSquare + 10 * epsilon * traceO ^ 2 := by
  have hDpos : (0 : ℝ) < D := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 4) hD)
  let prefactor : ℝ := (D : ℝ) * ((D : ℝ) + 1) ^ 2
  let coeff : ℝ := 2 * traceO / (D : ℝ)
  have hprefactor : 0 ≤ prefactor := by
    dsimp [prefactor]
    positivity
  have hcoeff : 0 ≤ coeff := by
    dsimp [coeff]
    positivity
  have hinside :
      ensemble3 - coeff * ensemble2 ≤
        haar3 - coeff * haar2 +
          epsilon * (haar3 + coeff * haar2) := by
    have hneg := neg_le_neg (mul_le_mul_of_nonneg_left hsecond hcoeff)
    nlinarith
  have hcentered :
      positiveObservableCenteredMoment D traceO
          ensemble3 ensemble2 first ≤
        positiveObservableCenteredMoment D traceO haar3 haar2 first +
          prefactor * epsilon * (haar3 + coeff * haar2) := by
    have hmul := mul_le_mul_of_nonneg_left hinside hprefactor
    dsimp [positiveObservableCenteredMoment, prefactor, coeff] at hmul ⊢
    nlinarith
  have hcoeffHaar :
      haar3 + coeff * haar2 ≤
        6 * traceO ^ 2 /
            ((D : ℝ) * ((D : ℝ) + 1) * ((D : ℝ) + 2)) +
          (2 * traceO / (D : ℝ)) *
            (2 * traceO /
              ((D : ℝ) * ((D : ℝ) + 1))) := by
    exact add_le_add hhaar3 (mul_le_mul_of_nonneg_left hhaar2 hcoeff)
  have herrorCoefficient :
      prefactor * (haar3 + coeff * haar2) ≤ 10 * traceO ^ 2 := by
    calc
      prefactor * (haar3 + coeff * haar2) ≤
          prefactor *
            (6 * traceO ^ 2 /
                ((D : ℝ) * ((D : ℝ) + 1) * ((D : ℝ) + 2)) +
              (2 * traceO / (D : ℝ)) *
                (2 * traceO /
                  ((D : ℝ) * ((D : ℝ) + 1)))) :=
        mul_le_mul_of_nonneg_left hcoeffHaar hprefactor
      _ ≤ 10 * traceO ^ 2 := by
        simpa [prefactor] using
          haarMomentErrorCoefficient_le_ten D hD traceO
  have herror :
      prefactor * epsilon * (haar3 + coeff * haar2) ≤
        10 * epsilon * traceO ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left herrorCoefficient hepsilon
    nlinarith
  exact hvariance.trans (hcentered.trans (by linarith))

end ScalarAssembly

section RelativeCPVariance

/-- The positive-observable variance theorem composed directly with literal
relative completely-positive order at moments three and two.

The matrix sizes may differ because the order-three and order-two tensor
spaces are different.  Positivity of the input moment operators and of the
observable tests turns CP order into the scalar inequalities needed by
`positiveObservableVariance_le_of_relativeMoments`. -/
theorem positiveObservableVariance_le_of_relativeCP
    (D : ℕ) (hD : 4 ≤ D)
    {N3 N2 : ℕ}
    [Nonempty (Fin N3)] [Nonempty (Fin N2)]
    {epsilon traceO haarSquare variance first : ℝ}
    {ensembleMap3 haarMap3 :
      Matrix (Fin N3) (Fin N3) ℂ →ₗ[ℂ]
        Matrix (Fin N3) (Fin N3) ℂ}
    {ensembleMap2 haarMap2 :
      Matrix (Fin N2) (Fin N2) ℂ →ₗ[ℂ]
        Matrix (Fin N2) (Fin N2) ℂ}
    {input3 test3 : Matrix (Fin N3) (Fin N3) ℂ}
    {input2 test2 : Matrix (Fin N2) (Fin N2) ℂ}
    (hepsilon : 0 ≤ epsilon) (htraceO : 0 ≤ traceO)
    (hrelative3 : RelativeCPApproximation
      (A := Matrix (Fin N3) (Fin N3) ℂ)
      epsilon ensembleMap3 haarMap3)
    (hrelative2 : RelativeCPApproximation
      (A := Matrix (Fin N2) (Fin N2) ℂ)
      epsilon ensembleMap2 haarMap2)
    (hinput3 : input3.PosSemidef) (htest3 : test3.PosSemidef)
    (hinput2 : input2.PosSemidef) (htest2 : test2.PosSemidef)
    (hhaar3 : cpTracePairing test3 haarMap3 input3 ≤
      6 * traceO ^ 2 /
        ((D : ℝ) * ((D : ℝ) + 1) * ((D : ℝ) + 2)))
    (hhaar2 : cpTracePairing test2 haarMap2 input2 ≤
      2 * traceO / ((D : ℝ) * ((D : ℝ) + 1)))
    (hhaarBaseline :
      positiveObservableCenteredMoment D traceO
          (cpTracePairing test3 haarMap3 input3)
          (cpTracePairing test2 haarMap2 input2) first ≤
        3 * haarSquare)
    (hvariance : variance ≤
      positiveObservableCenteredMoment D traceO
          (cpTracePairing test3 ensembleMap3 input3)
          (cpTracePairing test2 ensembleMap2 input2) first) :
    variance ≤ 3 * haarSquare + 10 * epsilon * traceO ^ 2 := by
  apply positiveObservableVariance_le_of_relativeMoments D hD
    hepsilon htraceO
  · exact hrelative3.cpTracePairing_le_upper hinput3 htest3
  · exact hrelative2.lower_cpTracePairing_le hinput2 htest2
  · exact hhaar3
  · exact hhaar2
  · exact hhaarBaseline
  · exact hvariance

end RelativeCPVariance

end

end TomographyOracleCore
