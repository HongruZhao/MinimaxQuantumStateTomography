import TomographyOracleCore.Revision.AlgorithmResourcesPeriodicChannel
import TomographyOracleCore.BinaryCliffordFiniteThirdMoment

/-! Rational encodability of the literal physical measurement projectors.

The physical unitary lift is defined by existence. Its irrelevant complex
phase need not be decoded: the projector's Pauli coefficients are obtained
from conjugated Hermitian Paulis, whose phases are signs. This file proves
that every physical transcript lies in the rational solver's input class.
It does not purport to compute a classical choice of a unitary lift.
-/

namespace TomographyOracleCore.Revision.AlgorithmResources

open Matrix MatrixSolver FinitePrecision
open scoped BigOperators

set_option maxHeartbeats 1000000

noncomputable section

theorem phase_sq_one_has_rational_encoding (c : ℂ) (hc : c * c = 1) :
    ∃ r : QComplex, qComplexToComplex r = c := by
  rcases mul_self_eq_one_iff.mp hc with rfl | rfl
  · exact ⟨1, map_one _⟩
  · exact ⟨-1, by simp only [map_neg, map_one]⟩

theorem conjugates_binaryPauli_to_hermitian
    (N : ℕ) (U : Matrix.unitaryGroup (PauliBinaryWord N) ℂ)
    (p q : PauliLabel N) (c : ℂ) (hc : c ≠ 0)
    (hconj : U.1 * binaryPauliMatrix N p * U.1.conjTranspose =
      c • binaryPauliMatrix N q) :
    ∃ phase : ℂ, phase * phase = 1 ∧
      U.1 * hermitianBinaryPauliMatrix N p * U.1.conjTranspose =
        phase • hermitianBinaryPauliMatrix N q := by
  let phase : ℂ := hermitianPauliPhase N p * c * (hermitianPauliPhase N q)⁻¹
  have hherm : U.1 * hermitianBinaryPauliMatrix N p * U.1.conjTranspose =
      phase • hermitianBinaryPauliMatrix N q := by
    unfold hermitianBinaryPauliMatrix phase
    rw [Matrix.mul_smul, Matrix.smul_mul, hconj, smul_smul, smul_smul]
    apply congrArg (fun z : ℂ => z • binaryPauliMatrix N q)
    field_simp [hermitianPauliPhase_ne_zero]
  exact ⟨phase, conjugation_phase_sq_eq_one U _ _ phase
    (hermitianBinaryPauliMatrix_sq N p) (hermitianBinaryPauliMatrix_sq N q) hherm,
    hherm⟩

theorem binaryUnitaryMeasurementProjector_coefficient
    (N : ℕ) (U : Matrix.unitaryGroup (PauliBinaryWord N) ℂ)
    (b : PauliBinaryWord N) (p : PauliLabel N) :
    binaryHermitianPauliCoefficient N (binaryUnitaryMeasurementProjector N U b) p =
      (U.1 * hermitianBinaryPauliMatrix N p * U.1.conjTranspose) b b := by
  unfold binaryHermitianPauliCoefficient binaryUnitaryMeasurementProjector
    computationalBasisProjector
  calc
    (hermitianBinaryPauliMatrix N p * (U.1.conjTranspose * Matrix.single b b 1 * U.1)).trace =
        ((hermitianBinaryPauliMatrix N p * U.1.conjTranspose * Matrix.single b b 1) * U.1).trace := by
          congr 1
          noncomm_ring
    _ = (U.1 * (hermitianBinaryPauliMatrix N p * U.1.conjTranspose * Matrix.single b b 1)).trace :=
      Matrix.trace_mul_comm _ _
    _ = ((U.1 * hermitianBinaryPauliMatrix N p * U.1.conjTranspose) * Matrix.single b b 1).trace := by
      congr 1
      noncomm_ring
    _ = _ := by rw [Matrix.trace_mul_single]; simp

theorem matrix_has_rational_encoding_of_pauli_coefficients
    (N : ℕ) (X : Matrix (PauliBinaryWord N) (PauliBinaryWord N) ℂ)
    (hcoeff : ∀ p, ∃ c : QComplex, qComplexToComplex c = binaryHermitianPauliCoefficient N X p) :
    ∃ A : Matrix (PauliBinaryWord N) (PauliBinaryWord N) QComplex,
      castQMatrix A = X := by
  classical
  choose c hc using hcoeff
  refine ⟨((2 : ℚ) ^ N)⁻¹ • ∑ p : PauliLabel N, c p • rationalHermitianPauliMatrix N p, ?_⟩
  rw [castQMatrix_rat_smul]
  simp only [castQMatrix_sum, castQMatrix_qcomplex_smul,
    cast_rationalHermitianPauliMatrix, hc]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  convert (hermitianBinaryPauli_reconstruction N X).symm using 1
  congr 1
  change (((((2 : ℚ) ^ N)⁻¹ : ℚ) : ℝ) : ℂ) = ((2 : ℂ) ^ N)⁻¹
  simp only [Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat, Complex.ofReal_inv,
    Complex.ofReal_pow, Complex.ofReal_ofNat]

theorem binaryUnitaryMeasurementProjector_has_rational_encoding
    (N : ℕ) (U : Matrix.unitaryGroup (PauliBinaryWord N) ℂ)
    (hU : ∀ p : PauliLabel N, ∃ q : PauliLabel N, ∃ c : ℂ,
      c * c = 1 ∧ U.1 * hermitianBinaryPauliMatrix N p * U.1.conjTranspose =
        c • hermitianBinaryPauliMatrix N q)
    (b : PauliBinaryWord N) :
    ∃ A : Matrix (PauliBinaryWord N) (PauliBinaryWord N) QComplex,
      castQMatrix A = binaryUnitaryMeasurementProjector N U b := by
  apply matrix_has_rational_encoding_of_pauli_coefficients
  intro p
  obtain ⟨q, c, hc, hconj⟩ := hU p
  obtain ⟨r, hr⟩ := phase_sq_one_has_rational_encoding c hc
  refine ⟨r * rationalHermitianPauliMatrix N q b b, ?_⟩
  rw [map_mul, hr, binaryUnitaryMeasurementProjector_coefficient, hconj]
  have hentry := congrArg (fun A : Matrix (PauliBinaryWord N) (PauliBinaryWord N) ℂ => A b b)
    (cast_rationalHermitianPauliMatrix N q)
  exact congrArg (fun z : ℂ => c * z) hentry

theorem periodic_projector_has_rational_encoding
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K)))
    (e : PeriodicTwoLayerCliffordEnsemble m K) (b : PauliBinaryWord (m * K)) :
    ∃ A : Matrix (PauliBinaryWord (m * K)) (PauliBinaryWord (m * K)) QComplex,
      castQMatrix A = binaryUnitaryMeasurementProjector (m * K)
        (periodicTwoLayerCliffordUnitary m K σ e) b := by
  apply binaryUnitaryMeasurementProjector_has_rational_encoding
  intro p
  obtain ⟨c, hc, hconj⟩ := periodicTwoLayerCliffordUnitary_conjugates_binaryPauli m K σ e p
  exact ⟨periodicTwoLayerPauliAction m K σ e p,
    conjugates_binaryPauli_to_hermitian (m * K) _ p _ c hc hconj⟩

/-- Every literal finite-dimensional physical measurement projector has
an exact Gaussian-rational matrix encoding. This is a theorem, not a
promise about the data supplied to the solver. -/
theorem choKim_projector_has_rational_encoding {n K : ℕ} (hdiv : K ∣ n)
    (e : PeriodicTwoLayerCliffordEnsemble (n / K) K) (b : Fin (2 ^ n)) :
    ∃ A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) QComplex,
      castQMatrix A = finiteUnitaryMeasurementProjector
        (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv e) b := by
  let idx := computableChoKimBlockIndex hdiv
  obtain ⟨A, hA⟩ := periodic_projector_has_rational_encoding (n / K) K
    (cyclicQubitShift ((n / K) * K) (K / 2)) e (idx.symm b)
  refine ⟨qReindexMatrix idx A, ?_⟩
  rw [cast_qReindexMatrix, hA]
  have hproj := finiteUnitaryMeasurementProjector_reindexUnitary idx
    (choKimPeriodicTwoLayerCliffordUnitary (n / K) K e) (idx.symm b)
  simpa only [Equiv.apply_symm_apply, choKimPeriodicTwoLayerCliffordUnitaryFin,
    choKimPeriodicTwoLayerCliffordUnitary, binaryUnitaryMeasurementProjector,
    computationalBasisProjector] using hproj.symm

#print axioms choKim_projector_has_rational_encoding

end
end TomographyOracleCore.Revision.AlgorithmResources
