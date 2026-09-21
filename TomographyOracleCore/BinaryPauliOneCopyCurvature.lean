import TomographyOracleCore.BinaryCliffordPeriodicPhysicalChannel
import TomographyOracleCore.FiniteUnitaryProjectiveScore
import TomographyOracleCore.BinaryPauliTensorPermutations

namespace TomographyOracleCore

open scoped BigOperators
open MatrixReduction
noncomputable section

/-- Hilbert--Schmidt coefficient of a matrix against one Hermitian binary
Pauli. -/
noncomputable def binaryHermitianPauliCoefficient
    (K : ℕ) (X : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)
    (p : PauliLabel K) : ℂ :=
  (hermitianBinaryPauliMatrix K p * X).trace

theorem binaryHermitianPauliCoefficient_eq_trace
    (K : ℕ) (X : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)
    (p : PauliLabel K) :
    binaryHermitianPauliCoefficient K X p =
      (hermitianBinaryPauliMatrix K p * X).trace := by
  rfl

/-- Unnormalized one-copy Hermitian Pauli reconstruction. -/
theorem hermitianBinaryPauli_reconstruction_unscaled
    (K : ℕ) (X : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ) :
    (∑ p : PauliLabel K,
      binaryHermitianPauliCoefficient K X p •
        hermitianBinaryPauliMatrix K p) =
      ((2 : ℂ) ^ K) • X := by
  classical
  ext x y
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    binaryHermitianPauliCoefficient, Matrix.trace, Matrix.diag_apply]
  simp_rw [Matrix.mul_apply]
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ a : PauliBinaryWord K, ∑ b : PauliBinaryWord K,
        X b a *
          (∑ p : PauliLabel K,
            hermitianBinaryPauliMatrix K p a b *
              hermitianBinaryPauliMatrix K p x y) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = (2 ^ K) * X x y := by
      simp_rw [hermitianBinaryPauli_completeness]
      rw [Finset.sum_eq_single y]
      · rw [Finset.sum_eq_single x]
        · simp [mul_comm]
        · intro b hb hby
          simp [hby]
        · simp
      · intro a ha hax
        apply Finset.sum_eq_zero
        intro b hb
        simp [hax]
      · simp

/-- Exact one-copy reconstruction of an arbitrary matrix in the Hermitian
Pauli basis. -/
theorem hermitianBinaryPauli_reconstruction
    (K : ℕ) (X : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ) :
    X = (((2 : ℂ) ^ K)⁻¹) •
      ∑ p : PauliLabel K,
        binaryHermitianPauliCoefficient K X p •
          hermitianBinaryPauliMatrix K p := by
  symm
  rw [hermitianBinaryPauli_reconstruction_unscaled, smul_smul]
  have hD : ((2 : ℂ) ^ K) ≠ 0 := by norm_num
  rw [inv_mul_cancel₀ hD, one_smul]

/-- Hermitian Pauli coordinates of a Hermitian matrix are real. -/
theorem binaryHermitianPauliCoefficient_im_eq_zero
    (K : ℕ) (X : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)
    (hX : X.IsHermitian) (p : PauliLabel K) :
    (binaryHermitianPauliCoefficient K X p).im = 0 := by
  rw [binaryHermitianPauliCoefficient_eq_trace]
  exact trace_mul_im_eq_zero_of_isHermitian
    (hermitianBinaryPauliMatrix K p) X
    (hermitianBinaryPauliMatrix_conjTranspose K p) hX

theorem binaryHermitianPauliCoefficient_eq_re
    (K : ℕ) (X : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)
    (hX : X.IsHermitian) (p : PauliLabel K) :
    binaryHermitianPauliCoefficient K X p =
      ((binaryHermitianPauliCoefficient K X p).re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [binaryHermitianPauliCoefficient_im_eq_zero K X hX p]

theorem complexLinearPauliChannel_apply_reconstruction
    (K : ℕ)
    (channel : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ →ₗ[ℂ]
      Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)
    (eigenvalue : PauliLabel K → ℝ)
    (hdiagonal : ∀ p, channel (hermitianBinaryPauliMatrix K p) =
      (eigenvalue p : ℂ) • hermitianBinaryPauliMatrix K p)
    (X : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ) :
    channel X = (((2 : ℂ) ^ K)⁻¹) •
      ∑ p : PauliLabel K,
        (binaryHermitianPauliCoefficient K X p * (eigenvalue p : ℂ)) •
          hermitianBinaryPauliMatrix K p := by
  conv_lhs => rw [hermitianBinaryPauli_reconstruction K X]
  rw [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [map_smul, hdiagonal, smul_smul]

/-- Exact quadratic-energy formula for a complex-linear channel diagonal in
the Hermitian Pauli basis. -/
theorem complexLinearPauliChannel_energy_eq
    (K : ℕ)
    (channel : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ →ₗ[ℂ]
      Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)
    (eigenvalue : PauliLabel K → ℝ)
    (hdiagonal : ∀ p, channel (hermitianBinaryPauliMatrix K p) =
      (eigenvalue p : ℂ) • hermitianBinaryPauliMatrix K p)
    (X : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)
    (hX : X.IsHermitian) :
    (channel X * X).trace.re =
      ((2 : ℝ) ^ K)⁻¹ *
        ∑ p : PauliLabel K,
          eigenvalue p * (binaryHermitianPauliCoefficient K X p).re ^ 2 := by
  rw [complexLinearPauliChannel_apply_reconstruction K channel eigenvalue
    hdiagonal X]
  simp only [Matrix.smul_mul, Finset.sum_mul, Matrix.trace_smul,
    Matrix.trace_sum]
  simp_rw [← binaryHermitianPauliCoefficient_eq_trace]
  have hpow : ((2 : ℂ) ^ K)⁻¹ = ((((2 : ℝ) ^ K)⁻¹ : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hpow]
  simp only [smul_eq_mul, Complex.mul_re, Complex.re_sum,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply congrArg (fun z : ℝ ↦ ((2 : ℝ) ^ K)⁻¹ * z)
  apply Finset.sum_congr rfl
  intro p hp
  rw [binaryHermitianPauliCoefficient_eq_re K X hX p]
  simp
  ring

/-- A common real eigenvalue floor on every nonidentity Hermitian Pauli
implies the corresponding Hilbert--Schmidt curvature inequality on every
traceless Hermitian matrix. -/
theorem complexLinearPauliChannel_curvature
    (K : ℕ)
    (channel : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ →ₗ[ℂ]
      Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)
    (eigenvalue : PauliLabel K → ℝ)
    (hdiagonal : ∀ p, channel (hermitianBinaryPauliMatrix K p) =
      (eigenvalue p : ℂ) • hermitianBinaryPauliMatrix K p)
    (mu : ℝ)
    (heigenvalue : ∀ p, p ≠ 0 → mu ≤ eigenvalue p)
    (X : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)
    (hX : X.IsHermitian) (htrace : X.trace = 0) :
    mu * hermitianFrobeniusNorm X hX ^ 2 ≤
      (channel X * X).trace.re := by
  classical
  have hidDiagonal : ∀ p : PauliLabel K,
      LinearMap.id (R := ℂ)
          (M := Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)
          (hermitianBinaryPauliMatrix K p) =
        ((1 : ℝ) : ℂ) • hermitianBinaryPauliMatrix K p := by
    intro p
    simp
  have hidEnergy := complexLinearPauliChannel_energy_eq K
    (LinearMap.id (R := ℂ)
      (M := Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ))
    (fun _ : PauliLabel K ↦ (1 : ℝ)) hidDiagonal X hX
  have hidEnergy' : (X * X).trace.re =
      ((2 : ℝ) ^ K)⁻¹ *
        ∑ p : PauliLabel K,
          (binaryHermitianPauliCoefficient K X p).re ^ 2 := by
    simpa using hidEnergy
  have htraceSq := trace_sq_eq_hermitianFrobeniusSq X hX
  have hnorm : hermitianFrobeniusNorm X hX ^ 2 =
      ((2 : ℝ) ^ K)⁻¹ *
        ∑ p : PauliLabel K,
          (binaryHermitianPauliCoefficient K X p).re ^ 2 := by
    rw [hermitianFrobeniusNorm_sq]
    have hre := congrArg Complex.re htraceSq
    have hre' : hermitianFrobeniusSq X hX = (X * X).trace.re := by
      simpa using hre.symm
    rw [hre', hidEnergy']
  have hzero : (binaryHermitianPauliCoefficient K X 0).re = 0 := by
    simp [binaryHermitianPauliCoefficient,
      hermitianBinaryPauliMatrix_zero, htrace]
  have hsum :
      mu * (∑ p : PauliLabel K,
        (binaryHermitianPauliCoefficient K X p).re ^ 2) ≤
      ∑ p : PauliLabel K,
        eigenvalue p *
          (binaryHermitianPauliCoefficient K X p).re ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    by_cases hp0 : p = 0
    · subst p
      simp [hzero]
    · exact mul_le_mul_of_nonneg_right (heigenvalue p hp0) (sq_nonneg _)
  rw [hnorm, complexLinearPauliChannel_energy_eq K channel eigenvalue
    hdiagonal X hX]
  calc
    mu * (((2 : ℝ) ^ K)⁻¹ *
        ∑ p : PauliLabel K,
          (binaryHermitianPauliCoefficient K X p).re ^ 2) =
        ((2 : ℝ) ^ K)⁻¹ *
          (mu * ∑ p : PauliLabel K,
            (binaryHermitianPauliCoefficient K X p).re ^ 2) := by ring
    _ ≤ ((2 : ℝ) ^ K)⁻¹ *
        ∑ p : PauliLabel K,
          eigenvalue p *
            (binaryHermitianPauliCoefficient K X p).re ^ 2 :=
      mul_le_mul_of_nonneg_left hsum (by positivity)

end
end TomographyOracleCore
