import TomographyOracleCore.Revision.AlgorithmResourcesPowerScalar
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Normed

/-! Matrix power iteration: exact column/trace identities and a gap-free bound. -/

namespace TomographyOracleCore.Revision.AlgorithmResources

open Matrix Unitary
open scoped BigOperators ComplexOrder

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def complexVectorNormSq (v : ι → ℂ) : ℝ := ∑ i, Complex.normSq (v i)

def complexQuadratic (A : Matrix ι ι ℂ) (v : ι → ℂ) : ℝ :=
  (∑ i, star (v i) * (A *ᵥ v) i).re

def complexRayleigh (A : Matrix ι ι ℂ) (v : ι → ℂ) : ℝ :=
  complexQuadratic A v / complexVectorNormSq v

def powerColumn (A : Matrix ι ι ℂ) (k : ℕ) (j : ι) : ι → ℂ :=
  fun i => (A ^ k) i j

theorem complexVectorNormSq_nonneg (v : ι → ℂ) : 0 ≤ complexVectorNormSq v :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem complexVectorNormSq_eq_zero (v : ι → ℂ) :
    complexVectorNormSq v = 0 ↔ v = 0 := by
  simp only [complexVectorNormSq, Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Complex.normSq_nonneg (v i)), Finset.mem_univ, forall_const,
    Complex.normSq_eq_zero, funext_iff, Pi.zero_apply]

theorem complexVectorNormSq_pos (v : ι → ℂ) (hv : v ≠ 0) :
    0 < complexVectorNormSq v :=
  lt_of_le_of_ne (complexVectorNormSq_nonneg v)
    (Ne.symm (mt (complexVectorNormSq_eq_zero v).mp hv))

@[simp] theorem complexQuadratic_zero (A : Matrix ι ι ℂ) : complexQuadratic A 0 = 0 := by
  simp [complexQuadratic]

theorem powerColumn_normSq (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (k : ℕ) (j : ι) :
    complexVectorNormSq (powerColumn A k j) = ((A ^ (2 * k)) j j).re := by
  calc
    complexVectorNormSq (powerColumn A k j) =
        (((A ^ k)ᴴ * (A ^ k)) j j).re := by
      simp only [complexVectorNormSq, powerColumn, Matrix.mul_apply, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Matrix.conjTranspose_apply]
      simp [Complex.normSq_apply, Complex.mul_re]
    _ = ((A ^ (2 * k)) j j).re := by
      rw [(hA.pow k).eq, ← pow_add, ← two_mul]

theorem powerColumn_quadratic (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (k : ℕ) (j : ι) :
    complexQuadratic A (powerColumn A k j) = ((A ^ (2 * k + 1)) j j).re := by
  calc
    complexQuadratic A (powerColumn A k j) =
        (((A ^ k)ᴴ * (A * (A ^ k))) j j).re := by
      simp only [complexQuadratic, powerColumn, Matrix.mul_apply,
        Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
    _ = ((A ^ (2 * k + 1)) j j).re := by
      have he : k + (k + 1) = 2 * k + 1 := by omega
      rw [(hA.pow k).eq, ← pow_succ', ← pow_add, he]

theorem trace_pow_re_eq_sum (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (p : ℕ) :
    (A ^ p).trace.re = ∑ i, hA.eigenvalues i ^ p := by
  conv_lhs => rw [hA.spectral_theorem, ← map_pow,
    Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
    one_mul]
  simp only [Matrix.diagonal_pow, Matrix.trace_diagonal, Function.comp_def,
    Pi.pow_apply, Complex.re_sum]
  change (∑ i, ((hA.eigenvalues i : ℂ) ^ p).re) = _
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]

theorem sum_powerColumn_normSq (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (k : ℕ) :
    (∑ j, complexVectorNormSq (powerColumn A k j)) =
      ∑ i, hA.eigenvalues i ^ (2 * k) := by
  rw [← trace_pow_re_eq_sum A hA]
  simp [powerColumn_normSq A hA, Matrix.trace]

theorem sum_powerColumn_quadratic (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (k : ℕ) :
    (∑ j, complexQuadratic A (powerColumn A k j)) =
      ∑ i, hA.eigenvalues i ^ (2 * k + 1) := by
  rw [← trace_pow_re_eq_sum A hA]
  simp [powerColumn_quadratic A hA, Matrix.trace]

/-- Every common upper bound on column Rayleigh quotients approximates the
largest eigenvalue. In particular this applies to the computed maximum. -/
theorem largest_eigenvalue_le_column_bound
    (A : Matrix ι ι ℂ) (hA : A.PosSemidef) (k : ℕ) (j : ι)
    (hmax : ∀ i, hA.isHermitian.eigenvalues i ≤ hA.isHermitian.eigenvalues j)
    (hpos : 0 < hA.isHermitian.eigenvalues j) (R : ℝ)
    (hcolumns : ∀ i, complexRayleigh A (powerColumn A k i) ≤ R) :
    hA.isHermitian.eigenvalues j -
      (Fintype.card ι : ℝ) * hA.isHermitian.eigenvalues j / ((2 * k : ℕ) + 1 : ℝ) ≤ R := by
  have hs : 0 < ∑ i, complexVectorNormSq (powerColumn A k i) := by
    rw [sum_powerColumn_normSq A hA.isHermitian]
    exact Finset.sum_pos' (fun i _ => pow_nonneg (hA.eigenvalues_nonneg i) _)
      ⟨j, Finset.mem_univ _, pow_pos hpos _⟩
  have hpoint : ∀ i, complexQuadratic A (powerColumn A k i) ≤
      R * complexVectorNormSq (powerColumn A k i) := by
    intro i
    by_cases hz : powerColumn A k i = 0
    · simp [hz, complexVectorNormSq]
    · exact (div_le_iff₀ (complexVectorNormSq_pos _ hz)).mp (hcolumns i)
  have hr := weighted_ratio_le_of_pointwise
    (fun i => complexVectorNormSq (powerColumn A k i))
    (fun i => complexQuadratic A (powerColumn A k i)) R hs hpoint
  rw [sum_powerColumn_normSq A hA.isHermitian,
    sum_powerColumn_quadratic A hA.isHermitian] at hr
  exact (spectral_moment_ratio_lower hA.isHermitian.eigenvalues j
    hA.eigenvalues_nonneg hmax hpos (2 * k)).trans hr

#print axioms largest_eigenvalue_le_column_bound

end
end TomographyOracleCore.Revision.AlgorithmResources
