import TomographyOracleCore.PaperMatch.PureCapStates
import TomographyOracleCore.Revision.FinitePrecisionRepair

/-! Explicit pure-state sign hypercubes and the measurable coordinate decoder. -/
namespace TomographyOracleCore.PaperMatch.RankMinimax
open MeasureTheory ProbabilityTheory MatrixReduction Metric Set
open scoped BigOperators ENNReal ComplexOrder InnerProductSpace
noncomputable section
set_option maxHeartbeats 1000000

abbrev SignCube (m : ℕ) := Fin m → Bool

def cubeSign {m : ℕ} (θ : SignCube m) (j : Fin m) : ℝ := if θ j then 1 else -1

@[simp] theorem cubeSign_sq {m : ℕ} (θ : SignCube m) (j : Fin m) :
    cubeSign θ j ^ 2 = 1 := by unfold cubeSign; split <;> norm_num

@[simp] theorem cubeSign_abs {m : ℕ} (θ : SignCube m) (j : Fin m) :
    |cubeSign θ j| = 1 := by unfold cubeSign; split <;> norm_num

def cubeFlip {m : ℕ} (j : Fin m) (θ : SignCube m) : SignCube m :=
  Function.update θ j (!θ j)

@[simp] theorem cubeFlip_self {m : ℕ} (j : Fin m) (θ : SignCube m) :
    cubeFlip j θ j = !θ j := by simp [cubeFlip]

@[simp] theorem cubeFlip_other {m : ℕ} (j : Fin m) (θ : SignCube m)
    {i : Fin m} (hi : i ≠ j) : cubeFlip j θ i = θ i := by simp [cubeFlip, hi]

@[simp] theorem cubeFlip_involutive {m : ℕ} (j : Fin m) (θ : SignCube m) :
    cubeFlip j (cubeFlip j θ) = θ := by
  funext i
  by_cases hi : i = j
  · subst i; simp
  · simp [cubeFlip_other, hi]

def cubeFlipEquiv {m : ℕ} (j : Fin m) : SignCube m ≃ SignCube m :=
  ⟨cubeFlip j, cubeFlip j, cubeFlip_involutive j, cubeFlip_involutive j⟩

def cubeVector (m : ℕ) (a : ℝ) (θ : SignCube m) : EuclideanSpace ℂ (Fin (m + 1)) :=
  WithLp.toLp 2 (Fin.cons (Real.sqrt (1 - (m : ℝ) * a ^ 2) : ℂ)
    (fun j => ((a * cubeSign θ j : ℝ) : ℂ)))

@[simp] theorem cubeVector_zero {m : ℕ} (a : ℝ) (θ : SignCube m) :
    cubeVector m a θ 0 = (Real.sqrt (1 - (m : ℝ) * a ^ 2) : ℂ) := rfl

@[simp] theorem cubeVector_succ {m : ℕ} (a : ℝ) (θ : SignCube m) (j : Fin m) :
    cubeVector m a θ j.succ = ((a * cubeSign θ j : ℝ) : ℂ) := rfl

theorem cubeVector_norm {m : ℕ} (a : ℝ) (θ : SignCube m)
    (ha : (m : ℝ) * a ^ 2 ≤ 1) : ‖cubeVector m a θ‖ = 1 := by
  have hs : ‖cubeVector m a θ‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
    simp only [cubeVector_zero, cubeVector_succ, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, Real.sq_sqrt (sub_nonneg.mpr ha), mul_pow, cubeSign_sq, mul_one]
    simp
  nlinarith [norm_nonneg (cubeVector m a θ)]

def cubeState {m : ℕ} (a : ℝ) (ha : (m : ℝ) * a ^ 2 ≤ 1) (θ : SignCube m) :
    DensityOperator (Fin (m + 1)) :=
  complexSpherePureState ⟨cubeVector m a θ, by simpa [mem_sphere] using cubeVector_norm a θ ha⟩

theorem cubeState_rank_le_one {m : ℕ} (a : ℝ) (ha : (m : ℝ) * a ^ 2 ≤ 1)
    (θ : SignCube m) : (cubeState a ha θ).matrix.rank ≤ 1 :=
  complexSphereProjector_rank_le_one _

@[simp] theorem cubeState_column {m : ℕ} (a : ℝ) (ha : (m : ℝ) * a ^ 2 ≤ 1)
    (θ : SignCube m) (j : Fin m) :
    (cubeState a ha θ).matrix j.succ 0 =
      ((Real.sqrt (1 - (m : ℝ) * a ^ 2) * a * cubeSign θ j : ℝ) : ℂ) := by
  change cubeVector m a θ j.succ * star (cubeVector m a θ 0) = _
  simp only [cubeVector_succ, cubeVector_zero, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
  congr 1
  ring

theorem cubeVector_neighbor_norm_sq {m : ℕ} (a : ℝ) (θ : SignCube m) (j : Fin m) :
    ‖cubeVector m a θ - cubeVector m a (cubeFlip j θ)‖ ^ 2 = 4 * a ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  simp only [PiLp.sub_apply, cubeVector_zero, sub_self, norm_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, cubeVector_succ, zero_add]
  rw [Finset.sum_eq_single j]
  · unfold cubeSign
    cases h : θ j <;> simp [h] <;> ring_nf <;>
      simp [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs] <;> ring_nf <;> simp
  · intro i hi hij
    simp [cubeFlip_other, hij, cubeSign]
  · simp

def decodedCubeSign {m : ℕ} (σ : DensityOperator (Fin (m + 1))) (j : Fin m) : Bool :=
  decide (0 ≤ (σ.matrix j.succ 0).re)

theorem measurable_decodedCubeSign {m : ℕ} (j : Fin m) :
    Measurable (fun σ : DensityOperator (Fin (m + 1)) => decodedCubeSign σ j) := by
  unfold decodedCubeSign
  apply measurable_to_countable'
  intro b
  have hs := measurableSet_le (measurable_const (a := (0 : ℝ)))
    (Complex.measurable_re.comp (PhysicalPOVM.measurable_densityOperator_apply (m + 1) j.succ 0))
  cases b
  · convert hs.compl using 1
    ext σ
    simp
  · convert hs using 1
    ext σ
    simp

def cubeBitError {m : ℕ} (θ : SignCube m) (σ : DensityOperator (Fin (m + 1)))
    (j : Fin m) : ℝ := if decodedCubeSign σ j = θ j then 0 else 1

def cubeHamming {m : ℕ} (θ : SignCube m) (σ : DensityOperator (Fin (m + 1))) : ℝ :=
  ∑ j, cubeBitError θ σ j

theorem cube_wrong_sign_entry {m : ℕ} (a : ℝ) (ha0 : 0 ≤ a)
    (ha : (m : ℝ) * a ^ 2 ≤ 1) (θ : SignCube m)
    (σ : DensityOperator (Fin (m + 1))) (j : Fin m) :
    Real.sqrt (1 - (m : ℝ) * a ^ 2) * a * cubeBitError θ σ j ≤
      ‖(σ.matrix - (cubeState a ha θ).matrix) j.succ 0‖ := by
  have hha : 0 ≤ Real.sqrt (1 - (m : ℝ) * a ^ 2) * a := mul_nonneg (Real.sqrt_nonneg _) ha0
  have hr := Complex.abs_re_le_norm ((σ.matrix - (cubeState a ha θ).matrix) j.succ 0)
  simp only [Matrix.sub_apply, cubeState_column, Complex.sub_re, Complex.ofReal_re] at hr
  unfold cubeBitError decodedCubeSign cubeSign at *
  cases hθ : θ j <;> by_cases hσ : 0 ≤ (σ.matrix j.succ 0).re
  · simp [hθ, hσ, cubeSign]
    simp [hθ] at hr
    rw [abs_of_nonneg (by linarith)] at hr
    linarith
  · simp [hθ, hσ]
  · simp [hθ, hσ]
  · simp [hθ, hσ, cubeSign]
    simp [hθ] at hr
    rw [abs_of_nonpos (by linarith)] at hr
    linarith

/-- One matrix column is controlled by the full Frobenius norm. -/
theorem cube_column_sum_le {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :
    (∑ j : Fin m, ‖A j.succ 0‖) ≤ Real.sqrt m * ‖Revision.MatrixSolver.encode A‖ := by
  have hs := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (f := fun _ : Fin m => (1 : ℝ)) (g := fun j => ‖A j.succ 0‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hs
  have hcol : (∑ j : Fin m, ‖A j.succ 0‖ ^ 2) ≤
      ‖Revision.MatrixSolver.encode A‖ ^ 2 := by
    rw [Revision.MatrixSolver.norm_encode_sq]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_succ]
    have ht : (∑ j : Fin m, ‖A j.succ 0‖ ^ 2) ≤
        ∑ j : Fin m, (‖A j.succ 0‖ ^ 2 + ∑ k : Fin m, ‖A j.succ k.succ‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro j hj
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hh : 0 ≤ ‖A 0 0‖ ^ 2 + ∑ k : Fin m, ‖A 0 k.succ‖ ^ 2 := by positivity
    linarith
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hsq : (Real.sqrt (m : ℝ) * ‖Revision.MatrixSolver.encode A‖) ^ 2 =
      (m : ℝ) * ‖Revision.MatrixSolver.encode A‖ ^ 2 := by rw [mul_pow, Real.sq_sqrt hm]
  apply (sq_le_sq₀ (Finset.sum_nonneg fun _ _ => norm_nonneg _) (by positivity)).1
  rw [hsq]
  exact hs.trans (mul_le_mul_of_nonneg_left hcol hm)

/-- Pointwise trace-loss-to-Hamming comparison, including mixed estimates. -/
theorem cube_hamming_le_trace {m : ℕ} (a : ℝ) (ha0 : 0 ≤ a)
    (ha : (m : ℝ) * a ^ 2 ≤ 1) (θ : SignCube m)
    (σ : DensityOperator (Fin (m + 1))) :
    Real.sqrt (1 - (m : ℝ) * a ^ 2) * a * cubeHamming θ σ ≤
      Real.sqrt m * hermitianTraceNorm (σ.matrix - (cubeState a ha θ).matrix)
        (σ.sub_isHermitian (cubeState a ha θ)) := by
  calc
    _ = ∑ j, Real.sqrt (1 - (m : ℝ) * a ^ 2) * a * cubeBitError θ σ j := by
      simp [cubeHamming, Finset.mul_sum]
    _ ≤ ∑ j : Fin m, ‖(σ.matrix - (cubeState a ha θ).matrix) j.succ 0‖ :=
      Finset.sum_le_sum fun j _ => cube_wrong_sign_entry a ha0 ha θ σ j
    _ ≤ Real.sqrt m * ‖Revision.MatrixSolver.encode (σ.matrix - (cubeState a ha θ).matrix)‖ :=
      cube_column_sum_le _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Revision.FinitePrecision.norm_encode_le_hermitianTraceNorm _ _) (Real.sqrt_nonneg _)

end
end TomographyOracleCore.PaperMatch.RankMinimax
