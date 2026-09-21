import TomographyOracleCore.ProjectiveHaarFirstMoment
import TomographyOracleCore.UnitaryHaarSphereOrbit
import TomographyOracleCore.PaperMatch.RankThreeLower

/-! Actual pure states in a small spherical cap. These are geometric
ingredients for the remaining rank-one statistical lower bound, not an
assertion of that lower bound. -/
namespace TomographyOracleCore.PaperMatch.RankMinimax
open MeasureTheory ProbabilityTheory MatrixReduction Metric Set
open scoped BigOperators ENNReal ComplexOrder InnerProductSpace
noncomputable section
set_option maxHeartbeats 1000000

/-- One head amplitude and a k-dimensional tail of squared mass b. -/
def pureCapVector {k : ℕ} (b : ℝ)
    (v : sphere (0 : EuclideanSpace ℂ (Fin k)) 1) :
    EuclideanSpace ℂ (Fin (k + 1)) :=
  WithLp.toLp 2 (Fin.cons (Real.sqrt (1 - b) : ℂ)
    (fun j => (Real.sqrt b : ℂ) * v.1 j))

@[simp] theorem pureCapVector_zero {k : ℕ} (b : ℝ)
    (v : sphere (0 : EuclideanSpace ℂ (Fin k)) 1) :
    pureCapVector b v 0 = (Real.sqrt (1 - b) : ℂ) := rfl

@[simp] theorem pureCapVector_succ {k : ℕ} (b : ℝ)
    (v : sphere (0 : EuclideanSpace ℂ (Fin k)) 1) (j : Fin k) :
    pureCapVector b v j.succ = (Real.sqrt b : ℂ) * v.1 j := rfl

lemma pureCapVector_norm {k : ℕ} {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (v : sphere (0 : EuclideanSpace ℂ (Fin k)) 1) :
    ‖pureCapVector b v‖ = 1 := by
  have hv : ‖v.1‖ = 1 := by simpa [mem_sphere] using v.2
  have hvs : ∑ j : Fin k, ‖v.1 j‖ ^ 2 = (1 : ℝ) := by
    simpa [hv] using (EuclideanSpace.norm_sq_eq v.1).symm
  have hs : ‖pureCapVector b v‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
    simp only [pureCapVector_zero, pureCapVector_succ, norm_mul, mul_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt hb, Real.sq_sqrt (sub_nonneg.mpr hb1)]
    rw [← Finset.mul_sum, hvs]
    ring
  nlinarith [norm_nonneg (pureCapVector b v)]

/-- A genuine normalized vector, with normalization proved. -/
def pureCapSphere {k : ℕ} (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (v : sphere (0 : EuclideanSpace ℂ (Fin k)) 1) :
    sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1 :=
  ⟨pureCapVector b v, by simpa [mem_sphere] using pureCapVector_norm hb hb1 v⟩

/-- The actual positive trace-one matrix |psi><psi|. -/
def pureCapState {k : ℕ} (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (v : sphere (0 : EuclideanSpace ℂ (Fin k)) 1) :
    DensityOperator (Fin (k + 1)) := complexSpherePureState (pureCapSphere b hb hb1 v)

theorem pureCapState_rank_le_one {k : ℕ} (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (v : sphere (0 : EuclideanSpace ℂ (Fin k)) 1) :
    (pureCapState b hb hb1 v).matrix.rank ≤ 1 :=
  complexSphereProjector_rank_le_one _

theorem continuous_pureCapVector {k : ℕ} (b : ℝ) :
    Continuous (pureCapVector (k := k) b) := by
  unfold pureCapVector
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (k + 1) => ℂ)).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_const
  · change Continuous (fun v : sphere (0 : EuclideanSpace ℂ (Fin k)) 1 =>
      (Real.sqrt b : ℂ) * v.1 j)
    fun_prop

theorem measurable_pureCapState {k : ℕ} (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    Measurable (pureCapState (k := k) b hb hb1) := by
  rw [measurable_iff_comap_le, PhysicalPOVM.densityOperatorMeasurableSpace,
    MeasurableSpace.comap_comp]
  apply Measurable.comap_le
  apply measurable_pi_lambda
  intro ij
  change Measurable (fun v : sphere (0 : EuclideanSpace ℂ (Fin k)) 1 =>
    pureCapVector b v ij.1 * star (pureCapVector b v ij.2))
  have hentry (i : Fin (k + 1)) :
      Measurable (fun v : sphere (0 : EuclideanSpace ℂ (Fin k)) 1 => pureCapVector b v i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact measurable_const
    · change Measurable (fun v : sphere (0 : EuclideanSpace ℂ (Fin k)) 1 =>
        (Real.sqrt b : ℂ) * v.1 j)
      fun_prop
  apply (hentry ij.1).mul
  exact (Complex.continuous_conj.measurable).comp (hentry ij.2)

end
end TomographyOracleCore.PaperMatch.RankMinimax
