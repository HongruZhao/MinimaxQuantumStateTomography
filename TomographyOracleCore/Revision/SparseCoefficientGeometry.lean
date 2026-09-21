import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace TomographyOracleCore.Revision.SparseCoefficientGeometry

open scoped BigOperators InnerProductSpace
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def coefficientNorm (y : ι → ℝ) : ℝ := ‖WithLp.toLp 2 y‖
def support (y : ι → ℝ) : Finset ι := Finset.univ.filter fun i => y i ≠ 0
def Supported (y : ι → ℝ) (I : Finset ι) : Prop := ∀ i ∉ I, y i = 0
def restrict (I : Finset ι) (y : ι → ℝ) (i : ι) : ℝ := if i ∈ I then y i else 0

@[simp] theorem coefficientNorm_nonneg (y : ι → ℝ) : 0 ≤ coefficientNorm y := norm_nonneg _
@[simp] theorem coefficientNorm_sq (y : ι → ℝ) :
    coefficientNorm y ^ 2 = ∑ i, y i ^ 2 := EuclideanSpace.real_norm_sq_eq _
theorem coefficientNorm_eq_sqrt (y : ι → ℝ) :
    coefficientNorm y = Real.sqrt (∑ i, y i ^ 2) := by
  rw [← coefficientNorm_sq, Real.sqrt_sq (coefficientNorm_nonneg _)]
@[simp] theorem coefficientNorm_zero : coefficientNorm (0 : ι → ℝ) = 0 := by
  simp [coefficientNorm]
@[simp] theorem coefficientNorm_smul (a : ℝ) (y : ι → ℝ) :
    coefficientNorm (fun i => a * y i) = |a| * coefficientNorm y := by
  change ‖a • (WithLp.toLp 2 y : EuclideanSpace ℝ ι)‖ = _
  simp [norm_smul, coefficientNorm, Real.norm_eq_abs]
theorem coefficientNorm_eq_zero_iff (y : ι → ℝ) :
    coefficientNorm y = 0 ↔ y = 0 := by
  simp [coefficientNorm]

theorem coefficientNorm_normalized_le (y : ι → ℝ) :
    coefficientNorm (fun i => (coefficientNorm y)⁻¹ * y i) ≤ 1 := by
  rw [coefficientNorm_smul, abs_inv, abs_of_nonneg (coefficientNorm_nonneg y)]
  by_cases h : coefficientNorm y = 0 <;> simp [h]

@[simp] theorem mem_support {y : ι → ℝ} {i : ι} : i ∈ support y ↔ y i ≠ 0 := by
  simp [support]
@[simp] theorem support_zero : support (0 : ι → ℝ) = ∅ := by ext; simp
theorem support_subset_iff (y : ι → ℝ) (I : Finset ι) : support y ⊆ I ↔ Supported y I := by
  constructor
  · intro h i hi
    by_contra hne
    exact hi (h (mem_support.mpr hne))
  · intro h i hi
    by_contra hn
    exact (mem_support.mp hi) (h i hn)
@[simp] theorem supported_zero (I : Finset ι) : Supported (0 : ι → ℝ) I := by
  intro i hi; rfl
@[simp] theorem supported_univ (y : ι → ℝ) : Supported y Finset.univ := by
  intro i hi; exact False.elim (hi (Finset.mem_univ _))
@[simp] theorem supported_restrict (I : Finset ι) (y : ι → ℝ) : Supported (restrict I y) I := by
  intro i hi; simp [restrict, hi]
theorem restrict_eq_self {I : Finset ι} {y : ι → ℝ} (hy : Supported y I) : restrict I y = y := by
  funext i
  by_cases hi : i ∈ I
  · simp [restrict, hi]
  · simp [restrict, hi, hy i hi]
theorem restrict_sub (I : Finset ι) (y z : ι → ℝ) :
    restrict I (fun i => y i - z i) = fun i => restrict I y i - restrict I z i := by
  funext i
  by_cases hi : i ∈ I <;> simp [restrict, hi]
theorem supported_restrict_of_supported {I : Finset ι} {y : ι → ℝ}
    (hy : Supported y I) (J : Finset ι) : Supported (restrict J y) I := by
  intro i hi
  by_cases hj : i ∈ J <;> simp [restrict, hj, hy i hi]
theorem support_smul_subset (a : ℝ) (y : ι → ℝ) :
    support (fun i => a * y i) ⊆ support y := by
  intro i hi
  exact mem_support.mpr (fun hz => (mem_support.mp hi) (by simp [hz]))
theorem supported_smul (a : ℝ) {y : ι → ℝ} {I : Finset ι} (hy : Supported y I) :
    Supported (fun i => a * y i) I := by
  intro i hi; simp [hy i hi]
theorem supported_sub {y z : ι → ℝ} {I : Finset ι}
    (hy : Supported y I) (hz : Supported z I) : Supported (fun i => y i - z i) I := by
  intro i hi; simp [hy i hi, hz i hi]
theorem coefficientNorm_restrict_le (I : Finset ι) (y : ι → ℝ) :
    coefficientNorm (restrict I y) ≤ coefficientNorm y := by
  apply (sq_le_sq₀ (coefficientNorm_nonneg _) (coefficientNorm_nonneg _)).mp
  simp only [coefficientNorm_sq]
  apply Finset.sum_le_sum
  intro i hi
  by_cases h : i ∈ I <;> simp [restrict, h, sq_nonneg]
theorem coefficientNorm_restrict_sq (I : Finset ι) (y : ι → ℝ) :
    coefficientNorm (restrict I y) ^ 2 = ∑ i ∈ I, y i ^ 2 := by
  rw [coefficientNorm_sq]
  simp [restrict, Finset.sum_filter]
theorem support_restrict_subset (I : Finset ι) (y : ι → ℝ) :
    support (restrict I y) ⊆ support y := by
  intro i hi
  by_cases h : i ∈ I
  · simpa [restrict, h] using hi
  · simp [restrict, h] at hi

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def synthesis (X : ι → E) (y : ι → ℝ) : E := ∑ i, y i • X i
@[simp] theorem synthesis_zero (X : ι → E) : synthesis X (0 : ι → ℝ) = 0 := by
  simp [synthesis]
theorem synthesis_smul (X : ι → E) (a : ℝ) (y : ι → ℝ) :
    synthesis X (fun i => a * y i) = a • synthesis X y := by
  simp [synthesis, mul_smul, Finset.smul_sum]
theorem synthesis_sub (X : ι → E) (y z : ι → ℝ) :
    synthesis X (fun i => y i - z i) = synthesis X y - synthesis X z := by
  simp [synthesis, sub_smul, Finset.sum_sub_distrib]
theorem synthesis_restrict (X : ι → E) (y : ι → ℝ) (I : Finset ι) :
    synthesis X (restrict I y) = ∑ i ∈ I, y i • X i := by
  simp [synthesis, restrict, Finset.sum_filter]
theorem synthesis_eq_sum_subtype (X : ι → E) (y : ι → ℝ) (I : Finset ι)
    (hy : Supported y I) : (∑ i : I, y i • X i) = synthesis X y := by
  rw [Finset.sum_coe_sort I (fun i => y i • X i)]
  apply Finset.sum_subset (Finset.subset_univ I)
  intro i hi hni
  simp [hy i hni]
theorem synthesis_restrict_add_compl (X : ι → E) (y : ι → ℝ) (I : Finset ι) :
    synthesis X (restrict I y) + synthesis X (restrict Iᶜ y) = synthesis X y := by
  simp only [synthesis, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : i ∈ I <;> simp [restrict, h]
theorem synthesis_eq_sum_support (X : ι → E) (y : ι → ℝ) :
    synthesis X y = ∑ i ∈ support y, y i • X i := by
  simp only [synthesis, support, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : y i = 0 <;> simp [h]
theorem inner_synthesis_left (X : ι → E) (y : ι → ℝ) (v : E) :
    ⟪synthesis X y, v⟫_ℝ = ∑ i, y i * ⟪X i, v⟫_ℝ := by
  simp [synthesis, sum_inner, real_inner_smul_left]
theorem inner_synthesis_right (X : ι → E) (y : ι → ℝ) (v : E) :
    ⟪v, synthesis X y⟫_ℝ = ∑ i, y i * ⟪v, X i⟫_ℝ := by
  simp [synthesis, inner_sum, real_inner_smul_right]

theorem synthesis_norm_le (X : ι → E) (y : ι → ℝ) :
    ‖synthesis X y‖ ≤ coefficientNorm y * Real.sqrt (∑ i, ‖X i‖ ^ 2) := by
  calc
    ‖synthesis X y‖ ≤ ∑ i, |y i| * ‖X i‖ := by
      simpa [synthesis, norm_smul, Real.norm_eq_abs] using
        norm_sum_le (Finset.univ : Finset ι) (fun i => y i • X i)
    _ ≤ Real.sqrt (∑ i, |y i| ^ 2) * Real.sqrt (∑ i, ‖X i‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by simp only [sq_abs, ← coefficientNorm_eq_sqrt]

theorem sum_abs_le_sqrt_card_mul_norm (y : ι → ℝ) :
    (∑ i, |y i|) ≤ Real.sqrt ((support y).card : ℝ) * coefficientNorm y := by
  have hs : (∑ i, |y i|) = ∑ i ∈ support y, |y i| := by
    simp only [support, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : y i = 0 <;> simp [h]
  have hq : (∑ i ∈ support y, |y i| ^ 2) = ∑ i, y i ^ 2 := by
    simp only [support, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : y i = 0 <;> simp [h, sq_abs]
  rw [hs]
  calc
    (∑ i ∈ support y, |y i|) = ∑ i ∈ support y, (1 : ℝ) * |y i| := by simp
    _ ≤ Real.sqrt (∑ _i ∈ support y, (1 : ℝ) ^ 2) *
          Real.sqrt (∑ i ∈ support y, |y i| ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by rw [hq, ← coefficientNorm_eq_sqrt]; simp

end
end TomographyOracleCore.Revision.SparseCoefficientGeometry
