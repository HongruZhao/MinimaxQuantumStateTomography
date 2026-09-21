import TomographyOracleCore.Revision.EuclideanBallFiniteNet
import TomographyOracleCore.Revision.SparseCoefficientGeometry
import TomographyOracleCore.Revision.BinomialEntropyBound

set_option backward.isDefEq.respectTransparency false

namespace TomographyOracleCore.Revision.SupportedCoefficientNets

open SparseCoefficientGeometry EuclideanBallFiniteNet
open scoped BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def extend (S : Finset ι) (v : EuclideanSpace ℝ S) (i : ι) : ℝ :=
  if h : i ∈ S then v ⟨i, h⟩ else 0

theorem extend_supported (S : Finset ι) (v : EuclideanSpace ℝ S) : Supported (extend S v) S := by
  intro i hi
  simp [extend, hi]

theorem sum_extend_sq (S : Finset ι) (v : EuclideanSpace ℝ S) :
    (∑ i, extend S v i ^ 2) = ∑ i : S, v i ^ 2 := by
  calc
    _ = ∑ i ∈ S, extend S v i ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro i hi hni
      simp [extend, hni]
    _ = ∑ i : S, extend S v i ^ 2 := (Finset.sum_coe_sort S _).symm
    _ = _ := by apply Finset.sum_congr rfl; intro i hi; simp [extend]

theorem coefficientNorm_extend (S : Finset ι) (v : EuclideanSpace ℝ S) :
    coefficientNorm (extend S v) = ‖v‖ := by
  apply (sq_eq_sq₀ (coefficientNorm_nonneg _) (norm_nonneg _)).mp
  rw [coefficientNorm_sq, sum_extend_sq, EuclideanSpace.real_norm_sq_eq]

theorem extend_sub (S : Finset ι) (v w : EuclideanSpace ℝ S) :
    extend S (v - w) = fun i => extend S v i - extend S w i := by
  funext i
  by_cases hi : i ∈ S <;> simp [extend, hi]

theorem extend_restriction {S : Finset ι} {y : ι → ℝ} (hy : Supported y S) :
    extend S (WithLp.toLp 2 (fun i : S => y i)) = y := by
  funext i
  by_cases hi : i ∈ S
  · simp [extend, hi]
  · simp [extend, hi, hy i hi]

/-- A finite net that preserves a prescribed coordinate support. -/
theorem exists_supported_net (S : Finset ι) {eta : ℝ} (heta : 0 < eta) :
    ∃ net : Finset (ι → ℝ),
      (∀ v ∈ net, Supported v S ∧ coefficientNorm v ≤ 1) ∧
      (∀ y : ι → ℝ, Supported y S → coefficientNorm y ≤ 1 →
        ∃ v ∈ net, coefficientNorm (fun i => y i - v i) ≤ eta) ∧
      (net.card : ℝ) ≤ (1 + 2 / eta) ^ S.card := by
  classical
  obtain ⟨net, hunit, hcover, hcard⟩ :=
    exists_unitBall_finset_net_card_le (E := EuclideanSpace ℝ S) heta
  refine ⟨net.image (extend S), ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨extend_supported S w, by rw [coefficientNorm_extend]; exact hunit w hw⟩
  · intro y hy hyn
    let w : EuclideanSpace ℝ S := WithLp.toLp 2 (fun i : S => y i)
    have heq : extend S w = y := extend_restriction hy
    have hw : ‖w‖ ≤ 1 := by rw [← coefficientNorm_extend, heq]; exact hyn
    obtain ⟨v, hv, hd⟩ := hcover w hw
    refine ⟨extend S v, Finset.mem_image.mpr ⟨v, hv, rfl⟩, ?_⟩
    rw [← heq, ← extend_sub, coefficientNorm_extend]
    exact hd
  · have hc : ((net.image (extend S)).card : ℝ) ≤ net.card := by
      exact_mod_cast Finset.card_image_le
    exact hc.trans (by simpa using hcard)

end
end TomographyOracleCore.Revision.SupportedCoefficientNets
