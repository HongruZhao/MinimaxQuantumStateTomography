import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Tactic
import TomographyOracleCore.PortedScalarGammaBetaBridge

/-!
# Fixed-subspace projections of a standard Gaussian vector

This file isolates the Hilbert-space probability layer of the
Gaussian-to-Beta bridge.  A standard Gaussian vector is projected onto a
fixed subspace and its orthogonal complement.  We prove that both projections
are standard Gaussian and independent.  Consequently, all measurable scalar
functions of the two projections, in particular their squared norms, are
independent.

Mathematical provenance: this is a coordinate-free formalization of the
fixed-past Gaussian projection step in Rouault (2005), proof of Proposition
2.1, printed p. 6.  Its classical quadratic-form ancestor is Cochran (1934).
Lean proves the result directly from Gaussian covariance and orthogonal
projection theorems rather than importing Cochran's theorem.  See
`PROVENANCE.md` for the exact source relationship.
-/

namespace LogdetLean

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Sum of the squared coordinates of a finite real tuple. -/
private def finSumSq (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, (x i) ^ 2

private theorem measurable_finSumSq (n : ℕ) : Measurable (finSumSq n) := by
  unfold finSumSq
  fun_prop

/-- The sum of squares of `n+1` independent standard real Gaussians has the
Gamma law with shape `(n+1)/2` and rate `1/2`. -/
private theorem hasLaw_finSumSq_pi_standardGaussian (n : ℕ) :
    HasLaw (finSumSq (n + 1))
      (gammaMeasure (((n + 1 : ℕ) : ℝ) / 2) (1 / 2))
      (Measure.pi fun _ : Fin (n + 1) ↦ gaussianReal 0 1) := by
  induction n with
  | zero =>
      have hcoord : HasLaw (fun x : Fin 1 → ℝ ↦ x 0) (gaussianReal 0 1)
          (Measure.pi fun _ : Fin 1 ↦ gaussianReal 0 1) :=
        (measurePreserving_eval (fun _ : Fin 1 ↦ gaussianReal 0 1) 0).hasLaw
      have hsquare := LogdetLean.HasLaw.sq_standardGaussian hcoord
      convert hsquare using 1
      · funext x
        simp [finSumSq]
      · norm_num
  | succ n ih =>
      let Pn : Measure (Fin (n + 1) → ℝ) :=
        Measure.pi fun _ : Fin (n + 1) ↦ gaussianReal 0 1
      let Psucc : Measure (Fin (n + 2) → ℝ) :=
        Measure.pi fun _ : Fin (n + 2) ↦ gaussianReal 0 1
      let split : (Fin (n + 2) → ℝ) → ℝ × (Fin (n + 1) → ℝ) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) ↦ ℝ) 0
      have hsplit : HasLaw split ((gaussianReal 0 1).prod Pn) Psucc := by
        exact (measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 2) ↦ gaussianReal 0 1) 0).hasLaw
      let X : ℝ × (Fin (n + 1) → ℝ) → ℝ := fun z ↦ z.1 ^ 2
      let Y : ℝ × (Fin (n + 1) → ℝ) → ℝ := fun z ↦ finSumSq (n + 1) z.2
      have hX : HasLaw X (gammaMeasure (1 / 2) (1 / 2))
          ((gaussianReal 0 1).prod Pn) := by
        have hfst : HasLaw Prod.fst (gaussianReal 0 1)
            ((gaussianReal 0 1).prod Pn) := measurePreserving_fst.hasLaw
        simpa [X] using LogdetLean.HasLaw.sq_standardGaussian hfst
      have hY : HasLaw Y
          (gammaMeasure (((n + 1 : ℕ) : ℝ) / 2) (1 / 2))
          ((gaussianReal 0 1).prod Pn) := by
        have hsnd : HasLaw Prod.snd Pn ((gaussianReal 0 1).prod Pn) :=
          measurePreserving_snd.hasLaw
        simpa [Y, Pn] using ih.fun_comp hsnd
      have hXY : IndepFun X Y ((gaussianReal 0 1).prod Pn) := by
        simpa [X, Y] using indepFun_prod
          (show Measurable (fun z : ℝ ↦ z ^ 2) by fun_prop)
          (measurable_finSumSq (n + 1))
      have hsum := LogdetLean.IndepFun.hasLaw_add_gamma
        (by norm_num : (0 : ℝ) < 1 / 2)
        (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) / 2)
        (by norm_num : (0 : ℝ) < 1 / 2) hX hY hXY
      have hcomp := hsum.fun_comp hsplit
      convert hcomp using 1
      · funext x
        simp [X, Y, split, finSumSq, Fin.sum_univ_succ, Fin.tail]
      · congr 2
        push_cast
        ring

/-- The exact squared-norm pushforward of standard Gaussian measure.  A later
scalar theorem identifies this measure with a Gamma measure; keeping this
definition here lets the fixed-subspace argument remain independent of that
analytic identification. -/
def stdGaussianNormSqMeasure (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] : Measure ℝ :=
  (stdGaussian F).map (fun z ↦ ‖z‖ ^ 2)

/-- By definition, the squared norm of a standard Gaussian has the
`stdGaussianNormSqMeasure` law. -/
theorem hasLaw_normSq_stdGaussian (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] :
    HasLaw (fun z : F ↦ ‖z‖ ^ 2) (stdGaussianNormSqMeasure F) (stdGaussian F) :=
  ⟨by fun_prop, rfl⟩

/-- In Euclidean dimension `n+1`, the squared norm of a standard Gaussian is
Gamma with shape `(n+1)/2` and rate `1/2`. -/
private theorem stdGaussianNormSqMeasure_euclidean_finSucc (n : ℕ) :
    stdGaussianNormSqMeasure (EuclideanSpace ℝ (Fin (n + 1))) =
      gammaMeasure (((n + 1 : ℕ) : ℝ) / 2) (1 / 2) := by
  let P : Measure (Fin (n + 1) → ℝ) :=
    Measure.pi fun _ : Fin (n + 1) ↦ gaussianReal 0 1
  calc
    stdGaussianNormSqMeasure (EuclideanSpace ℝ (Fin (n + 1))) =
        Measure.map (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦ ‖z‖ ^ 2)
          (Measure.map (WithLp.toLp 2) P) := by
      rw [stdGaussianNormSqMeasure, map_pi_eq_stdGaussian]
    _ = Measure.map
        ((fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦ ‖z‖ ^ 2) ∘
          (WithLp.toLp 2)) P := by
      exact Measure.map_map (by fun_prop) (by fun_prop)
    _ = Measure.map (finSumSq (n + 1)) P := by
      congr 1
      funext x
      simpa [finSumSq, Function.comp_def] using
        EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 x)
    _ = gammaMeasure (((n + 1 : ℕ) : ℝ) / 2) (1 / 2) :=
      (hasLaw_finSumSq_pi_standardGaussian n).map_eq

/-- In every nonzero finite-dimensional real inner-product space, the
squared norm of a standard Gaussian has the Gamma law with shape half the
dimension and rate `1/2`. -/
theorem stdGaussianNormSqMeasure_eq_gamma (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] [Nontrivial F] :
    stdGaussianNormSqMeasure F =
      gammaMeasure ((Module.finrank ℝ F : ℝ) / 2) (1 / 2) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Module.finrank ℝ F = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt (show 0 < Module.finrank ℝ F from Module.finrank_pos))
  let b : OrthonormalBasis (Fin (n + 1)) ℝ F :=
    (stdOrthonormalBasis ℝ F).reindex (finCongr hn)
  calc
    stdGaussianNormSqMeasure F =
        Measure.map (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦ ‖z‖ ^ 2)
          ((stdGaussian F).map b.repr) := by
      rw [stdGaussianNormSqMeasure, Measure.map_map]
      · congr 1
        funext x
        simp
      all_goals fun_prop
    _ = stdGaussianNormSqMeasure (EuclideanSpace ℝ (Fin (n + 1))) := by
      rw [stdGaussian_map b.repr]
      rfl
    _ = gammaMeasure (((n + 1 : ℕ) : ℝ) / 2) (1 / 2) :=
      stdGaussianNormSqMeasure_euclidean_finSucc n
    _ = gammaMeasure ((Module.finrank ℝ F : ℝ) / 2) (1 / 2) := by
      rw [hn]

/-- The orthogonal projection of a standard Gaussian vector onto a fixed
subspace is a standard Gaussian vector in that subspace. -/
theorem hasLaw_orthogonalProjectionOnto_stdGaussian (K : Submodule ℝ E) :
    HasLaw K.orthogonalProjectionOnto (stdGaussian K) (stdGaussian E) := by
  refine ⟨by fun_prop, ?_⟩
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id,
      integral_id_stdGaussian, integral_id_stdGaussian]
    simp
  · ext u v
    rw [covarianceBilin_map IsGaussian.memLp_two_id,
      covarianceBilin_stdGaussian, covarianceBilin_stdGaussian,
      K.adjoint_orthogonalProjectionOnto]
    change ⟪(u : E), (v : E)⟫ = ⟪(u : E), (v : E)⟫
    rfl

/-- The projection onto the orthogonal complement is likewise standard
Gaussian in that complement. -/
theorem hasLaw_orthogonalComplementProjection_stdGaussian (K : Submodule ℝ E) :
    HasLaw Kᗮ.orthogonalProjectionOnto (stdGaussian Kᗮ) (stdGaussian E) :=
  hasLaw_orthogonalProjectionOnto_stdGaussian Kᗮ

/-- The two orthogonal projections of a standard Gaussian vector are
independent. -/
theorem indepFun_orthogonalProjections_stdGaussian (K : Submodule ℝ E) :
    IndepFun K.orthogonalProjectionOnto Kᗮ.orthogonalProjectionOnto (stdGaussian E) := by
  have hpair : HasGaussianLaw
      (fun x : E ↦ (K.orthogonalProjectionOnto x,
        Kᗮ.orthogonalProjectionOnto x)) (stdGaussian E) :=
    IsGaussian.hasGaussianLaw_id.map_fun
      (K.orthogonalProjectionOnto.prod Kᗮ.orthogonalProjectionOnto)
  refine hpair.indepFun_of_covariance_inner fun u v ↦ ?_
  have hu : (fun x : E ↦ ⟪u, K.orthogonalProjectionOnto x⟫) =
      (fun x : E ↦ ⟪u.1, x⟫) := by
    funext x
    exact K.inner_orthogonalProjectionOnto_eq_of_mem_left u x
  have hv : (fun x : E ↦ ⟪v, Kᗮ.orthogonalProjectionOnto x⟫) =
      (fun x : E ↦ ⟪v.1, x⟫) := by
    funext x
    exact Kᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left v x
  rw [hu, hv, ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian, innerSL_apply_apply]
  exact v.property u u.property

/-- The joint law of the two projections is the product of the two standard
Gaussian laws. -/
theorem hasLaw_orthogonalProjections_prod_stdGaussian (K : Submodule ℝ E) :
    HasLaw (fun x : E ↦ (K.orthogonalProjectionOnto x,
      Kᗮ.orthogonalProjectionOnto x))
      ((stdGaussian K).prod (stdGaussian Kᗮ)) (stdGaussian E) := by
  exact (indepFun_orthogonalProjections_stdGaussian K).hasLaw_prod
    (hasLaw_orthogonalProjectionOnto_stdGaussian K)
    (hasLaw_orthogonalComplementProjection_stdGaussian K)

/-- Squared norms of the two fixed orthogonal projections are independent. -/
theorem indepFun_normSq_orthogonalProjections_stdGaussian (K : Submodule ℝ E) :
    IndepFun (fun x : E ↦ ‖K.orthogonalProjectionOnto x‖ ^ 2)
      (fun x : E ↦ ‖Kᗮ.orthogonalProjectionOnto x‖ ^ 2)
      (stdGaussian E) := by
  have h := IndepFun.comp (indepFun_orthogonalProjections_stdGaussian K)
    (φ := fun z : K ↦ ‖z‖ ^ 2) (ψ := fun z : Kᗮ ↦ ‖z‖ ^ 2)
    (by fun_prop) (by fun_prop)
  simpa [Function.comp_def] using h

/-- Each projected squared norm has the exact squared-norm pushforward law. -/
theorem hasLaw_normSq_orthogonalProjection_stdGaussian (K : Submodule ℝ E) :
    HasLaw (fun x : E ↦ ‖K.orthogonalProjectionOnto x‖ ^ 2)
      (stdGaussianNormSqMeasure K) (stdGaussian E) := by
  exact (hasLaw_normSq_stdGaussian K).fun_comp
    (hasLaw_orthogonalProjectionOnto_stdGaussian K)

/-- The same exact law statement for the orthogonal-complement energy. -/
theorem hasLaw_normSq_orthogonalComplementProjection_stdGaussian
    (K : Submodule ℝ E) :
    HasLaw (fun x : E ↦ ‖Kᗮ.orthogonalProjectionOnto x‖ ^ 2)
      (stdGaussianNormSqMeasure Kᗮ) (stdGaussian E) := by
  exact (hasLaw_normSq_stdGaussian Kᗮ).fun_comp
    (hasLaw_orthogonalComplementProjection_stdGaussian K)

/-- The joint law of the two projected squared norms is the product of their
exact squared-norm pushforward laws. -/
theorem hasLaw_normSq_orthogonalProjections_prod_stdGaussian
    (K : Submodule ℝ E) :
    HasLaw (fun x : E ↦ (‖K.orthogonalProjectionOnto x‖ ^ 2,
      ‖Kᗮ.orthogonalProjectionOnto x‖ ^ 2))
      ((stdGaussianNormSqMeasure K).prod (stdGaussianNormSqMeasure Kᗮ))
      (stdGaussian E) := by
  exact (indepFun_normSq_orthogonalProjections_stdGaussian K).hasLaw_prod
    (hasLaw_normSq_orthogonalProjection_stdGaussian K)
    (hasLaw_normSq_orthogonalComplementProjection_stdGaussian K)

/-- If the fixed subspace is nonzero, its projected squared norm has the
Gamma law with shape half its dimension and rate `1/2`. -/
theorem hasLaw_normSq_orthogonalProjection_gamma (K : Submodule ℝ E)
    [Nontrivial K] :
    HasLaw (fun x : E ↦ ‖K.orthogonalProjectionOnto x‖ ^ 2)
      (gammaMeasure ((Module.finrank ℝ K : ℝ) / 2) (1 / 2))
      (stdGaussian E) := by
  rw [← stdGaussianNormSqMeasure_eq_gamma K]
  exact hasLaw_normSq_orthogonalProjection_stdGaussian K

/-- If the orthogonal complement is nonzero, its projected squared norm has
the corresponding Gamma law. -/
theorem hasLaw_normSq_orthogonalComplementProjection_gamma
    (K : Submodule ℝ E) [Nontrivial Kᗮ] :
    HasLaw (fun x : E ↦ ‖Kᗮ.orthogonalProjectionOnto x‖ ^ 2)
      (gammaMeasure ((Module.finrank ℝ Kᗮ : ℝ) / 2) (1 / 2))
      (stdGaussian E) := by
  rw [← stdGaussianNormSqMeasure_eq_gamma Kᗮ]
  exact hasLaw_normSq_orthogonalComplementProjection_stdGaussian K

/-- When both orthogonal pieces are nonzero, their squared norms have the
product of the two dimension-indexed Gamma laws. -/
theorem hasLaw_normSq_orthogonalProjections_prod_gamma
    (K : Submodule ℝ E) [Nontrivial K] [Nontrivial Kᗮ] :
    HasLaw (fun x : E ↦ (‖K.orthogonalProjectionOnto x‖ ^ 2,
      ‖Kᗮ.orthogonalProjectionOnto x‖ ^ 2))
      ((gammaMeasure ((Module.finrank ℝ K : ℝ) / 2) (1 / 2)).prod
        (gammaMeasure ((Module.finrank ℝ Kᗮ : ℝ) / 2) (1 / 2)))
      (stdGaussian E) := by
  exact (indepFun_normSq_orthogonalProjections_stdGaussian K).hasLaw_prod
    (hasLaw_normSq_orthogonalProjection_gamma K)
    (hasLaw_normSq_orthogonalComplementProjection_gamma K)

omit [MeasurableSpace E] [BorelSpace E] in
/-- Pythagoras for the two projected squared norms.  This deterministic
identity is the denominator identity in the later Beta-ratio step. -/
theorem normSq_eq_projection_add_orthogonalComplement (K : Submodule ℝ E)
    (x : E) :
    ‖x‖ ^ 2 = ‖K.orthogonalProjectionOnto x‖ ^ 2 +
      ‖Kᗮ.orthogonalProjectionOnto x‖ ^ 2 := by
  simpa [sq] using K.norm_sq_eq_add_norm_sq_projection x

/-- The fraction of total Gaussian energy lying in a nonzero fixed subspace
has the exact Beta law.  Its two shape parameters are half the dimensions of
the subspace and its orthogonal complement. -/
theorem hasLaw_orthogonalProjection_normSq_ratio_beta (K : Submodule ℝ E)
    [Nontrivial K] [Nontrivial Kᗮ] :
    HasLaw (fun x : E ↦ ‖K.orthogonalProjectionOnto x‖ ^ 2 / ‖x‖ ^ 2)
      (betaMeasure ((Module.finrank ℝ K : ℝ) / 2)
        ((Module.finrank ℝ Kᗮ : ℝ) / 2))
      (stdGaussian E) := by
  have ha : (0 : ℝ) < (Module.finrank ℝ K : ℝ) / 2 := by
    exact div_pos (Nat.cast_pos.mpr Module.finrank_pos) (by norm_num)
  have hb : (0 : ℝ) < (Module.finrank ℝ Kᗮ : ℝ) / 2 := by
    exact div_pos (Nat.cast_pos.mpr Module.finrank_pos) (by norm_num)
  have hratio := LogdetLean.IndepFun.hasLaw_gammaRatio
    ha hb (by norm_num : (0 : ℝ) < 1 / 2)
    (hasLaw_normSq_orthogonalProjection_gamma K)
    (hasLaw_normSq_orthogonalComplementProjection_gamma K)
    (indepFun_normSq_orthogonalProjections_stdGaussian K)
  convert hratio using 1
  funext x
  rw [normSq_eq_projection_add_orthogonalComplement K x]

end

end LogdetLean
