import TomographyOracleCore.PhysicalFiniteFanoKernel
import TomographyOracleCore.DensityCompact
import TomographyOracleCore.RobustNoise

namespace TomographyOracleCore

open MeasureTheory
open MatrixReduction PhysicalPOVM
open scoped ENNReal Matrix.Norms.L2Operator

/-!
# A measurable nearest-neighbor decoder in physical trace loss

The lower-bound bridge in `PhysicalFiniteFanoKernel` accepts any measurable
finite decoder whose errors force a prescribed trace loss.  This file
constructs that decoder.  Its score is the actual Hermitian Schatten-one
distance, not a coordinate or Frobenius proxy, so no dimension-dependent loss
is introduced in the packing radius.

The only subtlety is measurability.  The physical state space carries the
coordinate sigma-algebra from `PhysicalPOVM`, while its metric is induced by
the matrix operator norm in `DensityCompact`.  In finite dimension the curry
linear equivalence between matrices and their full coordinate vector is a
homeomorphism.  Consequently all metric-open state sets are coordinate
measurable.  The trace-loss score is Lipschitz in the operator-norm metric, and
the existing finite tie-broken argmin machinery then gives a measurable
decoder.

No declaration in this file is an axiom.
-/

namespace PhysicalRisk

/-! ## Trace-loss topology and measurability -/

/-- The real-valued Hermitian trace loss underlying `hermitianTraceLoss`. -/
noncomputable def realHermitianTraceLoss {D : ℕ}
    (ρ estimate : DensityOperator (Fin D)) : ℝ :=
  hermitianTraceNorm (estimate.matrix - ρ.matrix)
    (estimate.sub_isHermitian ρ)

theorem hermitianTraceLoss_eq_ofReal_realHermitianTraceLoss {D : ℕ}
    (ρ estimate : DensityOperator (Fin D)) :
    hermitianTraceLoss ρ estimate =
      ENNReal.ofReal (realHermitianTraceLoss ρ estimate) := by
  rfl

/-- On Hermitian matrices, the Schatten-one norm is at most dimension times
the operator norm.  This explicit finite-dimensional comparison is enough for
the trace-loss continuity argument. -/
theorem hermitianTraceNorm_le_card_mul_matrixOperatorNorm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    hermitianTraceNorm A hA ≤
      (Fintype.card ι : ℝ) * matrixOperatorNorm A := by
  have hspectral :
      matrixOperatorNorm A =
        ‖fun i ↦ ((hA.eigenvalues i : ℝ) : ℂ)‖ := by
    change ‖A‖ = _
    rw (occs := .pos [1]) [hA.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
      Matrix.l2_opNorm_diagonal]
    congr 1
  rw [hspectral]
  simpa [hermitianTraceNorm, Complex.norm_real, Real.norm_eq_abs,
    nsmul_eq_mul] using
    (Pi.sum_norm_apply_le_norm
      (fun i : ι ↦ ((hA.eigenvalues i : ℝ) : ℂ)))

/-- Reverse triangle inequality for the real physical trace loss. -/
theorem abs_realHermitianTraceLoss_sub_le {D : ℕ}
    (ρ x y : DensityOperator (Fin D)) :
    |realHermitianTraceLoss ρ x - realHermitianTraceLoss ρ y| ≤
      hermitianTraceNorm (x.matrix - y.matrix) (x.sub_isHermitian y) := by
  have hxy : realHermitianTraceLoss ρ x ≤
      hermitianTraceNorm (x.matrix - y.matrix) (x.sub_isHermitian y) +
        realHermitianTraceLoss ρ y := by
    have h := hermitianTraceNorm_triangle
      (x.matrix - y.matrix) (y.matrix - ρ.matrix)
      (x.sub_isHermitian y) (y.sub_isHermitian ρ)
    simpa [realHermitianTraceLoss] using h
  have hsymm :
      hermitianTraceNorm (y.matrix - x.matrix) (y.sub_isHermitian x) =
        hermitianTraceNorm (x.matrix - y.matrix) (x.sub_isHermitian y) := by
    have h := hermitianTraceNorm_neg
      (x.matrix - y.matrix) (x.sub_isHermitian y)
    simpa only [neg_sub] using h
  have hyx : realHermitianTraceLoss ρ y ≤
      hermitianTraceNorm (x.matrix - y.matrix) (x.sub_isHermitian y) +
        realHermitianTraceLoss ρ x := by
    have h := hermitianTraceNorm_triangle
      (y.matrix - x.matrix) (x.matrix - ρ.matrix)
      (y.sub_isHermitian x) (x.sub_isHermitian ρ)
    rw [hsymm] at h
    simpa [realHermitianTraceLoss] using h
  rw [abs_le]
  constructor <;> linarith

/-- The real trace-loss score is Lipschitz, hence continuous, in the induced
operator-norm metric on density operators. -/
theorem realHermitianTraceLoss_continuous {D : ℕ}
    (ρ : DensityOperator (Fin D)) :
    Continuous (realHermitianTraceLoss ρ) := by
  apply (LipschitzWith.of_dist_le_mul
    (K := ⟨D, Nat.cast_nonneg D⟩) (fun x y ↦ ?_)).continuous
  rw [Real.dist_eq]
  calc
    |realHermitianTraceLoss ρ x - realHermitianTraceLoss ρ y| ≤
        hermitianTraceNorm (x.matrix - y.matrix) (x.sub_isHermitian y) :=
      abs_realHermitianTraceLoss_sub_le ρ x y
    _ ≤ (D : ℝ) * matrixOperatorNorm (x.matrix - y.matrix) := by
      simpa using hermitianTraceNorm_le_card_mul_matrixOperatorNorm
        (x.matrix - y.matrix) (x.sub_isHermitian y)
    _ = (D : ℝ) * dist x y := by
      congr 1
      change matrixOperatorNorm (x.matrix - y.matrix) =
        dist x.matrix y.matrix
      rw [dist_eq_norm]
      rfl

/-- The coordinate sigma-algebra used by the physical kernel contains every
open set for the induced operator-norm metric. -/
noncomputable instance densityOperatorOpensMeasurableSpace (D : ℕ) :
    OpensMeasurableSpace (DensityOperator (Fin D)) := by
  rw [opensMeasurableSpace_iff_forall_measurableSet]
  intro s hs
  rw [isOpen_induced_iff] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  let e : Matrix (Fin D) (Fin D) ℂ ≃L[ℂ] (Fin D × Fin D → ℂ) :=
    (LinearEquiv.curry ℂ ℂ (Fin D) (Fin D)).symm.toContinuousLinearEquiv
  have hu : IsOpen (e '' t) := e.toHomeomorph.isOpen_image.mpr ht
  have heq :
      (DensityOperator.matrix ⁻¹' t : Set (DensityOperator (Fin D))) =
        densityCoordinates D ⁻¹' (e '' t) := by
    ext ρ
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro hρ
      exact ⟨ρ.matrix, hρ, by ext p; rfl⟩
    · rintro ⟨A, hA, hAe⟩
      have hmatrix : A = ρ.matrix := by
        apply e.injective
        rw [hAe]
        ext p
        rfl
      simpa [hmatrix] using hA
  rw [heq]
  exact hu.measurableSet.preimage (measurable_densityCoordinates D)

/-- The actual real physical trace loss is measurable for every fixed true
state. -/
theorem realHermitianTraceLoss_measurable {D : ℕ}
    (ρ : DensityOperator (Fin D)) :
    Measurable (realHermitianTraceLoss ρ) :=
  (realHermitianTraceLoss_continuous ρ).measurable

/-! ## The finite nearest-state decoder -/

/-- Deterministically tie-broken nearest hard-state label in the actual
Hermitian trace loss. -/
noncomputable def finiteTraceNearestDecoder
    {D N : ℕ} [NeZero N]
    (stateOf : Fin N → DensityOperator (Fin D))
    (estimate : DensityOperator (Fin D)) : Fin N :=
  finiteLeastArgmin (Finset.univ : Finset (Fin N)) Finset.univ_nonempty
    (fun a ↦ realHermitianTraceLoss (stateOf a) estimate)

theorem finiteTraceNearestDecoder_score_le
    {D N : ℕ} [NeZero N]
    (stateOf : Fin N → DensityOperator (Fin D))
    (estimate : DensityOperator (Fin D)) (a : Fin N) :
    realHermitianTraceLoss
        (stateOf (finiteTraceNearestDecoder stateOf estimate)) estimate ≤
      realHermitianTraceLoss (stateOf a) estimate := by
  exact finiteLeastArgmin_score_le
    (Finset.univ : Finset (Fin N)) Finset.univ_nonempty
    (fun b ↦ realHermitianTraceLoss (stateOf b) estimate)
    (Finset.mem_univ a)

/-- The finite nearest-state decoder is measurable.  Its fibers are finite
Boolean combinations of comparisons between the measurable trace-loss
scores. -/
theorem finiteTraceNearestDecoder_measurable
    {D N : ℕ} [NeZero N]
    (stateOf : Fin N → DensityOperator (Fin D)) :
    Measurable (finiteTraceNearestDecoder stateOf) := by
  classical
  apply measurable_to_countable'
  intro a
  change MeasurableSet {estimate |
    finiteLeastArgmin (Finset.univ : Finset (Fin N)) Finset.univ_nonempty
      (fun b ↦ realHermitianTraceLoss (stateOf b) estimate) = a}
  exact finiteLeastArgmin_fiber_measurable
    (Finset.univ : Finset (Fin N)) Finset.univ_nonempty
    (fun b estimate ↦ realHermitianTraceLoss (stateOf b) estimate)
    (fun b _hb ↦ realHermitianTraceLoss_measurable (stateOf b))
    (Finset.mem_univ a)

theorem realHermitianTraceLoss_symm {D : ℕ}
    (ρ σ : DensityOperator (Fin D)) :
    realHermitianTraceLoss ρ σ = realHermitianTraceLoss σ ρ := by
  have h := hermitianTraceNorm_neg
    (σ.matrix - ρ.matrix) (σ.sub_isHermitian ρ)
  simpa only [realHermitianTraceLoss, neg_sub] using h.symm

theorem realHermitianTraceLoss_triangle {D : ℕ}
    (ρ σ τ : DensityOperator (Fin D)) :
    realHermitianTraceLoss ρ τ ≤
      realHermitianTraceLoss ρ σ + realHermitianTraceLoss σ τ := by
  have h := hermitianTraceNorm_triangle
    (τ.matrix - σ.matrix) (σ.matrix - ρ.matrix)
    (τ.sub_isHermitian σ) (σ.sub_isHermitian ρ)
  simpa [realHermitianTraceLoss, add_comm] using h

/-- Under `2 * radius` pairwise separation in the actual trace loss, every
nearest-decoder error forces trace loss at least `radius`. -/
theorem radius_le_realHermitianTraceLoss_of_finiteTraceNearestDecoder_ne
    {D N : ℕ} [NeZero N]
    (stateOf : Fin N → DensityOperator (Fin D))
    (radius : ℝ)
    (hseparated : ∀ a b : Fin N, a ≠ b →
      2 * radius ≤ realHermitianTraceLoss (stateOf a) (stateOf b))
    (truth : Fin N) (estimate : DensityOperator (Fin D))
    (herror : finiteTraceNearestDecoder stateOf estimate ≠ truth) :
    radius ≤ realHermitianTraceLoss (stateOf truth) estimate := by
  let decoded := finiteTraceNearestDecoder stateOf estimate
  have hnear : realHermitianTraceLoss (stateOf decoded) estimate ≤
      realHermitianTraceLoss (stateOf truth) estimate :=
    finiteTraceNearestDecoder_score_le stateOf estimate truth
  have hsep : 2 * radius ≤
      realHermitianTraceLoss (stateOf truth) (stateOf decoded) :=
    hseparated truth decoded (Ne.symm herror)
  have htriangle :
      realHermitianTraceLoss (stateOf truth) (stateOf decoded) ≤
        realHermitianTraceLoss (stateOf truth) estimate +
          realHermitianTraceLoss (stateOf decoded) estimate := by
    calc
      realHermitianTraceLoss (stateOf truth) (stateOf decoded) ≤
          realHermitianTraceLoss (stateOf truth) estimate +
            realHermitianTraceLoss estimate (stateOf decoded) :=
        realHermitianTraceLoss_triangle _ _ _
      _ = realHermitianTraceLoss (stateOf truth) estimate +
            realHermitianTraceLoss (stateOf decoded) estimate := by
        rw [realHermitianTraceLoss_symm estimate (stateOf decoded)]
  linarith

/-- `ENNReal` form consumed directly by the physical finite-Fano bridge. -/
theorem ofReal_radius_le_hermitianTraceLoss_of_finiteTraceNearestDecoder_ne
    {D N : ℕ} [NeZero N]
    (stateOf : Fin N → DensityOperator (Fin D))
    (radius : ℝ)
    (hseparated : ∀ a b : Fin N, a ≠ b →
      2 * radius ≤ realHermitianTraceLoss (stateOf a) (stateOf b))
    (truth : Fin N) (estimate : DensityOperator (Fin D))
    (herror : finiteTraceNearestDecoder stateOf estimate ≠ truth) :
    ENNReal.ofReal radius ≤ hermitianTraceLoss (stateOf truth) estimate := by
  rw [hermitianTraceLoss_eq_ofReal_realHermitianTraceLoss]
  exact ENNReal.ofReal_mono
    (radius_le_realHermitianTraceLoss_of_finiteTraceNearestDecoder_ne
      stateOf radius hseparated truth estimate herror)

/-- Existence package: every finite family has a measurable decoder, and
pairwise trace-loss separation gives the exact error-to-loss radius. -/
theorem exists_measurable_decoder_wrong_forces_traceLoss
    {D N : ℕ} [NeZero N]
    (stateOf : Fin N → DensityOperator (Fin D))
    (radius : ℝ)
    (hseparated : ∀ a b : Fin N, a ≠ b →
      2 * radius ≤ realHermitianTraceLoss (stateOf a) (stateOf b)) :
    ∃ decode : DensityOperator (Fin D) → Fin N,
      Measurable decode ∧
        ∀ (truth : Fin N) (estimate : DensityOperator (Fin D)),
          decode estimate ≠ truth →
            ENNReal.ofReal radius ≤
              hermitianTraceLoss (stateOf truth) estimate := by
  exact ⟨finiteTraceNearestDecoder stateOf,
    finiteTraceNearestDecoder_measurable stateOf,
    ofReal_radius_le_hermitianTraceLoss_of_finiteTraceNearestDecoder_ne
      stateOf radius hseparated⟩

/-! ## Decoder-free endpoint for the physical Fano bridge -/

/-- The complete finite-kernel Fano-to-physical-risk theorem with the
measurable decoder constructed internally.  The remaining information premise
is stated for this canonical nearest-state decoder. -/
theorem ofReal_eleven_mul_radius_div_sixteen_le_finiteAverageTraceRisk_of_separated
    {D T N : ℕ} [NeZero N]
    (hN : 2 ≤ N)
    (design : Design D T) (estimator : Estimator D T)
    (stateOf : Fin N → DensityOperator (Fin D))
    (hstate : Measurable stateOf)
    (radius : ℝ) (hradius : 0 ≤ radius)
    (hseparated : ∀ a b : Fin N, a ≠ b →
      2 * radius ≤ realHermitianTraceLoss (stateOf a) (stateOf b))
    (hinformation :
      (finiteDecodedJoint design estimator stateOf hstate
        (finiteTraceNearestDecoder stateOf)
        (finiteTraceNearestDecoder_measurable stateOf)).posteriorKLSum ≤
          Real.log N / 16)
    (hlogTwo : 4 * Real.log 2 ≤ Real.log N) :
    ENNReal.ofReal (11 * radius / 16) ≤
      finiteAverageTraceRisk design estimator stateOf := by
  apply ofReal_eleven_mul_radius_div_sixteen_le_finiteAverageTraceRisk
    hN design estimator stateOf hstate
    (finiteTraceNearestDecoder stateOf)
    (finiteTraceNearestDecoder_measurable stateOf)
    radius hradius
  · exact fun a estimate herror ↦
      ofReal_radius_le_hermitianTraceLoss_of_finiteTraceNearestDecoder_ne
        stateOf radius hseparated a estimate herror
  · exact hinformation
  · exact hlogTwo

end PhysicalRisk

end TomographyOracleCore
