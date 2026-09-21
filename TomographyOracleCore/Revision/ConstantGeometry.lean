import TomographyOracleCore.OrderedSpectral
import TomographyOracleCore.Revision.ConstantNegativeSpectrum

namespace TomographyOracleCore.MatrixReduction

noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Retain the exact square root of the tangent rank bound. -/
theorem density_projection_cone_sqrt_two
    (σ ρ : DensityOperator ι) (P : Matrix ι ι ℂ) (s : ℕ)
    (hP : P.IsHermitian) (hid : IsIdempotentElem P)
    (hPnorm : matrixOperatorNorm P ≤ 1) (hPrank : P.rank ≤ s) :
    let Δ := σ.matrix - ρ.matrix
    let Q := 1 - P
    hermitianTraceNorm Δ (σ.sub_isHermitian ρ) ≤
      2 * (Q * ρ.matrix * Q).trace.re +
        2 * Real.sqrt (2 * (s : ℝ)) *
          hermitianFrobeniusNorm Δ (σ.sub_isHermitian ρ) := by
  dsimp
  let Δ := σ.matrix - ρ.matrix
  let Q : Matrix ι ι ℂ := 1 - P
  let T := projectionTangent P Δ
  let R := projectionRemainder P Δ
  have hΔ : Δ.IsHermitian := σ.sub_isHermitian ρ
  have hT : T.IsHermitian := projectionTangent_isHermitian P Δ hP hΔ
  have hR : R.IsHermitian := projectionRemainder_isHermitian P Δ hP hΔ
  have hdec : T + R = Δ := projectionTangent_add_remainder P Δ
  have htri : hermitianTraceNorm Δ hΔ ≤
      hermitianTraceNorm T hT + hermitianTraceNorm R hR := by
    have ht := hermitianTraceNorm_triangle T R hT hR
    exact (hermitianTraceNorm_congr hdec (hT.add hR) hΔ).symm ▸ ht
  have hrem : hermitianTraceNorm R hR ≤
      hermitianTraceNorm (P * Δ * P)
          (sandwich_isHermitian P Δ hP hΔ) +
        2 * (Q * ρ.matrix * Q).trace.re := by
    change hermitianTraceNorm ((1 - P) * Δ * (1 - P)) _ ≤
      hermitianTraceNorm (P * Δ * P) _ +
        2 * ((1 - P) * ρ.matrix * (1 - P)).trace.re
    simpa [Δ] using density_complement_block_traceNorm_le σ ρ P hP hid
  have hcompress0 := hermitianTraceNorm_sandwich_le P T hP hT hPnorm
  have hPTP : P * T * P = P * Δ * P := by
    simpa [T] using projection_tangent_compression P Δ hid
  have hcompress :
      hermitianTraceNorm (P * Δ * P)
          (sandwich_isHermitian P Δ hP hΔ) ≤
        hermitianTraceNorm T hT := by
    rw [← hermitianTraceNorm_congr hPTP
      (sandwich_isHermitian P T hP hT)
      (sandwich_isHermitian P Δ hP hΔ)]
    exact hcompress0
  have hTrankNat : T.rank ≤ 2 * s :=
    (projectionTangent_rank_le P Δ).trans (Nat.mul_le_mul_left 2 hPrank)
  have hTrank : hermitianRank T hT ≤ 2 * s := by
    rw [hermitianRank_eq_rank]
    exact hTrankNat
  have hs : 0 ≤ (s : ℝ) := Nat.cast_nonneg _
  have hcast : (hermitianRank T hT : ℝ) ≤ 2 * (s : ℝ) := by
    exact_mod_cast hTrank
  have hsqrt : Real.sqrt (hermitianRank T hT) ≤ Real.sqrt (2 * (s : ℝ)) :=
    Real.sqrt_le_sqrt hcast
  have hTfrob := projectionTangent_frobeniusNorm_le P Δ hP hΔ hid
  have hTbound : hermitianTraceNorm T hT ≤
      Real.sqrt (2 * (s : ℝ)) * hermitianFrobeniusNorm Δ hΔ := by
    calc
      hermitianTraceNorm T hT ≤
          Real.sqrt (hermitianRank T hT) *
            hermitianFrobeniusNorm T hT :=
        hermitianTraceNorm_le_sqrt_rank_mul_frobeniusNorm T hT
      _ ≤ (Real.sqrt (2 * (s : ℝ))) * hermitianFrobeniusNorm T hT := by
        gcongr
        exact hermitianFrobeniusNorm_nonneg T hT
      _ ≤ (Real.sqrt (2 * (s : ℝ))) * hermitianFrobeniusNorm Δ hΔ := by
        gcongr
      _ = Real.sqrt (2 * (s : ℝ)) * hermitianFrobeniusNorm Δ hΔ := rfl
  calc
    hermitianTraceNorm Δ hΔ ≤
        hermitianTraceNorm T hT + hermitianTraceNorm R hR := htri
    _ ≤ hermitianTraceNorm T hT +
        (hermitianTraceNorm (P * Δ * P)
          (sandwich_isHermitian P Δ hP hΔ) +
            2 * (Q * ρ.matrix * Q).trace.re) := by gcongr
    _ ≤ hermitianTraceNorm T hT +
        (hermitianTraceNorm T hT +
            2 * (Q * ρ.matrix * Q).trace.re) := by gcongr
    _ ≤ 2 * (Real.sqrt (2 * (s : ℝ)) * hermitianFrobeniusNorm Δ hΔ) +
        2 * (Q * ρ.matrix * Q).trace.re := by linarith
    _ = 2 * (Q * ρ.matrix * Q).trace.re +
        2 * Real.sqrt (2 * (s : ℝ)) * hermitianFrobeniusNorm Δ hΔ := by ring

/-- The strengthened cone bound for the actual ordered spectral tail. -/
theorem density_orderedSpectralTail_cone_sqrt_two
    (sigma rho : DensityOperator ι) (s : ℕ) :
    hermitianTraceNorm (sigma.matrix - rho.matrix) (sigma.sub_isHermitian rho) ≤
      2 * orderedSpectralTail rho s + 2 * Real.sqrt (2 * (s : ℝ)) *
        hermitianFrobeniusNorm (sigma.matrix - rho.matrix) (sigma.sub_isHermitian rho) := by
  have hcone := density_projection_cone_sqrt_two sigma rho
    (leadingSpectralProjection rho s) s
    (leadingSpectralProjection_isHermitian rho s)
    (leadingSpectralProjection_isIdempotent rho s)
    (leadingSpectralProjection_operatorNorm_le_one rho s)
    (leadingSpectralProjection_rank_le rho s)
  dsimp only at hcone
  rw [leadingSpectralProjection_complement_trace_eq_tail rho s] at hcone
  exact hcone

/-- Sharp Young absorption for the retained tangent-rank estimate. -/
theorem tangent_cone_absorption (x tail v z : ℝ)
    (hx : 0 ≤ x) (hv : 0 ≤ v) (hz : 0 ≤ z)
    (hcone : x ≤ 2 * tail + 2 * v) (henergy : v ^ 2 ≤ 2 * z * x) :
    x ≤ 4 * tail + 8 * z := by
  have hsquare : (2 * v) ^ 2 ≤ (x / 2 + 4 * z) ^ 2 := by
    nlinarith [sq_nonneg (x / 2 - 4 * z)]
  have hroot := (sq_le_sq₀ (by positivity : 0 ≤ 2 * v)
    (by positivity : 0 ≤ x / 2 + 4 * z)).mp hsquare
  linarith

/-- Curvature and the negative-eigenspace cone give 4*s*h/a instead of 16*s*h/a. -/
theorem density_orderedSpectralTail_trace_bound_sharp
    (sigma rho : DensityOperator ι) (s : ℕ) (a h energy : ℝ)
    (ha : 0 < a) (hh : 0 ≤ h)
    (hlower : a * hermitianFrobeniusNorm (sigma.matrix - rho.matrix)
      (sigma.sub_isHermitian rho) ^ 2 ≤ energy)
    (hupper : energy ≤ hermitianTraceNorm (sigma.matrix - rho.matrix)
      (sigma.sub_isHermitian rho) * h) :
    hermitianTraceNorm (sigma.matrix - rho.matrix) (sigma.sub_isHermitian rho) ≤
      4 * orderedSpectralTail rho s + 4 * ((s : ℝ) * h / a) := by
  let x := hermitianTraceNorm (sigma.matrix - rho.matrix) (sigma.sub_isHermitian rho)
  let f := hermitianFrobeniusNorm (sigma.matrix - rho.matrix) (sigma.sub_isHermitian rho)
  let v := Real.sqrt (s : ℝ) * f
  let z := (s : ℝ) * h / a
  have henergy := frobenius_energy_control a x f h energy ha hlower hupper
  have hx : 0 ≤ x := hermitianTraceNorm_nonneg _ _
  have hf : 0 ≤ f := hermitianFrobeniusNorm_nonneg _ _
  have hv : 0 ≤ v := mul_nonneg (Real.sqrt_nonneg _) hf
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hcone : x ≤ 2 * orderedSpectralTail rho s + 2 * v := by
    simpa only [v, mul_assoc] using density_orderedSpectralTail_cone_negative sigma rho s
  have hvsq : v ^ 2 ≤ z * x := by
    dsimp [v, z]
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg s)]
    have hm := mul_le_mul_of_nonneg_left henergy (Nat.cast_nonneg s)
    calc
      _ ≤ (s : ℝ) * (h / a * x) := hm
      _ = _ := by ring
  have hsquare : (2 * v) ^ 2 ≤ (x / 2 + 2 * z) ^ 2 := by
    nlinarith [sq_nonneg (x / 2 - 2 * z)]
  have hroot := (sq_le_sq₀ (by positivity : 0 ≤ 2 * v)
    (by positivity : 0 ≤ x / 2 + 2 * z)).mp hsquare
  change x ≤ 4 * orderedSpectralTail rho s + 4 * z
  linarith

end
end TomographyOracleCore.MatrixReduction
