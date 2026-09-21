import TomographyOracleCore.BinaryCliffordPauliTwoMixing
import TomographyOracleCore.BinaryCliffordPhysicalChannel

namespace TomographyOracleCore

open scoped BigOperators

/-!
# Pauli-coset completion of the generated Clifford ensemble

Choosing one unitary lift for each generated symplectic element is sufficient
for the second-moment measurement-channel calculation, but that section of
the quotient is not by itself the uniform Clifford ensemble used in exact
third-moment arguments.  Here we enlarge it by an independent uniform
Hermitian Pauli factor.  The resulting finite ensemble is Pauli-invariant at
the distributional level and has exactly the same dephasing-channel action
on the Pauli basis.
-/

/-- Every Hermitian binary Pauli is a unitary matrix. -/
theorem hermitianBinaryPauliMatrix_mem_unitaryGroup
    (K : ℕ) (a : PauliLabel K) :
    hermitianBinaryPauliMatrix K a ∈
      Matrix.unitaryGroup (PauliBinaryWord K) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    hermitianBinaryPauliMatrix_conjTranspose,
    hermitianBinaryPauliMatrix_sq]

/-- Hermitian Pauli matrix as an element of the matrix unitary group. -/
noncomputable def hermitianBinaryPauliUnitary
    (K : ℕ) (a : PauliLabel K) :
    Matrix.unitaryGroup (PauliBinaryWord K) ℂ :=
  ⟨hermitianBinaryPauliMatrix K a,
    hermitianBinaryPauliMatrix_mem_unitaryGroup K a⟩

/-- A Hermitian Pauli is a unitary lift of the identity symplectic action:
it changes only the Pauli phase under conjugation. -/
theorem hermitianBinaryPauliUnitary_isIdentityLift
    (K : ℕ) (a : PauliLabel K) :
    IsUnitaryPauliLift K 1 (hermitianBinaryPauliUnitary K a) := by
  intro p
  refine ⟨(pauliCharacter K a p : ℂ), ?_, ?_⟩
  · exact_mod_cast binarySign_ne_zero (pauliSymplecticForm K a p)
  · simpa [hermitianBinaryPauliUnitary,
      hermitianBinaryPauliMatrix_conjTranspose] using
      (hermitianBinaryPauliMatrix_sandwich K a p)

/-- The product of two specified unitary lifts is a specified lift of the
product symplectic action. -/
theorem IsUnitaryPauliLift.mul_of_unitaries
    (K : ℕ) {g h : binarySymplecticGroup K}
    {U V : Matrix.unitaryGroup (PauliBinaryWord K) ℂ}
    (hU : IsUnitaryPauliLift K g U)
    (hV : IsUnitaryPauliLift K h V) :
    IsUnitaryPauliLift K (g * h) (U * V) := by
  intro p
  obtain ⟨c, hc, hVc⟩ := hV p
  obtain ⟨d, hd, hUd⟩ := hU (h.1 p)
  refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
  change (((U.1 * V.1) * binaryPauliMatrix K p) *
      (U.1 * V.1).conjTranspose) =
    (c * d) • binaryPauliMatrix K (g.1 (h.1 p))
  rw [Matrix.conjTranspose_mul]
  calc
    ((U.1 * V.1) * binaryPauliMatrix K p) *
          (V.1.conjTranspose * U.1.conjTranspose) =
        (U.1 * ((V.1 * binaryPauliMatrix K p) *
          V.1.conjTranspose)) * U.1.conjTranspose := by
      noncomm_ring
    _ = (U.1 * (c • binaryPauliMatrix K (h.1 p))) *
          U.1.conjTranspose := by rw [hVc]
    _ = c • ((U.1 * binaryPauliMatrix K (h.1 p)) *
          U.1.conjTranspose) := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = c • (d • binaryPauliMatrix K (g.1 (h.1 p))) := by rw [hUd]
    _ = (c * d) • binaryPauliMatrix K (g.1 (h.1 p)) := by
      rw [smul_smul]

/-- Finite Pauli-coset completion of the generated symplectic ensemble. -/
abbrev PauliCosetCliffordEnsemble (K : ℕ) :=
  PauliLabel K × binaryTransvectionGroup K

/-- Concrete unitary attached to a Pauli label and a generated symplectic
element. -/
noncomputable def pauliCosetCliffordUnitary
    (K : ℕ) (e : PauliCosetCliffordEnsemble K) :
    Matrix.unitaryGroup (PauliBinaryWord K) ℂ :=
  hermitianBinaryPauliUnitary K e.1 *
    binaryTransvectionUnitaryLift K e.2

/-- Every Pauli-coset unitary implements the symplectic action of its second
component, independently of the Pauli factor. -/
theorem pauliCosetCliffordUnitary_spec
    (K : ℕ) (e : PauliCosetCliffordEnsemble K) :
    IsUnitaryPauliLift K e.2.1 (pauliCosetCliffordUnitary K e) := by
  simpa [pauliCosetCliffordUnitary] using
    (IsUnitaryPauliLift.mul_of_unitaries K
      (hermitianBinaryPauliUnitary_isIdentityLift K e.1)
      (binaryTransvectionUnitaryLift_spec K e.2))

/-- Adding the independent Pauli factor leaves each Pauli-basis dephasing
channel value unchanged. -/
theorem conjugatedPauliCosetMeasurementChannel_binaryPauli
    (K : ℕ) (e : PauliCosetCliffordEnsemble K) (p : PauliLabel K) :
    conjugatedComputationalBasisMeasurementChannel K
        (pauliCosetCliffordUnitary K e) (binaryPauliMatrix K p) =
      if (e.2.1.1 p).1 = 0 then binaryPauliMatrix K p else 0 :=
  conjugatedComputationalBasisMeasurementChannel_binaryPauli_of_lift
    K e.2.1 (pauliCosetCliffordUnitary K e)
      (pauliCosetCliffordUnitary_spec K e) p

/-- Uniform physical measurement channel over the Pauli-coset completion. -/
noncomputable def averagedPauliCosetCliffordMeasurementChannel (K : ℕ)
    (A : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ) :
    Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ :=
  ((Fintype.card (PauliCosetCliffordEnsemble K) : ℂ)⁻¹) •
    ∑ e : PauliCosetCliffordEnsemble K,
      conjugatedComputationalBasisMeasurementChannel K
        (pauliCosetCliffordUnitary K e) A

/-- Counting a Pauli-coset hit factors off the free Pauli coordinate. -/
noncomputable def pauliCosetHitEquiv
    (K : ℕ) (p : PauliLabel K) :
    {e : PauliCosetCliffordEnsemble K // (e.2.1.1 p).1 = 0} ≃
      PauliLabel K ×
        {g : binaryTransvectionGroup K // (g.1.1 p).1 = 0} where
  toFun e := (e.1.1, ⟨e.1.2, e.2⟩)
  invFun e := ⟨(e.1, e.2.1), e.2.2⟩
  left_inv e := by apply Subtype.ext; rfl
  right_inv e := rfl

set_option maxHeartbeats 600000 in
/-- The uniform Pauli-coset channel has the same exact Pauli eigenvalue
ratio as the generated quotient section. -/
theorem averagedPauliCosetCliffordMeasurementChannel_binaryPauli
    (K : ℕ) (p : PauliLabel K) :
    averagedPauliCosetCliffordMeasurementChannel K
        (binaryPauliMatrix K p) =
      (((Fintype.card
          {g : binaryTransvectionGroup K // (g.1.1 p).1 = 0} : ℕ) : ℂ) /
        Fintype.card (binaryTransvectionGroup K)) •
          binaryPauliMatrix K p := by
  classical
  have hsum :
      (∑ e : PauliCosetCliffordEnsemble K,
        if (e.2.1.1 p).1 = 0 then binaryPauliMatrix K p else 0) =
      ((Fintype.card
          {e : PauliCosetCliffordEnsemble K //
            (e.2.1.1 p).1 = 0} : ℕ) : ℂ) •
        binaryPauliMatrix K p := by
    calc
      (∑ e : PauliCosetCliffordEnsemble K,
          if (e.2.1.1 p).1 = 0 then binaryPauliMatrix K p else 0) =
        ∑ e : PauliCosetCliffordEnsemble K,
          (if (e.2.1.1 p).1 = 0 then (1 : ℂ) else 0) •
            binaryPauliMatrix K p := by
          apply Finset.sum_congr rfl
          intro e _
          split_ifs <;> simp
      _ = (∑ e : PauliCosetCliffordEnsemble K,
          if (e.2.1.1 p).1 = 0 then (1 : ℂ) else 0) •
            binaryPauliMatrix K p := by rw [Finset.sum_smul]
      _ = ((Fintype.card
          {e : PauliCosetCliffordEnsemble K //
            (e.2.1.1 p).1 = 0} : ℕ) : ℂ) •
            binaryPauliMatrix K p := by
          rw [Finset.sum_boole, ← Fintype.card_subtype]
  have hpauli : (Fintype.card (PauliLabel K) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (PauliLabel K) ≠ 0)
  have hgroup : (Fintype.card (binaryTransvectionGroup K) : ℂ) ≠ 0 := by
    exact_mod_cast
      (Fintype.card_ne_zero : Fintype.card (binaryTransvectionGroup K) ≠ 0)
  have hratio :
      ((Fintype.card
          {e : PauliCosetCliffordEnsemble K //
            (e.2.1.1 p).1 = 0} : ℕ) : ℂ) /
          Fintype.card (PauliCosetCliffordEnsemble K) =
        ((Fintype.card
          {g : binaryTransvectionGroup K // (g.1.1 p).1 = 0} : ℕ) : ℂ) /
          Fintype.card (binaryTransvectionGroup K) := by
    change
      ((Fintype.card
          {e : PauliCosetCliffordEnsemble K //
            (e.2.1.1 p).1 = 0} : ℕ) : ℂ) /
          Fintype.card
            (PauliLabel K × binaryTransvectionGroup K) =
        ((Fintype.card
          {g : binaryTransvectionGroup K // (g.1.1 p).1 = 0} : ℕ) : ℂ) /
          Fintype.card (binaryTransvectionGroup K)
    rw [Fintype.card_congr (pauliCosetHitEquiv K p)]
    rw [Fintype.card_prod (PauliLabel K)
        {g : binaryTransvectionGroup K // (g.1.1 p).1 = 0},
      Fintype.card_prod (PauliLabel K) (binaryTransvectionGroup K)]
    push_cast
    field_simp [hpauli, hgroup]
  unfold averagedPauliCosetCliffordMeasurementChannel
  simp_rw [conjugatedPauliCosetMeasurementChannel_binaryPauli]
  rw [hsum, smul_smul]
  apply congrArg (fun c : ℂ ↦ c • binaryPauliMatrix K p)
  simpa [div_eq_mul_inv, mul_comm] using hratio

/-- For every nonidentity Pauli, the Pauli-coset-completed physical channel
retains the exact eigenvalue `1 / (2^K + 1)`. -/
theorem averagedPauliCosetCliffordMeasurementChannel_binaryPauli_nonzero
    {K : ℕ} (hK : 0 < K) {p : PauliLabel K} (hp : p ≠ 0) :
    averagedPauliCosetCliffordMeasurementChannel K
        (binaryPauliMatrix K p) =
      (1 / ((2 : ℂ) ^ K + 1)) • binaryPauliMatrix K p := by
  rw [averagedPauliCosetCliffordMeasurementChannel_binaryPauli]
  have hreal := uniform_binaryTransvectionGroup_z_probability hK
    (⟨p, hp⟩ : NonidentityPauliLabel K)
  have hcard :
      Fintype.card
          {g : binaryTransvectionGroup K // (g.1.1 p).1 = 0} =
        Fintype.card
          {g : binaryTransvectionGroup K //
            (g • (⟨p, hp⟩ : NonidentityPauliLabel K)).1.1 = 0} := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquiv (Equiv.refl _) (by intro g; rfl)
  have hreal' :
      ((Fintype.card
          {g : binaryTransvectionGroup K // (g.1.1 p).1 = 0} : ℕ) : ℝ) /
          Fintype.card (binaryTransvectionGroup K) =
        1 / ((2 : ℝ) ^ K + 1) := by
    rw [hcard]
    exact hreal
  have hcomplex := congrArg (fun x : ℝ ↦ (x : ℂ)) hreal'
  push_cast at hcomplex
  rw [hcomplex]

end TomographyOracleCore
