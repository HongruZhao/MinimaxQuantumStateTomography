import TomographyOracleCore.Revision.BinaryCliffordNeutralFourth
import TomographyOracleCore.BinaryPauliOneCopyCurvature
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Data.Matrix.Basis

namespace TomographyOracleCore.Revision.BinaryPauliFourthBasis

open BinaryCliffordNeutralFourth
open scoped BigOperators

noncomputable section

private abbrev finFourDecidableEq : DecidableEq (Fin 4) := inferInstance

def matrixTensorFourthMultilinear {ι : Type*} :
    MultilinearMap ℂ (fun _ : Fin 4 => Matrix ι ι ℂ)
      (Matrix (FourthIndex ι) (FourthIndex ι) ℂ) where
  toFun A := matrixTensorFour (A 0) (A 1) (A 2) (A 3)
  map_update_add' {dec} A i B C := by
    have hdec : dec = finFourDecidableEq := Subsingleton.elim _ _
    subst dec
    fin_cases i <;> ext x y <;>
      simp [matrixTensorFour_apply, add_mul, mul_add]
  map_update_smul' {dec} A i c B := by
    have hdec : dec = finFourDecidableEq := Subsingleton.elim _ _
    subst dec
    fin_cases i <;> ext x y <;>
      simp [matrixTensorFour_apply] <;> ring

def hermitianPauliTensorFour (K : ℕ) (p : Fin 4 → PauliLabel K) :
    FourthPauliMatrix K :=
  matrixTensorFourthMultilinear (fun i => hermitianBinaryPauliMatrix K (p i))

theorem matrixTensorFourth_mem_span_pauli
    (K : ℕ) (A : Fin 4 → Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ) :
    matrixTensorFourthMultilinear A ∈
      Submodule.span ℂ (Set.range (hermitianPauliTensorFour K)) := by
  classical
  let c (i : Fin 4) (p : PauliLabel K) : ℂ :=
    ((2 : ℂ) ^ K)⁻¹ * binaryHermitianPauliCoefficient K (A i) p
  have hrepr : A = fun i => ∑ p : PauliLabel K, c i p • hermitianBinaryPauliMatrix K p := by
    funext i
    have h := hermitianBinaryPauli_reconstruction K (A i)
    rw [Finset.smul_sum] at h
    simpa only [smul_smul, c] using h
  rw [hrepr, MultilinearMap.map_sum]
  apply Submodule.sum_mem
  intro p hp
  rw [MultilinearMap.map_smul_univ]
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨p, rfl⟩

/-- Literal four-register Pauli tensors span the full matrix space. -/
theorem span_hermitianPauliTensorFour_eq_top (K : ℕ) :
    Submodule.span ℂ (Set.range (hermitianPauliTensorFour K)) = ⊤ := by
  classical
  apply top_unique
  intro X hX
  rw [Matrix.matrix_eq_sum_single X]
  apply Submodule.sum_mem
  intro a ha
  apply Submodule.sum_mem
  intro b hb
  have heq : Matrix.single a b (X a b) =
      matrixTensorFourthMultilinear
        ![Matrix.single a.1 b.1 (X a b),
          Matrix.single a.2.1 b.2.1 1,
          Matrix.single a.2.2.1 b.2.2.1 1,
          Matrix.single a.2.2.2 b.2.2.2 1] := by
    simp [matrixTensorFourthMultilinear, matrixTensorFour,
      Matrix.single_kronecker_single]
  rw [heq]
  exact matrixTensorFourth_mem_span_pauli K _

/-- Equality on the concrete Pauli tensors implies equality on all
four-register matrices. -/
theorem linearMap_ext_on_pauli_four
    (K : ℕ) {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (L M : FourthPauliMatrix K →ₗ[ℂ] V)
    (h : ∀ p, L (hermitianPauliTensorFour K p) = M (hermitianPauliTensorFour K p)) :
    L = M := by
  apply LinearMap.ext_on (span_hermitianPauliTensorFour_eq_top K)
  rintro _ ⟨p, rfl⟩
  exact h p

end

end TomographyOracleCore.Revision.BinaryPauliFourthBasis
