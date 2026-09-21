import TomographyOracleCore.Revision.SparseCorrelationSparsification
import TomographyOracleCore.Revision.SparseNetConstants

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace TomographyOracleCore.Revision.SparseNetStep

open SparseCoefficientGeometry SparseSampleSuprema SparseDeterministicRecurrence
open SparseCorrelationSparsification SparseNetConstants
open scoped BigOperators InnerProductSpace
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem largeRows_step {X : ι → E} {h : ℕ} (hh : 0 < h)
    (hN : 65536 * h ≤ Fintype.card ι) (I : Finset ι)
    {M tau : ℝ} (hM : 0 ≤ M) (htau : 0 < tau)
    (hentry : ∀ i j, i ≠ j → |⟪X i, X j⟫_ℝ| ≤ M)
    (net : Finset (ι → ℝ)) (hnet : ∀ v ∈ net, Admissible h I v)
    (hcover : ∀ y, Admissible h I y → ∃ v ∈ net,
      coefficientNorm (fun i => y i - v i) ≤ netRadius ∧
      (support (fun i => y i - v i)).card ≤ h)
    (hgood : ∀ v ∈ net, (largeRows X v Iᶜ tau).card < 8 * h)
    (y : ι → ℝ) (hy : Admissible (65536 * h) I y) :
    (largeRows X y Iᶜ
      (rowThreshold (65536 * h) M tau (crossNorm X (32768 * h) I))).card < 32768 * h := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hkR : (0 : ℝ) < 65536 * h := by positivity
  have hrR : (0 : ℝ) < 8 * h := by positivity
  have hg := crossNorm_nonneg X (32768 * h) I
  apply largeRows_card_lt_of_net (delta := sparsifyingFraction) (eta := netRadius)
    (k := 65536 * h) (m := 32768 * h) (h := h) (r := 8 * h) (M := M)
    I (by omega) hN (by omega) (by omega) (by omega)
    (by norm_num [sparsifyingFraction]) (by norm_num [sparsifyingFraction])
    (by norm_num [netRadius]) (rowThreshold_pos hkR hM htau hg)
    (by norm_num [sparsifyingFraction]; ring_nf; exact le_rfl)
    (by norm_num; ring_nf; exact le_rfl) hentry
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using rowThreshold_entry_bound hkR hM htau hg)
    net hnet hcover hgood
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      rowThreshold_separation hkR hrR (by ring) hM htau hg) y hy

/-- One deterministic sparse-norm recursion with fixed, explicit sparsification
and net radii. This requires tests of only h-sparse vectors to reduce 65536 h
coordinates to 32768 h coordinates. -/
theorem crossNorm_step {X : ι → E} {h : ℕ} (hh : 0 < h)
    (hN : 65536 * h ≤ Fintype.card ι) (I : Finset ι)
    {M tau : ℝ} (hM : 0 ≤ M) (htau : 0 < tau)
    (hentry : ∀ i j, i ≠ j → |⟪X i, X j⟫_ℝ| ≤ M)
    (netL netR : Finset (ι → ℝ))
    (hnetL : ∀ v ∈ netL, Admissible h I v)
    (hcoverL : ∀ y, Admissible h I y → ∃ v ∈ netL,
      coefficientNorm (fun i => y i - v i) ≤ netRadius ∧
      (support (fun i => y i - v i)).card ≤ h)
    (hnetR : ∀ v ∈ netR, Admissible h Iᶜ v)
    (hcoverR : ∀ y, Admissible h Iᶜ y → ∃ v ∈ netR,
      coefficientNorm (fun i => y i - v i) ≤ netRadius ∧
      (support (fun i => y i - v i)).card ≤ h)
    (hgoodL : ∀ v ∈ netL, (largeRows X v Iᶜ tau).card < 8 * h)
    (hgoodR : ∀ v ∈ netR, (largeRows X v I tau).card < 8 * h) :
    crossNorm X (65536 * h) I ≤
      (17 / 16 : ℝ) * crossNorm X (32768 * h) I +
        549755813888 * M + 549755813888 * Real.sqrt (65536 * h) * tau := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hkR : (0 : ℝ) < 65536 * h := by positivity
  have hg := crossNorm_nonneg X (32768 * h) I
  have hleft := largeRows_step hh hN I hM htau hentry netL hnetL hcoverL hgoodL
  have hright := largeRows_step hh hN Iᶜ hM htau hentry netR hnetR hcoverR
    (by simpa only [compl_compl] using hgoodR)
  simp only [compl_compl, crossNorm_compl] at hright
  have hrec := crossNorm_recurrence I (rowThreshold_pos hkR hM htau hg).le
    (fun y hy => (hleft y hy).le) (fun y hy => (hright y hy).le)
  have heq := rowThreshold_mul_sqrt hkR M tau (crossNorm X (32768 * h) I)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hrec
  nlinarith

end
end TomographyOracleCore.Revision.SparseNetStep
