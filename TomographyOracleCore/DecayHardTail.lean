import TomographyOracleCore.Algebra

namespace TomographyOracleCore

/-!
# Scalar tail of the spectral-decay hard family

This file formalizes only the scalar spectrum calculation used in the lower
bound.  It does not assert that a matrix with this tail has been constructed;
that separate density-matrix realization remains outside this module.
-/

/-- The exact ordered tail of the paper's hard spectrum: two head
eigenvalues, `m` equal tail eigenvalues of total mass `b`, and zeros after
rank `m + 2`. -/
noncomputable def hardFamilyTail (m : ℕ) (b : ℝ) (s : ℕ) : ℝ :=
  if s = 1 then
    (1 + b) / 2
  else if s ≤ m + 1 then
    b * (((m : ℝ) + 2 - (s : ℝ)) / (m : ℝ))
  else
    0

@[simp] theorem hardFamilyTail_one (m : ℕ) (b : ℝ) :
    hardFamilyTail m b 1 = (1 + b) / 2 := by
  simp [hardFamilyTail]

theorem hardFamilyTail_middle
    (m s : ℕ) (b : ℝ) (hs2 : 2 ≤ s) (hsm : s ≤ m + 1) :
    hardFamilyTail m b s =
      b * (((m : ℝ) + 2 - (s : ℝ)) / (m : ℝ)) := by
  have hsne : s ≠ 1 := by omega
  simp [hardFamilyTail, hsne, hsm]

theorem hardFamilyTail_high
    (m s : ℕ) (b : ℝ) (hhigh : m + 2 ≤ s) :
    hardFamilyTail m b s = 0 := by
  have hsne : s ≠ 1 := by omega
  have hnmid : ¬s ≤ m + 1 := by omega
  simp [hardFamilyTail, hsne, hnmid]

/-- In the middle branch the remaining fraction of the tail mass is at most
one, so the spectral tail is at most `b`. -/
theorem hardFamilyTail_middle_le_mass
    (m s : ℕ) (b : ℝ)
    (hm : 1 ≤ m) (hb : 0 ≤ b) (hs2 : 2 ≤ s) (hsm : s ≤ m + 1) :
    hardFamilyTail m b s ≤ b := by
  rw [hardFamilyTail_middle m s b hs2 hsm]
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hs2real : 2 ≤ (s : ℝ) := by exact_mod_cast hs2
  have hfrac : ((m : ℝ) + 2 - (s : ℝ)) / (m : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hmpos).2
    linarith
  simpa using mul_le_mul_of_nonneg_left hfrac hb

/-- The scaled mass restriction from the hard-family construction implies
the desired decay envelope throughout the middle range. -/
theorem hardFamily_mass_le_decay_envelope
    (m s : ℕ) (alpha L b : ℝ)
    (hm : 1 ≤ m) (halpha : 1 < alpha) (hL : 1 ≤ L)
    (hs2 : 2 ≤ s) (hsm : s ≤ m + 1)
    (hbscaled :
      b ≤ (2 : ℝ) ^ (1 - alpha) * L * (m : ℝ) ^ (1 - alpha)) :
    b ≤ L * (s : ℝ) ^ (1 - alpha) := by
  have hmreal : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hmnonneg : 0 ≤ (m : ℝ) := le_trans zero_le_one hmreal
  have hspos : 0 < (s : ℝ) := by
    have : 0 < s := by omega
    exact_mod_cast this
  have hs_le_two_m : (s : ℝ) ≤ 2 * (m : ℝ) := by
    have hsmreal : (s : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hsm
    linarith
  have hexp : 1 - alpha ≤ 0 := by linarith
  have hrpow :
      (2 * (m : ℝ)) ^ (1 - alpha) ≤ (s : ℝ) ^ (1 - alpha) :=
    Real.rpow_le_rpow_of_nonpos hspos hs_le_two_m hexp
  have hLnonneg : 0 ≤ L := le_trans zero_le_one hL
  have hscaled :
      (2 : ℝ) ^ (1 - alpha) * L * (m : ℝ) ^ (1 - alpha) ≤
        L * (s : ℝ) ^ (1 - alpha) := by
    calc
      (2 : ℝ) ^ (1 - alpha) * L * (m : ℝ) ^ (1 - alpha) =
          L * ((2 : ℝ) ^ (1 - alpha) *
            (m : ℝ) ^ (1 - alpha)) := by ring
      _ = L * (2 * (m : ℝ)) ^ (1 - alpha) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hmnonneg]
      _ ≤ L * (s : ℝ) ^ (1 - alpha) :=
        mul_le_mul_of_nonneg_left hrpow hLnonneg
  exact hbscaled.trans hscaled

/-- The full scalar hard-family tail obeys the polynomial decay envelope.
The proof covers the head, middle, and zero-tail branches separately. -/
theorem hardFamilyTail_le_decay_envelope
    (m s : ℕ) (alpha L b : ℝ)
    (hm : 1 ≤ m) (halpha : 1 < alpha) (hL : 1 ≤ L)
    (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4)
    (hbscaled :
      b ≤ (2 : ℝ) ^ (1 - alpha) * L * (m : ℝ) ^ (1 - alpha))
    (hs1 : 1 ≤ s) :
    hardFamilyTail m b s ≤ L * (s : ℝ) ^ (1 - alpha) := by
  by_cases hsone : s = 1
  · subst s
    rw [hardFamilyTail_one]
    have hhead : (1 + b) / 2 ≤ 1 := by
      norm_num at hbquarter ⊢
      linarith
    simpa using hhead.trans hL
  · have hs2 : 2 ≤ s := by omega
    by_cases hsm : s ≤ m + 1
    · exact (hardFamilyTail_middle_le_mass m s b hm hb0 hs2 hsm).trans
        (hardFamily_mass_le_decay_envelope m s alpha L b hm halpha hL
          hs2 hsm hbscaled)
    · have hhigh : m + 2 ≤ s := by omega
      rw [hardFamilyTail_high m s b hhigh]
      exact mul_nonneg (le_trans zero_le_one hL)
        (Real.rpow_nonneg (Nat.cast_nonneg s) (1 - alpha))

/-- Membership form of `hardFamilyTail_le_decay_envelope`, simultaneously
for every positive truncation index. -/
theorem hardFamilyTail_decay_membership
    (m : ℕ) (alpha L b : ℝ)
    (hm : 1 ≤ m) (halpha : 1 < alpha) (hL : 1 ≤ L)
    (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4)
    (hbscaled :
      b ≤ (2 : ℝ) ^ (1 - alpha) * L * (m : ℝ) ^ (1 - alpha)) :
    ∀ s : ℕ, 1 ≤ s →
      hardFamilyTail m b s ≤ L * (s : ℝ) ^ (1 - alpha) := by
  intro s hs
  exact hardFamilyTail_le_decay_envelope m s alpha L b hm halpha hL
    hb0 hbquarter hbscaled hs

end TomographyOracleCore
