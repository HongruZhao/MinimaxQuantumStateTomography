import TomographyOracleCore.ChoKimCondition
import Mathlib.Analysis.Complex.ExponentialBounds

namespace TomographyOracleCore

/-!
# Explicit arithmetic for the periodic Cho--Kim design gate

The cited relative-design gluing theorem supplies a bound in terms of a local
overlap dimension `q` and the number of circuit vertices.  Everything after
that theorem in the manuscript is elementary arithmetic.  This module checks
that arithmetic, including the advertised constants `46`, `92 / log 2`, and
the final relative-error threshold one.

It does not assert the Clifford three-design theorem or the two-layer gluing
theorem.  Those remain explicit premises at the eventual circuit boundary.
-/

/-- The order-three two-block loss used in the specialized gluing estimate. -/
noncomputable def choKimFThree (q : ℝ) : ℝ :=
  2 *
    (9 / q + 9 / (2 * q) + 81 / (2 * q ^ 2) +
      (9 / (4 * q)) / (1 - 9 / (4 * q))) *
    (1 + 9 / (2 * q))

/-- The overlap Hilbert-space dimension of two staggered `K`-qubit blocks. -/
noncomputable def choKimOverlapDimension (K : ℕ) : ℝ :=
  (2 : ℝ) ^ (K / 2)

/-- Dimension-free lower factor obtained from the calibrated Pauli
eigenvalue floor after extracting the leading `2^n` from `D+1`. -/
noncomputable def choKimCurvatureFloor (n K : ℕ) : ℝ :=
  ((1 + ((2 : ℝ) ^ K)⁻¹)⁻¹) ^ (n / K)

/-- Literal calibrated eigenvalue floor obtained from
`(D+1) m_P` and Cho--Kim's lower bound
`m_P ≥ (2^K+1)^(-n/K)`. -/
noncomputable def choKimCalibratedEigenvalueFloor (n K : ℕ) : ℝ :=
  ((2 : ℝ) ^ n + 1) * ((((2 : ℝ) ^ K + 1)⁻¹) ^ (n / K))

theorem choKimOverlapDimension_pos (K : ℕ) :
    0 < choKimOverlapDimension K := by
  exact pow_pos (by norm_num) _

theorem choKimCurvatureFloor_pos (n K : ℕ) :
    0 < choKimCurvatureFloor n K := by
  unfold choKimCurvatureFloor
  positivity

theorem choKimCalibratedEigenvalueFloor_pos (n K : ℕ) :
    0 < choKimCalibratedEigenvalueFloor n K := by
  unfold choKimCalibratedEigenvalueFloor
  positivity

/-- If the total inverse-overlap exponent is at most `log 2`, the calibrated
eigenvalue floor is at least one half. -/
theorem half_le_inverse_one_add_inv_pow
    {z : ℝ} (hz : 0 < z) (m : ℕ)
    (hexponent : (m : ℝ) * z⁻¹ ≤ Real.log 2) :
    (1 : ℝ) / 2 ≤ ((1 + z⁻¹)⁻¹) ^ m := by
  have hbasePos : 0 < 1 + z⁻¹ := by positivity
  have hexpBase : Real.exp (-z⁻¹) ≤ (1 + z⁻¹)⁻¹ := by
    rw [Real.exp_neg]
    apply inv_anti₀ hbasePos
    simpa [add_comm] using Real.add_one_le_exp z⁻¹
  have hpow : (Real.exp (-z⁻¹)) ^ m ≤ ((1 + z⁻¹)⁻¹) ^ m :=
    pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) hexpBase m
  have hhalf : (1 : ℝ) / 2 = Real.exp (-Real.log 2) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [hhalf]
  calc
    Real.exp (-Real.log 2) ≤ Real.exp (-((m : ℝ) * z⁻¹)) := by
      exact Real.exp_le_exp.mpr (neg_le_neg hexponent)
    _ = (Real.exp (-z⁻¹)) ^ m := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ ((1 + z⁻¹)⁻¹) ^ m := hpow

/-- The four rational contributions in the gluing loss satisfy the manuscript's
simple `1/q` majorants as soon as `q ≥ 18`. -/
theorem choKimFThree_le_fortySix_div
    {q : ℝ} (hq : 18 ≤ q) :
    choKimFThree q ≤ 46 / q := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have h2q0 : 0 < 2 * q := mul_pos (by norm_num) hq0
  have h4q0 : 0 < 4 * q := mul_pos (by norm_num) hq0
  have hq2 : 0 < q ^ 2 := sq_pos_of_pos hq0
  have hden : 0 < 1 - 9 / (4 * q) := by
    rw [sub_pos]
    apply (div_lt_one h4q0).2
    nlinarith
  have hthird : 81 / (2 * q ^ 2) ≤ 9 / (4 * q) := by
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hq2) h4q0]
    nlinarith
  have hfrac : (9 / (4 * q)) / (1 - 9 / (4 * q)) ≤ 18 / (7 * q) := by
    rw [div_le_div_iff₀ hden (mul_pos (by norm_num) hq0)]
    field_simp
    nlinarith
  have hlast : 1 + 9 / (2 * q) ≤ 5 / 4 := by
    field_simp
    nlinarith
  have hsum :
      9 / q + 9 / (2 * q) + 81 / (2 * q ^ 2) +
          (9 / (4 * q)) / (1 - 9 / (4 * q)) ≤
        (9 + 9 / 2 + 9 / 4 + 18 / 7) / q := by
    calc
      9 / q + 9 / (2 * q) + 81 / (2 * q ^ 2) +
            (9 / (4 * q)) / (1 - 9 / (4 * q))
          ≤ 9 / q + 9 / (2 * q) + 9 / (4 * q) + 18 / (7 * q) := by
              linarith
      _ = (9 + 9 / 2 + 9 / 4 + 18 / 7) / q := by
        ring
  have hsum0 :
      0 ≤ 9 / q + 9 / (2 * q) + 81 / (2 * q ^ 2) +
          (9 / (4 * q)) / (1 - 9 / (4 * q)) := by
    positivity
  unfold choKimFThree
  calc
    2 *
        (9 / q + 9 / (2 * q) + 81 / (2 * q ^ 2) +
          (9 / (4 * q)) / (1 - 9 / (4 * q))) *
        (1 + 9 / (2 * q))
        ≤ 2 *
            ((9 + 9 / 2 + 9 / 4 + 18 / 7) / q) *
            (1 + 9 / (2 * q)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsum (by norm_num))
            (by positivity)
    _ ≤ 2 * ((9 + 9 / 2 + 9 / 4 + 18 / 7) / q) * (5 / 4) := by
      apply mul_le_mul_of_nonneg_left hlast
      positivity
    _ ≤ 46 / q := by
      rw [show 2 * ((9 + 9 / 2 + 9 / 4 + 18 / 7) / q) * (5 / 4) =
          (2565 / 56) / q by ring]
      exact div_le_div_of_nonneg_right (by norm_num) (le_of_lt hq0)

/-- The specialized two-block loss is nonnegative in the same range. -/
theorem choKimFThree_nonneg {q : ℝ} (hq : 18 ≤ q) :
    0 ≤ choKimFThree q := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hden : 0 < 1 - 9 / (4 * q) := by
    rw [sub_pos]
    apply (div_lt_one (mul_pos (by norm_num) hq0)).2
    nlinarith
  unfold choKimFThree
  positivity

/-- The elementary multiplicative-to-exponential estimate used before the
explicit gluing constants are inserted. -/
theorem one_add_pow_le_exp_nat_mul
    {x : ℝ} (hx : 0 ≤ x) (r : ℕ) :
    (1 + x) ^ r ≤ Real.exp ((r : ℝ) * x) := by
  have h := Real.prod_one_add_le_exp_sum
    (Finset.range r) (f := fun _ : ℕ ↦ x) (fun _ ↦ hx)
  simpa [Finset.prod_const, Finset.sum_const, nsmul_eq_mul] using h

/-- Number of independent local Clifford gates in the periodic two-layer
architecture (`n/K` gates in each of two layers). -/
def choKimGateVertices (n K : ℕ) : ℕ := 2 * (n / K)

/-- Removing one edge from the overlap cycle gives the spanning-tree gluing
count, bounded by the manuscript's real-valued `2n/K`. -/
theorem choKimGateVertices_sub_one_le_ratio
    {n K : ℕ} (hK : 0 < K) (hdiv : K ∣ n) :
    ((choKimGateVertices n K - 1 : ℕ) : ℝ) ≤
      2 * (n : ℝ) / (K : ℝ) := by
  calc
    ((choKimGateVertices n K - 1 : ℕ) : ℝ) ≤
        (choKimGateVertices n K : ℝ) := by
      exact_mod_cast Nat.sub_le (choKimGateVertices n K) 1
    _ = 2 * (n : ℝ) / (K : ℝ) := by
      have hKne : (K : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hK)
      have hcast : ((n / K : ℕ) : ℝ) = (n : ℝ) / (K : ℝ) :=
        Nat.cast_div hdiv hKne
      rw [choKimGateVertices, Nat.cast_mul, hcast]
      ring

/-- The explicit growth condition forces every admissible overlap dimension
past the `q = 18` threshold used by the rational estimate. -/
theorem eighteen_le_overlap_of_explicit_growth
    {n K : ℕ} (hn : 0 < n) (_hK : 0 < K) (hKn : K ≤ n)
    {q : ℝ} (hq : 0 ≤ q)
    (hgrowth : (92 / Real.log 2) * (n : ℝ) ≤ (K : ℝ) * q) :
    18 ≤ q := by
  have hlog : 0 < Real.log 2 := log_two_pos
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hKreal : (K : ℝ) ≤ (n : ℝ) := by exact_mod_cast hKn
  have hKq : (K : ℝ) * q ≤ (n : ℝ) * q :=
    mul_le_mul_of_nonneg_right hKreal hq
  have hcancel : 92 / Real.log 2 ≤ q := by
    exact (mul_le_mul_iff_of_pos_right hnreal).mp (by
      simpa [mul_comm] using hgrowth.trans hKq)
  have hlog_lt_one : Real.log 2 < 1 :=
    Real.log_two_lt_d9.trans (by norm_num)
  have heighteen : (18 : ℝ) ≤ 92 / Real.log 2 := by
    apply (le_div_iff₀ hlog).2
    nlinarith
  exact heighteen.trans hcancel

/-- A form directly specialized to the arithmetic block predicate. -/
theorem ChoKimBlockCondition.eighteen_le_overlap
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) :
    18 ≤ choKimOverlapDimension K := by
  apply eighteen_le_overlap_of_explicit_growth hn h.block_pos
    (h.block_le_qubits hn) (le_of_lt (choKimOverlapDimension_pos K))
  simpa [choKimOverlapDimension] using h.explicit_growth

/-- The block condition therefore gives the explicit order-three local loss
bound with no asymptotic notation. -/
theorem ChoKimBlockCondition.fThree_le
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) :
    choKimFThree (choKimOverlapDimension K) ≤
      46 / choKimOverlapDimension K :=
  choKimFThree_le_fortySix_div (h.eighteen_le_overlap hn)

/-- The same explicit growth condition controls the inverse-eigenvalue
exponent needed for a dimension-free curvature constant. -/
theorem ChoKimBlockCondition.curvatureExponent_le_log_two
    {n K : ℕ} (h : ChoKimBlockCondition n K) :
    ((n / K : ℕ) : ℝ) * (((2 : ℝ) ^ K)⁻¹) ≤ Real.log 2 := by
  obtain ⟨m, rfl⟩ := h.block_dvd
  have hlog : 0 < Real.log 2 := log_two_pos
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast h.block_pos
  let q : ℝ := (2 : ℝ) ^ (K / 2)
  let z : ℝ := (2 : ℝ) ^ K
  have hq0 : 0 ≤ q := by positivity
  have hz : 0 < z := by positivity
  have hqz : q ≤ z := by
    dsimp [q, z]
    exact pow_le_pow_right₀ (by norm_num) (Nat.div_le_self K 2)
  have hgrowth := h.explicit_growth
  have hgrowth' :
      (K : ℝ) * ((92 / Real.log 2) * (m : ℝ)) ≤
        (K : ℝ) * q := by
    calc
      (K : ℝ) * ((92 / Real.log 2) * (m : ℝ)) =
          (92 / Real.log 2) * ((K : ℝ) * (m : ℝ)) := by ring
      _ ≤ (K : ℝ) * q := by
        simpa [q, Nat.cast_mul] using hgrowth
  have hcancel : (92 / Real.log 2) * (m : ℝ) ≤ q :=
    (mul_le_mul_iff_of_pos_left hKreal).mp hgrowth'
  have h92q : 92 * (m : ℝ) ≤ Real.log 2 * q := by
    have hmul := (mul_le_mul_iff_of_pos_left hlog).2 hcancel
    have hleft : Real.log 2 * ((92 / Real.log 2) * (m : ℝ)) =
        92 * (m : ℝ) := by
      field_simp
    simpa [hleft] using hmul
  have h92z : 92 * (m : ℝ) ≤ Real.log 2 * z :=
    h92q.trans (mul_le_mul_of_nonneg_left hqz hlog.le)
  have hmz : (m : ℝ) ≤ Real.log 2 * z := by
    have hm0 : 0 ≤ (m : ℝ) := by positivity
    nlinarith
  have hexponent : (m : ℝ) * z⁻¹ ≤ Real.log 2 := by
    exact (mul_inv_le_iff₀ hz).2 (by simpa [mul_comm] using hmz)
  have hdivnat : K * m / K = m := by
    rw [Nat.mul_comm]
    exact Nat.mul_div_left m h.block_pos
  simpa [z, hdivnat] using hexponent

/-- Thus the calibrated nonidentity Pauli spectrum has an explicit universal
curvature floor `1/2`; no hidden asymptotic constant remains in this step. -/
theorem ChoKimBlockCondition.half_le_curvatureFloor
    {n K : ℕ} (h : ChoKimBlockCondition n K) :
    (1 : ℝ) / 2 ≤ choKimCurvatureFloor n K := by
  exact half_le_inverse_one_add_inv_pow
    (pow_pos (by norm_num) K) (n / K) h.curvatureExponent_le_log_two

/-- The simplified curvature floor is below the literal calibrated
eigenvalue floor whenever `K` divides `n`. -/
theorem ChoKimBlockCondition.curvatureFloor_le_calibratedEigenvalueFloor
    {n K : ℕ} (h : ChoKimBlockCondition n K) :
    choKimCurvatureFloor n K ≤
      choKimCalibratedEigenvalueFloor n K := by
  obtain ⟨m, rfl⟩ := h.block_dvd
  let z : ℝ := (2 : ℝ) ^ K
  have hz : 0 < z := by positivity
  have hdivnat : K * m / K = m := by
    rw [Nat.mul_comm]
    exact Nat.mul_div_left m h.block_pos
  have hbase : (1 + z⁻¹)⁻¹ = z * (z + 1)⁻¹ := by
    field_simp
  have hfloor : choKimCurvatureFloor (K * m) K =
      (2 : ℝ) ^ (K * m) * ((z + 1)⁻¹ ^ m) := by
    rw [choKimCurvatureFloor, hdivnat, show ((2 : ℝ) ^ K) = z by rfl,
      hbase, mul_pow, pow_mul]
  rw [hfloor, choKimCalibratedEigenvalueFloor, hdivnat,
    show ((2 : ℝ) ^ K) = z by rfl]
  exact mul_le_mul_of_nonneg_right
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))
    (by positivity)

/-- Final explicit curvature constant obtained from the published Pauli
eigenvalue floor: the calibrated spectrum is uniformly at least `1/2`. -/
theorem ChoKimBlockCondition.half_le_calibratedEigenvalueFloor
    {n K : ℕ} (h : ChoKimBlockCondition n K) :
    (1 : ℝ) / 2 ≤ choKimCalibratedEigenvalueFloor n K :=
  h.half_le_curvatureFloor.trans
    h.curvatureFloor_le_calibratedEigenvalueFloor

/-- The `92` in the block condition is exactly what makes the accumulated
`2 * 46` gluing exponent at most `log 2`. -/
theorem choKimAccumulatedExponent_le_log_two
    {n K : ℕ} (hn : 0 < n) (hK : 0 < K)
    {q : ℝ} (hq : 0 < q)
    (hgrowth : (92 / Real.log 2) * (n : ℝ) ≤ (K : ℝ) * q) :
    (2 * (n : ℝ) / (K : ℝ)) * (46 / q) ≤ Real.log 2 := by
  have hlog : 0 < Real.log 2 := log_two_pos
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
  have hprod : 0 < (K : ℝ) * q := mul_pos hKreal hq
  have hgrowth' : 92 * (n : ℝ) ≤
      Real.log 2 * ((K : ℝ) * q) := by
    have hmul := (mul_le_mul_iff_of_pos_left hlog).2 hgrowth
    have hleft : Real.log 2 * ((92 / Real.log 2) * (n : ℝ)) =
        92 * (n : ℝ) := by
      field_simp
    simpa [hleft, mul_assoc] using hmul
  rw [show (2 * (n : ℝ) / (K : ℝ)) * (46 / q) =
      92 * (n : ℝ) / ((K : ℝ) * q) by field_simp; ring]
  exact (div_le_iff₀ hprod).2 hgrowth'

/-- Once the cited gluing theorem has produced the exponential error bound,
the explicit block condition closes the relative-error gate `epsilon ≤ 1`. -/
theorem relativeDesignError_le_one_of_exponential_bound
    {exponent epsilon : ℝ}
    (hexponent : exponent ≤ Real.log 2)
    (hepsilon : epsilon ≤ Real.exp exponent - 1) :
    epsilon ≤ 1 := by
  calc
    epsilon ≤ Real.exp exponent - 1 := hepsilon
    _ ≤ Real.exp (Real.log 2) - 1 :=
      sub_le_sub_right (Real.exp_le_exp.mpr hexponent) 1
    _ = 1 := by rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num

/-- End-to-end scalar specialization of the published gluing estimate.  The
only non-arithmetic premise is `hepsilon`, the output of the relative-design
gluing theorem for this concrete circuit. -/
theorem ChoKimBlockCondition.relativeDesignError_le_one
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    {epsilon : ℝ}
    (hepsilon : epsilon ≤
      Real.exp
        ((2 * (n : ℝ) / (K : ℝ)) *
          (46 / choKimOverlapDimension K)) - 1) :
    epsilon ≤ 1 := by
  apply relativeDesignError_le_one_of_exponential_bound
    (choKimAccumulatedExponent_le_log_two hn h.block_pos
      (choKimOverlapDimension_pos K) (by
        simpa [choKimOverlapDimension] using h.explicit_growth))
    hepsilon

/-- The literal multiplicative expression produced by iterating the
two-block gluing theorem is already enough to obtain relative error at most
one.  Unlike `relativeDesignError_le_one`, this interface does not ask a
caller to simplify the gluing expression first. -/
theorem ChoKimBlockCondition.relativeDesignError_le_one_of_raw_gluing
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    {epsilon : ℝ}
    (hepsilon : epsilon ≤
      (1 + choKimFThree (choKimOverlapDimension K)) ^
          (choKimGateVertices n K - 1) - 1) :
    epsilon ≤ 1 := by
  let q := choKimOverlapDimension K
  let r := choKimGateVertices n K - 1
  have hq18 : 18 ≤ q := by
    simpa [q] using h.eighteen_le_overlap hn
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq18
  have hf0 : 0 ≤ choKimFThree q := choKimFThree_nonneg hq18
  have hf : choKimFThree q ≤ 46 / q :=
    choKimFThree_le_fortySix_div hq18
  have hr : (r : ℝ) ≤ 2 * (n : ℝ) / (K : ℝ) := by
    simpa [r] using
      choKimGateVertices_sub_one_le_ratio h.block_pos h.block_dvd
  have hratio0 : 0 ≤ 2 * (n : ℝ) / (K : ℝ) := by
    positivity
  have hfortySix0 : 0 ≤ 46 / q := by positivity
  have hexponent :
      (r : ℝ) * choKimFThree q ≤
        (2 * (n : ℝ) / (K : ℝ)) * (46 / q) :=
    mul_le_mul hr hf hf0 hratio0
  have hpow :
      (1 + choKimFThree q) ^ r ≤
        Real.exp ((r : ℝ) * choKimFThree q) :=
    one_add_pow_le_exp_nat_mul hf0 r
  have hrawExp : epsilon ≤
      Real.exp
        ((2 * (n : ℝ) / (K : ℝ)) * (46 / q)) - 1 := by
    calc
      epsilon ≤ (1 + choKimFThree q) ^ r - 1 := by
        simpa [q, r] using hepsilon
      _ ≤ Real.exp ((r : ℝ) * choKimFThree q) - 1 :=
        sub_le_sub_right hpow 1
      _ ≤ Real.exp
            ((2 * (n : ℝ) / (K : ℝ)) * (46 / q)) - 1 :=
        sub_le_sub_right (Real.exp_le_exp.mpr hexponent) 1
  apply h.relativeDesignError_le_one hn
  simpa [q] using hrawExp

/-- The final constant substitution in the positive-observable shadow
variance estimate.  For a rank-one projector in dimension `D`, the centered
Hilbert--Schmidt square is `1 - D⁻¹` and the trace square is one.  Thus the
published estimate
`variance ≤ 3 * (1 - D⁻¹) + 10 * epsilon` is at most `13` whenever the
relative-design error is at most one. -/
theorem choKimRankOneVariance_le_thirteen
    {D : ℕ} (hD : 0 < D) {epsilon variance : ℝ}
    (hepsilon : epsilon ≤ 1)
    (hvariance : variance ≤ 3 * (1 - ((D : ℝ)⁻¹)) + 10 * epsilon) :
    variance ≤ 13 := by
  have hDreal : 0 < (D : ℝ) := by exact_mod_cast hD
  have hinv : 0 ≤ ((D : ℝ)⁻¹) := (inv_nonneg.mpr hDreal.le)
  linarith

end TomographyOracleCore
