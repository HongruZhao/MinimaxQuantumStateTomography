import TomographyOracleCore.RelativeDesignTwoUnitaryGluing

namespace TomographyOracleCore

open scoped CStarAlgebra

noncomputable section

/-!
# Constructive finite relative-design gluing

This closes the logical gap between one two-unitary gluing theorem and a
finite circuit.  The final relative-design statement is derived by induction
from the literal circuit-prefix compositions, local relative designs, and
reference-gluing estimates; it is not supplied as a final-design premise.
-/

/-- Constructive finite iteration of the two-unitary relative-design gluing
lemma.  The circuit prefix at `i+1` is literally the composition of the
prefix at `i` with the next local ensemble.  Its global reference is obtained
from the analogous reference composition by one reference-gluing estimate. -/
theorem relativeCPApproximation_iterate_twoUnitary
    {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    {r : ℕ}
    (ensemble globalReference localEnsemble localReference :
      ℕ → A →CP A)
    (error localError referenceError : ℕ → ℝ)
    (hprefix : ∀ i < r,
      ensemble (i + 1) =
        CompletelyPositiveMap.comp (ensemble i) (localEnsemble i))
    (herrorBounds : ∀ i ≤ r, 0 ≤ error i ∧ error i ≤ 1)
    (hlocalBounds : ∀ i < r,
      0 ≤ localError i ∧ localError i ≤ 1)
    (hreferenceError : ∀ i < r, 0 ≤ referenceError i)
    (hbase : RelativeCPApproximation (error 0)
      (ensemble 0).toLinearMap (globalReference 0).toLinearMap)
    (hlocal : ∀ i < r, RelativeCPApproximation (localError i)
      (localEnsemble i).toLinearMap (localReference i).toLinearMap)
    (hreference : ∀ i < r, RelativeCPApproximation (referenceError i)
      (CompletelyPositiveMap.comp
        (globalReference i) (localReference i)).toLinearMap
      (globalReference (i + 1)).toLinearMap)
    (hrecurrence : ∀ i < r,
      error (i + 1) =
        (1 + error i) * (1 + localError i) *
          (1 + referenceError i) - 1) :
    RelativeCPApproximation (error r)
      (ensemble r).toLinearMap (globalReference r).toLinearMap := by
  have hthrough : ∀ j ≤ r, RelativeCPApproximation (error j)
      (ensemble j).toLinearMap (globalReference j).toLinearMap := by
    intro j hj
    induction j with
    | zero => exact hbase
    | succ j ih =>
        have hjr : j < r := by omega
        have hprevious := ih (by omega)
        have hstep := relativeCPApproximation_twoUnitary_of_reference_gluing
          (ensemble j) (globalReference j)
          (localEnsemble j) (localReference j)
          (globalReference (j + 1))
          (error j) (localError j) (referenceError j)
          (herrorBounds j (by omega)).1
          (herrorBounds j (by omega)).2
          (hlocalBounds j hjr).1
          (hlocalBounds j hjr).2
          (hreferenceError j hjr)
          hprevious (hlocal j hjr) (hreference j hjr)
        rw [hrecurrence j hjr, hprefix j hjr]
        exact hstep
  exact hthrough r le_rfl

/-- Left-composition version of the constructive iteration.  It is needed
when a new gate belongs to the later circuit layer and therefore acts on the
left of the already assembled prefix. -/
theorem relativeCPApproximation_iterate_twoUnitary_left
    {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    {r : ℕ}
    (ensemble globalReference localEnsemble localReference :
      ℕ → A →CP A)
    (error localError referenceError : ℕ → ℝ)
    (hprefix : ∀ i < r,
      ensemble (i + 1) =
        CompletelyPositiveMap.comp (localEnsemble i) (ensemble i))
    (herrorBounds : ∀ i ≤ r, 0 ≤ error i ∧ error i ≤ 1)
    (hlocalBounds : ∀ i < r,
      0 ≤ localError i ∧ localError i ≤ 1)
    (hreferenceError : ∀ i < r, 0 ≤ referenceError i)
    (hbase : RelativeCPApproximation (error 0)
      (ensemble 0).toLinearMap (globalReference 0).toLinearMap)
    (hlocal : ∀ i < r, RelativeCPApproximation (localError i)
      (localEnsemble i).toLinearMap (localReference i).toLinearMap)
    (hreference : ∀ i < r, RelativeCPApproximation (referenceError i)
      (CompletelyPositiveMap.comp
        (localReference i) (globalReference i)).toLinearMap
      (globalReference (i + 1)).toLinearMap)
    (hrecurrence : ∀ i < r,
      error (i + 1) =
        (1 + error i) * (1 + localError i) *
          (1 + referenceError i) - 1) :
    RelativeCPApproximation (error r)
      (ensemble r).toLinearMap (globalReference r).toLinearMap := by
  have hthrough : ∀ j ≤ r, RelativeCPApproximation (error j)
      (ensemble j).toLinearMap (globalReference j).toLinearMap := by
    intro j hj
    induction j with
    | zero => exact hbase
    | succ j ih =>
        have hjr : j < r := by omega
        have hprevious := ih (by omega)
        have hstep := relativeCPApproximation_twoUnitary_of_reference_gluing
          (localEnsemble j) (localReference j)
          (ensemble j) (globalReference j)
          (globalReference (j + 1))
          (localError j) (error j) (referenceError j)
          (hlocalBounds j hjr).1
          (hlocalBounds j hjr).2
          (herrorBounds j (by omega)).1
          (herrorBounds j (by omega)).2
          (hreferenceError j hjr)
          (hlocal j hjr) hprevious (hreference j hjr)
        rw [hrecurrence j hjr, hprefix j hjr]
        convert hstep using 1
        ring
  exact hthrough r le_rfl

/-- Mixed left/right composition version, matching a spanning-tree traversal
through two circuit layers.  At each step the Boolean specifies whether the
new local gate acts to the left or to the right of the assembled circuit. -/
theorem relativeCPApproximation_iterate_twoUnitary_mixed
    {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    {r : ℕ}
    (left : ℕ → Bool)
    (ensemble globalReference localEnsemble localReference :
      ℕ → A →CP A)
    (error localError referenceError : ℕ → ℝ)
    (hprefix : ∀ i < r,
      ensemble (i + 1) = if left i then
        CompletelyPositiveMap.comp (localEnsemble i) (ensemble i)
      else CompletelyPositiveMap.comp (ensemble i) (localEnsemble i))
    (herrorBounds : ∀ i ≤ r, 0 ≤ error i ∧ error i ≤ 1)
    (hlocalBounds : ∀ i < r,
      0 ≤ localError i ∧ localError i ≤ 1)
    (hreferenceError : ∀ i < r, 0 ≤ referenceError i)
    (hbase : RelativeCPApproximation (error 0)
      (ensemble 0).toLinearMap (globalReference 0).toLinearMap)
    (hlocal : ∀ i < r, RelativeCPApproximation (localError i)
      (localEnsemble i).toLinearMap (localReference i).toLinearMap)
    (hreference : ∀ i < r, RelativeCPApproximation (referenceError i)
      (if left i then CompletelyPositiveMap.comp
          (localReference i) (globalReference i)
        else CompletelyPositiveMap.comp
          (globalReference i) (localReference i)).toLinearMap
      (globalReference (i + 1)).toLinearMap)
    (hrecurrence : ∀ i < r,
      error (i + 1) =
        (1 + error i) * (1 + localError i) *
          (1 + referenceError i) - 1) :
    RelativeCPApproximation (error r)
      (ensemble r).toLinearMap (globalReference r).toLinearMap := by
  have hthrough : ∀ j ≤ r, RelativeCPApproximation (error j)
      (ensemble j).toLinearMap (globalReference j).toLinearMap := by
    intro j hj
    induction j with
    | zero => exact hbase
    | succ j ih =>
        have hjr : j < r := by omega
        have hprevious := ih (by omega)
        cases hleft : left j with
        | false =>
            have hstep := relativeCPApproximation_twoUnitary_of_reference_gluing
              (ensemble j) (globalReference j)
              (localEnsemble j) (localReference j)
              (globalReference (j + 1))
              (error j) (localError j) (referenceError j)
              (herrorBounds j (by omega)).1
              (herrorBounds j (by omega)).2
              (hlocalBounds j hjr).1
              (hlocalBounds j hjr).2
              (hreferenceError j hjr)
              hprevious (hlocal j hjr)
              (by simpa [hleft] using hreference j hjr)
            rw [hrecurrence j hjr, hprefix j hjr]
            simpa [hleft] using hstep
        | true =>
            have hstep := relativeCPApproximation_twoUnitary_of_reference_gluing
              (localEnsemble j) (localReference j)
              (ensemble j) (globalReference j)
              (globalReference (j + 1))
              (localError j) (error j) (referenceError j)
              (hlocalBounds j hjr).1
              (hlocalBounds j hjr).2
              (herrorBounds j (by omega)).1
              (herrorBounds j (by omega)).2
              (hreferenceError j hjr)
              (hlocal j hjr) hprevious
              (by simpa [hleft] using hreference j hjr)
            rw [hrecurrence j hjr, hprefix j hjr]
            simpa [hleft, mul_comm] using hstep
  exact hthrough r le_rfl

end
end TomographyOracleCore
