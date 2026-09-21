import TomographyOracleCore.PeriodicCliffordFourthTransferArithmetic

namespace TomographyOracleCore

noncomputable section

-- The two finite certificates below normalize explicit `30 × 30` tables.
-- Kernel reduction happens after tactic elaboration, so the budget must be
-- module-scoped rather than local to the `decide` invocation.
set_option maxHeartbeats 5000000

/-!
# Exact finite `t = 4` qubit Clifford sectors

This file replaces the Python-only `30`-sector check by kernel-checked Lean
certificates.  A sector is represented by four independent vectors in
`F₂^8`; `qubitFourthBinarySpan` takes their sixteen XOR combinations.  The
displayed bases are the thirty stochastic, quadratic-zero sectors used in the
fourth-copy qubit Clifford commutant.

The finite proofs use `decide`, not `native_decide`.  Consequently the audit
does not acquire a compiler-oracle axiom.
-/

abbrev QubitFourthBinaryVector := BitVec 8
abbrev QubitFourthBinaryBasis := Vector QubitFourthBinaryVector 4

/-- The sixteen XOR combinations of four binary row vectors. -/
def qubitFourthBinarySpan (b : QubitFourthBinaryBasis) : List QubitFourthBinaryVector :=
  List.ofFn fun mask : Fin 16 =>
    BitVec.xor (if mask.val.testBit 0 then b[0] else 0#8)
      (BitVec.xor (if mask.val.testBit 1 then b[1] else 0#8)
        (BitVec.xor (if mask.val.testBit 2 then b[2] else 0#8)
          (if mask.val.testBit 3 then b[3] else 0#8)))

/-- The `q(x)=0` condition in the stochastic-Lagrangian model over `F₂`:
the Hamming weights of the two four-bit halves agree modulo four. -/
def qubitFourthQuadraticZero (v : QubitFourthBinaryVector) : Bool :=
  (v.extractLsb 3 0).cpop.toNat % 4 == (v.extractLsb 7 4).cpop.toNat % 4

/-- Explicit RREF bases for the thirty qubit fourth-copy sectors. -/
def qubitFourthSectorBases : Vector QubitFourthBinaryBasis 30 := #v[
  #v[15#8, 51#8, 85#8, 150#8],
  #v[15#8, 51#8, 86#8, 149#8],
  #v[15#8, 53#8, 83#8, 150#8],
  #v[15#8, 53#8, 86#8, 147#8],
  #v[15#8, 54#8, 83#8, 149#8],
  #v[15#8, 54#8, 85#8, 147#8],
  #v[17#8, 34#8, 68#8, 136#8],
  #v[17#8, 34#8, 72#8, 132#8],
  #v[17#8, 36#8, 66#8, 136#8],
  #v[17#8, 36#8, 72#8, 130#8],
  #v[17#8, 40#8, 66#8, 132#8],
  #v[17#8, 40#8, 68#8, 130#8],
  #v[18#8, 33#8, 68#8, 136#8],
  #v[18#8, 33#8, 72#8, 132#8],
  #v[18#8, 36#8, 65#8, 136#8],
  #v[18#8, 36#8, 72#8, 129#8],
  #v[18#8, 40#8, 65#8, 132#8],
  #v[18#8, 40#8, 68#8, 129#8],
  #v[20#8, 33#8, 66#8, 136#8],
  #v[20#8, 33#8, 72#8, 130#8],
  #v[20#8, 34#8, 65#8, 136#8],
  #v[20#8, 34#8, 72#8, 129#8],
  #v[20#8, 40#8, 65#8, 130#8],
  #v[20#8, 40#8, 66#8, 129#8],
  #v[24#8, 33#8, 66#8, 132#8],
  #v[24#8, 33#8, 68#8, 130#8],
  #v[24#8, 34#8, 65#8, 132#8],
  #v[24#8, 34#8, 68#8, 129#8],
  #v[24#8, 36#8, 65#8, 130#8],
  #v[24#8, 36#8, 66#8, 129#8]
]

/-- The actual sixteen-vector carrier of sector `i`. -/
def qubitFourthSector (i : Fin 30) : List QubitFourthBinaryVector :=
  qubitFourthBinarySpan qubitFourthSectorBases[i]

/-- Cardinality of the intersection of two explicitly represented sectors. -/
def qubitFourthIntersectionCard (i j : Fin 30) : Nat :=
  (qubitFourthSector i).countP fun v => (qubitFourthSector j).contains v

/-- Binary dimension of a sector intersection. -/
def qubitFourthIntersectionDimension (i j : Fin 30) : Nat :=
  Nat.log2 (qubitFourthIntersectionCard i j)

/-- Every displayed carrier has sixteen distinct vectors, contains the all-one
vector, and is quadratic-zero.  Since it is an XOR span by construction, this
is the finite subspace/stochastic certificate. -/
theorem qubitFourthSector_valid : ∀ i : Fin 30,
    (qubitFourthSector i).Nodup ∧
      (255#8 ∈ qubitFourthSector i) ∧
      (qubitFourthSector i).all qubitFourthQuadraticZero = true := by
  decide

theorem qubitFourthSector_card (i : Fin 30) : (qubitFourthSector i).length = 16 := by
  rfl

/-! ## Certified intersection matrix -/

/-- The complete `30 × 30` intersection-dimension matrix.  It is kept as a
literal certificate so the later association-table computation does not
recompute binary spans hundreds of thousands of times. -/
def qubitFourthIntersectionMatrix : Vector (Vector Nat 30) 30 := #v[
  #v[4,3,3,2,2,3,3,2,2,1,1,2,2,3,1,2,2,1,1,2,2,1,3,2,2,1,1,2,2,3],
  #v[3,4,2,3,3,2,2,3,1,2,2,1,3,2,2,1,1,2,2,1,1,2,2,3,1,2,2,1,3,2],
  #v[3,2,4,3,3,2,2,1,3,2,2,1,1,2,2,1,3,2,2,3,1,2,2,1,1,2,2,3,1,2],
  #v[2,3,3,4,2,3,1,2,2,3,1,2,2,1,1,2,2,3,3,2,2,1,1,2,2,1,3,2,2,1],
  #v[2,3,3,2,4,3,1,2,2,1,3,2,2,1,3,2,2,1,1,2,2,3,1,2,2,3,1,2,2,1],
  #v[3,2,2,3,3,4,2,1,1,2,2,3,1,2,2,3,1,2,2,1,3,2,2,1,3,2,2,1,1,2],
  #v[3,2,2,1,1,2,4,3,3,2,2,3,3,2,2,1,1,2,2,1,3,2,2,1,1,2,2,3,1,2],
  #v[2,3,1,2,2,1,3,4,2,3,3,2,2,3,1,2,2,1,1,2,2,3,1,2,2,1,3,2,2,1],
  #v[2,1,3,2,2,1,3,2,4,3,3,2,2,1,3,2,2,1,3,2,2,1,1,2,2,1,1,2,2,3],
  #v[1,2,2,3,1,2,2,3,3,4,2,3,1,2,2,3,1,2,2,3,1,2,2,1,1,2,2,1,3,2],
  #v[1,2,2,1,3,2,2,3,3,2,4,3,1,2,2,1,3,2,2,1,1,2,2,3,3,2,2,1,1,2],
  #v[2,1,1,2,2,3,3,2,2,3,3,4,2,1,1,2,2,3,1,2,2,1,3,2,2,3,1,2,2,1],
  #v[2,3,1,2,2,1,3,2,2,1,1,2,4,3,3,2,2,3,3,2,2,1,1,2,2,3,1,2,2,1],
  #v[3,2,2,1,1,2,2,3,1,2,2,1,3,4,2,3,3,2,2,3,1,2,2,1,3,2,2,1,1,2],
  #v[1,2,2,1,3,2,2,1,3,2,2,1,3,2,4,3,3,2,2,1,3,2,2,1,1,2,2,1,3,2],
  #v[2,1,1,2,2,3,1,2,2,3,1,2,2,3,3,4,2,3,1,2,2,3,1,2,2,1,1,2,2,3],
  #v[2,1,3,2,2,1,1,2,2,1,3,2,2,3,3,2,4,3,1,2,2,1,3,2,2,1,3,2,2,1],
  #v[1,2,2,3,1,2,2,1,1,2,2,3,3,2,2,3,3,4,2,1,1,2,2,3,1,2,2,3,1,2],
  #v[1,2,2,3,1,2,2,1,3,2,2,1,3,2,2,1,1,2,4,3,3,2,2,3,3,2,2,1,1,2],
  #v[2,1,3,2,2,1,1,2,2,3,1,2,2,3,1,2,2,1,3,4,2,3,3,2,2,3,1,2,2,1],
  #v[2,1,1,2,2,3,3,2,2,1,1,2,2,1,3,2,2,1,3,2,4,3,3,2,2,1,3,2,2,1],
  #v[1,2,2,1,3,2,2,3,1,2,2,1,1,2,2,3,1,2,2,3,3,4,2,3,1,2,2,3,1,2],
  #v[3,2,2,1,1,2,2,1,1,2,2,3,1,2,2,1,3,2,2,3,3,2,4,3,1,2,2,1,3,2],
  #v[2,3,1,2,2,1,1,2,2,1,3,2,2,1,1,2,2,3,3,2,2,3,3,4,2,1,1,2,2,3],
  #v[2,1,1,2,2,3,1,2,2,1,3,2,2,3,1,2,2,1,3,2,2,1,1,2,4,3,3,2,2,3],
  #v[1,2,2,1,3,2,2,1,1,2,2,3,3,2,2,1,1,2,2,3,1,2,2,1,3,4,2,3,3,2],
  #v[1,2,2,3,1,2,2,3,1,2,2,1,1,2,2,1,3,2,2,1,3,2,2,1,3,2,4,3,3,2],
  #v[2,1,3,2,2,1,3,2,2,1,1,2,2,1,1,2,2,3,1,2,2,3,1,2,2,3,3,4,2,3],
  #v[2,3,1,2,2,1,1,2,2,3,1,2,2,1,3,2,2,1,1,2,2,1,3,2,2,3,3,2,4,3],
  #v[3,2,2,1,1,2,2,1,3,2,2,1,1,2,2,3,1,2,2,1,1,2,2,3,3,2,2,3,3,4]
]

def qubitFourthIntersectionEntry (i j : Fin 30) : Nat :=
  qubitFourthIntersectionMatrix[i][j]

/-- Kernel-checked connection between the literal matrix and actual
intersections of the explicit `BitVec 8` spans. -/
theorem qubitFourthIntersectionMatrix_exact : ∀ i j : Fin 30,
    qubitFourthIntersectionDimension i j = qubitFourthIntersectionEntry i j := by
  decide

/-! ## Row profile and the four association tables -/

def qubitFourthRowCount (i : Fin 30) (h : Nat) : Nat :=
  (List.finRange 30).countP fun j => qubitFourthIntersectionEntry i j == h

theorem qubitFourthRowCount_one_all : ∀ i : Fin 30, qubitFourthRowCount i 1 = 8 := by
  decide
theorem qubitFourthRowCount_two_all : ∀ i : Fin 30, qubitFourthRowCount i 2 = 14 := by
  decide
theorem qubitFourthRowCount_three_all : ∀ i : Fin 30, qubitFourthRowCount i 3 = 7 := by
  decide
theorem qubitFourthRowCount_four_all : ∀ i : Fin 30, qubitFourthRowCount i 4 = 1 := by
  decide

theorem qubitFourthRowCount_one (i : Fin 30) : qubitFourthRowCount i 1 = 8 :=
  qubitFourthRowCount_one_all i
theorem qubitFourthRowCount_two (i : Fin 30) : qubitFourthRowCount i 2 = 14 :=
  qubitFourthRowCount_two_all i
theorem qubitFourthRowCount_three (i : Fin 30) : qubitFourthRowCount i 3 = 7 :=
  qubitFourthRowCount_three_all i
theorem qubitFourthRowCount_four (i : Fin 30) : qubitFourthRowCount i 4 = 1 :=
  qubitFourthRowCount_four_all i

/-- Uniform row profile, ordered by intersection dimensions `1,2,3,4`. -/
theorem qubitFourthRowProfile (i : Fin 30) :
    (qubitFourthRowCount i 1, qubitFourthRowCount i 2,
      qubitFourthRowCount i 3, qubitFourthRowCount i 4) = (8, 14, 7, 1) := by
  rw [qubitFourthRowCount_one, qubitFourthRowCount_two,
    qubitFourthRowCount_three, qubitFourthRowCount_four]

/-- `N₁(i,j)`, with row/column zero included as a zero sentinel. -/
def qubitFourthNOne : Vector (Vector Nat 5) 5 := #v[
  #v[0,0,0,0,0], #v[0,0,7,0,1], #v[0,7,0,7,0],
  #v[0,0,7,0,0], #v[0,1,0,0,0]
]

/-- `N₂(i,j)`, with row/column zero included as a zero sentinel. -/
def qubitFourthNTwo : Vector (Vector Nat 5) 5 := #v[
  #v[0,0,0,0,0], #v[0,4,0,4,0], #v[0,0,13,0,1],
  #v[0,4,0,3,0], #v[0,0,1,0,0]
]

/-- `N₃(i,j)`, with row/column zero included as a zero sentinel. -/
def qubitFourthNThree : Vector (Vector Nat 5) 5 := #v[
  #v[0,0,0,0,0], #v[0,0,8,0,0], #v[0,8,0,6,0],
  #v[0,0,6,0,1], #v[0,0,0,1,0]
]

/-- `N₄(i,j)`, with row/column zero included as a zero sentinel. -/
def qubitFourthNFour : Vector (Vector Nat 5) 5 := #v[
  #v[0,0,0,0,0], #v[0,8,0,0,0], #v[0,0,14,0,0],
  #v[0,0,0,7,0], #v[0,0,0,0,1]
]

def qubitFourthAssociationTable (h : Nat) : Vector (Vector Nat 5) 5 :=
  match h with
  | 1 => qubitFourthNOne
  | 2 => qubitFourthNTwo
  | 3 => qubitFourthNThree
  | 4 => qubitFourthNFour
  | _ => #v[#v[0,0,0,0,0], #v[0,0,0,0,0], #v[0,0,0,0,0],
      #v[0,0,0,0,0], #v[0,0,0,0,0]]

def qubitFourthAssociationNumber (h : Nat) (a b : Fin 5) : Nat :=
  (qubitFourthAssociationTable h)[a][b]

def qubitFourthAssociationCount (left right : Fin 30) (a b : Fin 5) : Nat :=
  (List.finRange 30).countP fun middle =>
    qubitFourthIntersectionEntry left middle == a.val &&
      qubitFourthIntersectionEntry middle right == b.val

/-- The four displayed `N_h` tables hold for every ordered pair of sectors,
not merely for one representative of each intersection class. -/
theorem qubitFourthAssociationTables_exact : ∀ left right : Fin 30, ∀ a b : Fin 5,
    qubitFourthAssociationCount left right a b =
      qubitFourthAssociationNumber (qubitFourthIntersectionEntry left right) a b := by
  decide

/-! ## Connection to the scalar inverse-Gram module -/

/-- The certified row profile produces exactly the Gram row polynomial used
by `PeriodicCliffordFourthTransferArithmetic`. -/
theorem qubitFourthGramRowPolynomial_eq (i : Fin 30) (x : ℝ) :
    qubitFourthRowCount i 1 * x + qubitFourthRowCount i 2 * x ^ 2 +
        qubitFourthRowCount i 3 * x ^ 3 + qubitFourthRowCount i 4 * x ^ 4 =
      cliffordFourthGramRowSum x := by
  rw [qubitFourthRowCount_one, qubitFourthRowCount_two,
    qubitFourthRowCount_three, qubitFourthRowCount_four]
  unfold cliffordFourthGramRowSum
  norm_num

def qubitFourthWgCoefficient (h : Fin 5) (x : ℝ) : ℝ :=
  match h.val with
  | 1 => cliffordFourthWgOne x
  | 2 => cliffordFourthWgTwo x
  | 3 => cliffordFourthWgThree x
  | 4 => cliffordFourthWgFour x
  | _ => 0

/-- Association-table convolution `Σ_{i,j} N_h(i,j) w_i(x) x^j`. -/
def qubitFourthAssociationWeightedSum (h : Nat) (x : ℝ) : ℝ :=
  ((List.finRange 5).map fun i =>
    ((List.finRange 5).map fun j =>
      (qubitFourthAssociationNumber h i j : ℝ) *
        qubitFourthWgCoefficient i x * x ^ j.val).sum).sum

theorem qubitFourthAssociationWeightedSum_one (x : ℝ) :
    qubitFourthAssociationWeightedSum 1 x =
      7 * cliffordFourthWgOne x * x ^ 2 + cliffordFourthWgOne x * x ^ 4 +
      7 * cliffordFourthWgTwo x * x + 7 * cliffordFourthWgTwo x * x ^ 3 +
      7 * cliffordFourthWgThree x * x ^ 2 + cliffordFourthWgFour x * x := by
  simp [qubitFourthAssociationWeightedSum, qubitFourthAssociationNumber,
    qubitFourthAssociationTable, qubitFourthNOne, qubitFourthWgCoefficient,
    List.finRange]
  ring

theorem qubitFourthAssociationWeightedSum_two (x : ℝ) :
    qubitFourthAssociationWeightedSum 2 x =
      4 * cliffordFourthWgOne x * x + 4 * cliffordFourthWgOne x * x ^ 3 +
      13 * cliffordFourthWgTwo x * x ^ 2 + cliffordFourthWgTwo x * x ^ 4 +
      4 * cliffordFourthWgThree x * x + 3 * cliffordFourthWgThree x * x ^ 3 +
      cliffordFourthWgFour x * x ^ 2 := by
  simp [qubitFourthAssociationWeightedSum, qubitFourthAssociationNumber,
    qubitFourthAssociationTable, qubitFourthNTwo, qubitFourthWgCoefficient,
    List.finRange]
  ring

theorem qubitFourthAssociationWeightedSum_three (x : ℝ) :
    qubitFourthAssociationWeightedSum 3 x =
      8 * cliffordFourthWgOne x * x ^ 2 + 8 * cliffordFourthWgTwo x * x +
      6 * cliffordFourthWgTwo x * x ^ 3 + 6 * cliffordFourthWgThree x * x ^ 2 +
      cliffordFourthWgThree x * x ^ 4 + cliffordFourthWgFour x * x ^ 3 := by
  simp [qubitFourthAssociationWeightedSum, qubitFourthAssociationNumber,
    qubitFourthAssociationTable, qubitFourthNThree, qubitFourthWgCoefficient,
    List.finRange]
  ring

theorem qubitFourthAssociationWeightedSum_four (x : ℝ) :
    qubitFourthAssociationWeightedSum 4 x =
      8 * cliffordFourthWgOne x * x + 14 * cliffordFourthWgTwo x * x ^ 2 +
      7 * cliffordFourthWgThree x * x ^ 3 + cliffordFourthWgFour x * x ^ 4 := by
  simp [qubitFourthAssociationWeightedSum, qubitFourthAssociationNumber,
    qubitFourthAssociationTable, qubitFourthNFour, qubitFourthWgCoefficient,
    List.finRange]
  ring

/-- The certified association tables and the scalar coefficients together
give all four rows of `W_x G_x = I`. -/
theorem qubitFourthAssociationWg_inverse {x : ℝ} (hx : 4 < x) :
    qubitFourthAssociationWeightedSum 1 x = 0 ∧
    qubitFourthAssociationWeightedSum 2 x = 0 ∧
    qubitFourthAssociationWeightedSum 3 x = 0 ∧
    qubitFourthAssociationWeightedSum 4 x = 1 := by
  constructor
  · rw [qubitFourthAssociationWeightedSum_one]
    exact cliffordFourthWg_inverse_class_one hx
  constructor
  · rw [qubitFourthAssociationWeightedSum_two]
    exact cliffordFourthWg_inverse_class_two hx
  constructor
  · rw [qubitFourthAssociationWeightedSum_three]
    exact cliffordFourthWg_inverse_class_three hx
  · rw [qubitFourthAssociationWeightedSum_four]
    exact cliffordFourthWg_inverse_class_four hx

end

end TomographyOracleCore
