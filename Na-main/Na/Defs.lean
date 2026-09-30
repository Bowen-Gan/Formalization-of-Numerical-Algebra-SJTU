import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix

noncomputable section Norm

/-- the `ℝ`-valued Frobenius norm. -/
abbrev FNorm {α m n} [Fintype m] [Fintype n] [SeminormedAddCommGroup α] : Matrix m n α → ℝ :=
  fun X => (Matrix.frobeniusSeminormedAddCommGroup).norm X

/-- the `ℝ`-valued `L^∞` operator norm. -/
abbrev LinftyNorm {α m n} [Fintype m] [Fintype n] [SeminormedAddCommGroup α] : Matrix m n α → ℝ :=
  fun X => (Matrix.linftyOpSeminormedAddCommGroup).norm X

/-- the `ℝ`-valued `L¹` operator norm. -/
abbrev LoneNorm {α m n} [Fintype m] [Fintype n] [SeminormedAddCommGroup α] : Matrix m n α → ℝ :=
  fun X => (Matrix.linftyOpSeminormedAddCommGroup).norm Xᵀ

/-- the `ℝ`-valued `L²` operator norm. --/
abbrev LtwoNorm {α m n} [Fintype m] [Fintype n] [DecidableEq m] [RCLike α] : Matrix m n α → ℝ :=
  fun X => (Matrix.instL2OpNormedAddCommGroup).norm Xᵀ

@[inherit_doc] notation:100 "‖" A "‖_F" => FNorm A
@[inherit_doc] notation:100 "‖" A "‖_∞" => LinftyNorm A
@[inherit_doc] notation:100 "‖" A "‖₁" => LoneNorm A
@[inherit_doc] notation:100 "‖" A "‖₂" => LtwoNorm A

def Norm_ofPosDef {n : Type*} [Fintype n] (A : {X : Matrix n n ℝ // Matrix.PosDef X}) : (n → ℝ) → ℝ :=
  fun x ↦ Real.sqrt (x ⬝ᵥ (A *ᵥ x))

instance Norm_ofPosDef.toNorm {n : Type*} [Fintype n] (A : {X : Matrix n n ℝ // Matrix.PosDef X}) :
    Norm (n → ℝ) where
  norm := Norm_ofPosDef A

variable {m n R α} [Fintype m] [Fintype n] [NormedField R] [SeminormedAddCommGroup α] [NormedSpace R α]
  {X : Matrix m n R}

#check ‖X‖_F
#check ‖X‖₁
#check ‖X‖_∞

variable {m' n' : Type*} [Fintype m'] [Fintype n'] [DecidableEq m'] [DecidableEq n'] {X : Matrix m' n' ℝ}
#check ‖X‖₂

end Norm

noncomputable section Condition_Number

def Matrix.conditionNumber {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) [Invertible A] : ℝ :=
  ‖A‖₂ * ‖A⁻¹‖₂

end Condition_Number

section matrix_structure

def Matrix.lowerPart {n α : Type*} [LE n] [DecidableLE n] (X : Matrix n n α) [Zero α] :
  Matrix n n α := fun i j => if j ≥ i then 0 else X i j

def Matrix.upperPart {n α : Type*} [LE n] [DecidableLE n] (X : Matrix n n α) [Zero α] :
  Matrix n n α := fun i j => if j ≤ i then 0 else X i j

lemma Matrix.transpose_lowerPart_eq_upperPart
    {n α : Type*} [LE n] [DecidableLE n] (X : Matrix n n α) [Zero α] :
    (Matrix.lowerPart X)ᵀ = Matrix.upperPart Xᵀ := by
  ext i j
  simp [lowerPart, upperPart]

abbrev Matrix.diagPart {n α : Type*} [DecidableEq n] (X : Matrix n n α) [Zero α] :=
  Matrix.diagonal (fun i => X i i)

lemma Matrix.part_decompose {n α : Type*} [LinearOrder n] (X : Matrix n n α) [AddZeroClass α] :
    X = Matrix.lowerPart X + Matrix.upperPart X + Matrix.diagPart X := by
  ext i j
  simp only [diagonal, add_apply, lowerPart, ge_iff_le, upperPart, of_apply]
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  on_goal 2 => exact absurd (le_antisymm h1 h2) h3
  on_goal 7 => exact absurd (not_le.mp h1).le h5
  all_goals simp_all

theorem Matrix.diagnonzero_diagInvertable
    {n α : Type*} [Fintype n] [DecidableEq n] [Field α] (A : Matrix n n α)
    (hA : ∀ i, A i i ≠ 0) : IsUnit (Matrix.diagPart A) := by
  simpa [Matrix.isUnit_diagonal, Pi.isUnit_iff] using hA

theorem Matrix.diagnonzero_diagInvertable'
    {n α : Type*} [Fintype n] [DecidableEq n] [Field α]
    (A : {X : Matrix n n α // ∀ i, X i i ≠ 0}) : IsUnit (Matrix.diagPart A.1) :=
  (A.1).diagnonzero_diagInvertable A.2

end matrix_structure

section iterative_method

def linearsystem.residual {n : ℕ} {α : Type*} [Field α] (A : Matrix (Fin n) (Fin n) α) (b : (Fin n) → α) :
  (Fin n → α) → (Fin n → α) := fun x ↦ b - (A *ᵥ x)

structure Stationary_iterative {n : ℕ} {α : Type*} [Field α] (x0 : (Fin n) → α) where
  M : Matrix (Fin n) (Fin n) α
  g : (Fin n) → α

def Stationary_iterative.x {n : ℕ} {α : Type*} [Field α] {x0 : (Fin n) → α} (self : Stationary_iterative x0) :
    ℕ → ((Fin n) → α)
  | 0 => x0
  | p + 1 => self.M *ᵥ (self.x p) + self.g

lemma Stationary_iterative.x_zero {n : ℕ} {α : Type*} [Field α] {x0 : (Fin n) → α}
    (self : Stationary_iterative x0) : self.x 0 = x0 := rfl

lemma Stationary_iterative.x_succ {n : ℕ} {α : Type*} [Field α] {x0 : (Fin n) → α}
    (self : Stationary_iterative x0) (p : ℕ) : self.x (p + 1) = self.M *ᵥ (self.x p) + self.g := rfl

noncomputable def Jacobi {n : ℕ} {α : Type*} [Field α] (A : Matrix (Fin n) (Fin n) α) (hA : ∀ i, A i i ≠ 0)
    (b : (Fin n) → α) (x0 : (Fin n) → α) : Stationary_iterative x0 :=
  letI Dinv : Matrix (Fin n) (Fin n) α := (A.diagnonzero_diagInvertable hA).unit.inv
  {
    M := Dinv * (A.diagPart - A)
    g := Dinv *ᵥ b
  }

variable {n : ℕ} {α : Type*} [Field α]

lemma Jacobi.update (b : (Fin n) → α) (x0 : (Fin n) → α)
    (A : Matrix (Fin n) (Fin n) α) (hA : ∀ i, A i i ≠ 0) (p : ℕ) :
    (Jacobi A hA b x0).x (p + 1) =
    (Jacobi A hA b x0).M *ᵥ (Jacobi A hA b x0).x p + (Jacobi A hA b x0).g := rfl

end iterative_method

section gauss_iterative_method

open Matrix Finset Filter Topology spectrum

variable {α : Type*} {n : ℕ} [NormedField α]

lemma lemma_le_0_1 (M : Matrix (Fin n) (Fin n) α) (hM : ∀ i, M i i ≠ 0) :
    ∏ i, M i i ≠ 0
    := by
  rw [@prod_ne_zero_iff]
  intro a ha
  exact hM a

lemma lemma_eq_2_1 (A : Matrix (Fin n) (Fin n) α) (hA : ∀ i, A i i ≠ 0) :
    ∀ i, IsUnit ((A.diagPart + A.lowerPart) i i) := by
  intro i
  simp [lowerPart]
  exact hA i

lemma lemma_3_1 (A : Matrix (Fin n) (Fin n) α) (hA : ∀ i, A i i ≠ 0) : IsUnit (A.diagPart + A.lowerPart).det := by
  have h_diag : ∀ i, IsUnit ((A.diagPart + A.lowerPart) i i) := by
    exact lemma_eq_2_1 A hA
  have hd : A.diagPart.BlockTriangular ⇑OrderDual.toDual := by
    simp [diagPart]
    exact blockTriangular_diagonal fun i ↦ A i i
  have hl : A.lowerPart.BlockTriangular ⇑OrderDual.toDual := by
    unfold lowerPart
    unfold BlockTriangular
    simp
    intro i j hij hji
    absurd hij
    simpa using hji.le
  have h : (A.diagPart + A.lowerPart).BlockTriangular ⇑OrderDual.toDual := by
    exact BlockTriangular.add hd hl
  have det_eq : (A.diagPart + A.lowerPart).det = ∏ i : (Fin n), (A.diagPart + A.lowerPart) i i := det_of_lowerTriangular (A.diagPart + A.lowerPart) h
  have det_unit : IsUnit (A.diagPart + A.lowerPart).det := by
    rw [det_eq]
    simp [- add_apply]
    push_neg
    simp [- add_apply] at h_diag
    push_neg at h_diag
    exact lemma_le_0_1 (A.diagPart + A.lowerPart) h_diag
  exact det_unit

theorem Matrix.diagnonzero_diag_minus_lowerPart_Invertable
    (A : Matrix (Fin n) (Fin n) α)
    (hA : ∀ i, A i i ≠ 0) :
    let D := A.diagPart
    let L := -A.lowerPart
    -- let U := -A.upperPart
    IsUnit (D - L) := by
  intro D L
  simp [D, L]
  have det_unit : IsUnit (A.diagPart + A.lowerPart).det := by
    exact lemma_3_1 A hA
  exact (isUnit_iff_isUnit_det (A.diagPart + A.lowerPart)).mpr det_unit

noncomputable def GaussSeidel (A : Matrix (Fin n) (Fin n) α) (hA : ∀ i, (A i i) ≠ 0)
    (b : (Fin n) → α) (x0 : (Fin n) → α) : Stationary_iterative x0 :=
  letI D_add_L_inv : Matrix (Fin n) (Fin n) α := (A.diagnonzero_diag_minus_lowerPart_Invertable hA).unit.inv
  {
    M := D_add_L_inv * (-A.upperPart)
    g := D_add_L_inv *ᵥ b
  }

variable {x0 : (Fin n) → α} {A : Matrix (Fin n) (Fin n) α} {hA : ∀ i, (A i i) ≠ 0} {b : (Fin n) → α} {x0 : (Fin n) → α}

lemma GaussSeidel.update (alg := GaussSeidel A hA b x0) (p : ℕ) :
    alg.x (p + 1) = alg.M *ᵥ alg.x p + alg.g := rfl

end gauss_iterative_method
