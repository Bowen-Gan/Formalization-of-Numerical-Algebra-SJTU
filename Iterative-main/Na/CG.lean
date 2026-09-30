import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option quotPrecheck false

open Matrix

noncomputable section Norm

#check Matrix.frobeniusSeminormedAddCommGroup
abbrev FNorm {α m n} [Fintype m] [Fintype n] [SeminormedAddCommGroup α] : Matrix m n α → ℝ :=
  fun X => (Matrix.frobeniusSeminormedAddCommGroup).norm X

abbrev LinftyNorm {α m n} [Fintype m] [Fintype n] [SeminormedAddCommGroup α] : Matrix m n α → ℝ :=
  fun X => (Matrix.linftyOpSeminormedAddCommGroup).norm X

abbrev LoneNorm {α m n} [Fintype m] [Fintype n] [SeminormedAddCommGroup α] : Matrix m n α → ℝ :=
  fun X => (Matrix.linftyOpSeminormedAddCommGroup).norm Xᵀ

abbrev LtwoNorm {α m n} [Fintype m] [Fintype n] [DecidableEq m] [RCLike α] : Matrix m n α → ℝ :=
  fun X => (Matrix.instL2OpNormedAddCommGroup).norm Xᵀ

notation:100 "‖" A "‖_F" => FNorm A
notation:100 "‖" A "‖_∞" => LinftyNorm A
notation:100 "‖" A "‖₁" => LoneNorm A
notation:100 "‖" A "‖₂" => LtwoNorm A

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

def Matrix.lowerPart {n α : Type*} [Fintype n] [LE n] [DecidableLE n] (X : Matrix n n α) [Ring α]:
  Matrix n n α := fun i j => if j ≥ i then 0 else X i j

def Matrix.upperPart {n α : Type*} [Fintype n] [LE n] [DecidableLE n] (X : Matrix n n α) [Ring α]:
  Matrix n n α := fun i j => if j ≤ i then 0 else X i j

lemma Matrix.transpose_lowerPart_eq_upperPart
    {n α : Type*} [Fintype n] [LE n] [DecidableLE n] (X : Matrix n n α) [Ring α]:
    (Matrix.lowerPart X)ᵀ = Matrix.upperPart X :=
  sorry

def Matrix.diagPart {n α : Type*} [Fintype n] [LE n] [DecidableEq n] (X : Matrix n n α) [Ring α]:
  Matrix n n α := fun i j => if j = i then X i j else 0

lemma Matrix.diagPart_isDiag {n α : Type*} [Fintype n] [LE n] [DecidableEq n] (X : Matrix n n α) [Ring α] :
    (X.diagPart).IsDiag := by
  sorry

lemma Matrix.part_decompose {n α : Type*}
    [Fintype n] [LE n] [DecidableLE n] [DecidableEq n] (X : Matrix n n α) [Ring α]:
    X = Matrix.lowerPart X + Matrix.upperPart X + Matrix.diagPart X :=
  sorry

#check Invertible
theorem Matrix.diagnonzero_diagInvertable
    {n : Type*} [Fintype n] [LE n] [DecidableEq n] (X : Matrix n n ℝ)
    (h : ∀ i, X i i ≠ 0) : IsUnit (Matrix.diagPart X) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  apply Matrix.isUnit_det_of_right_inverse
  let X1 : Matrix n n ℝ := fun i j ↦ if i = j then 1 / X i i else 0
  show X.diagPart * X1 = 1
  sorry

theorem Matrix.diagnonzero_diagInvertable'
    {n : Type*} [Fintype n] [LE n] [DecidableEq n] (A : {X : Matrix n n ℝ // ∀ i, X i i ≠ 0}) :
    IsUnit (Matrix.diagPart A.1) :=
  Matrix.diagnonzero_diagInvertable A.1 A.2

end matrix_structure

section iterative_method

def linearsystem.residual {n : Type*} [Fintype n] (A : Matrix n n ℝ) (b : n → ℝ) :
  (n → ℝ) → (n → ℝ) := fun x ↦ b - (A *ᵥ x)

structure Stationary_iterative {n : Type*} [Fintype n] (x0 : n → ℝ) where
  M : Matrix n n ℝ
  g : n → ℝ

def Stationary_iterative.x {n : Type*} [Fintype n] {x0 : n → ℝ} (self : Stationary_iterative x0) :
    ℕ → (n → ℝ)
  | 0 => x0
  | p + 1 => self.M *ᵥ (self.x p) + self.g

lemma Stationary_iterative.x_zero {n : Type*} [Fintype n] {x0 : n → ℝ}
    (self : Stationary_iterative x0) : self.x 0 = x0 := rfl

lemma Stationary_iterative.x_succ {n : Type*} [Fintype n] {x0 : n → ℝ}
    (self : Stationary_iterative x0) (p : ℕ) : self.x (p + 1) = self.M *ᵥ (self.x p) + self.g := rfl

noncomputable def Jacobi {n : Type*} [Fintype n] [LE n] [DecidableEq n] (A : {X : Matrix n n ℝ // ∀ i, X i i ≠ 0})
    (b : n → ℝ) (x0 : n → ℝ) : Stationary_iterative x0 :=
  letI : Invertible ((A.1).diagPart) := (Matrix.diagnonzero_diagInvertable' A).invertible
  {
    M := ((A.1).diagPart)⁻¹ * ((A.1).diagPart - A.1)
    g := ((A.1).diagPart)⁻¹ *ᵥ b
  }

variable {n} [Fintype n] [LE n] [DecidableEq n] {A : {X : Matrix n n ℝ // ∀ i, X i i ≠ 0}}
  {b : n → ℝ} {x0 : n → ℝ}

lemma Jacobi.update (alg := Jacobi A b x0) (p : ℕ) :
    alg.x (p + 1) = alg.M *ᵥ alg.x p + alg.g := rfl

end iterative_method

noncomputable section steepest_descent

def steepest_descent.stepsize {n : Type*} [Fintype n] (A : Matrix n n ℝ) :
  (n → ℝ) → ℝ :=
  fun r ↦ if r = 0 then 0 else (r ⬝ᵥ r) / (r ⬝ᵥ (A *ᵥ r))

def steepest_descent.info {n : Type*} [Fintype n] (A : Matrix n n ℝ) (x0 b : n → ℝ)  :
    ℕ → ((n → ℝ) × (n → ℝ) × ℝ)
  | 0 => (x0, b - A *ᵥ x0, steepest_descent.stepsize A (b - A *ᵥ x0))
  | p + 1 =>
    let (x, r, s) := steepest_descent.info A x0 b p
    (x + s • r, linearsystem.residual A b (x + s • r),
      steepest_descent.stepsize A (linearsystem.residual A b (x + s • r)))

def steepest_descent.x {n : Type*} [Fintype n] (A : Matrix n n ℝ) (x0 b : n → ℝ)  :
    ℕ → (n → ℝ) := fun k ↦ (steepest_descent.info A x0 b k).1

def steepest_descent.r {n : Type*} [Fintype n] (A : Matrix n n ℝ) (x0 b : n → ℝ)  :
    ℕ → (n → ℝ) := fun k ↦ (steepest_descent.info A x0 b k).2.1

def steepest_descent.α {n : Type*} [Fintype n] (A : Matrix n n ℝ) (x0 b : n → ℝ)  :
    ℕ → ℝ := fun k ↦ (steepest_descent.info A x0 b k).2.2

end steepest_descent

noncomputable section conjugate_gradient

def conjugate_gradient.stepsize {n : Type*} [Fintype n] (A : Matrix n n ℝ) :
  (n → ℝ) → (n → ℝ) → ℝ :=
  fun r p ↦ if r = 0 ∨ p = 0 then 0 else (r ⬝ᵥ r) / (p ⬝ᵥ (A *ᵥ p))

def conjugate_gradient.info {n : Type*} [Fintype n] (A : Matrix n n ℝ) (x0 b : n → ℝ)  :
    ℕ → ((n → ℝ) × (n → ℝ) × (n → ℝ) × ℝ × ℝ)
  | 0 =>
    let r0 := linearsystem.residual A b x0
    (x0, r0, r0, conjugate_gradient.stepsize A r0 r0, 0)
  | 1 =>
      let (x0, r0, p0, α0, _) := conjugate_gradient.info A x0 b 0
      let r1 := r0 - α0 • (A *ᵥ p0)
      let β1 := (r1 ⬝ᵥ r1) / (r0 ⬝ᵥ r0)
      (x0 + α0 • p0, r1, r1 + β1 • p0, conjugate_gradient.stepsize A r1 (r1 + β1 • p0), β1)
  | p + 2 =>
      let (_, r0, _, _, _) := conjugate_gradient.info A x0 b p
      let (x1, r1, p1, α1, _) := conjugate_gradient.info A x0 b (p + 1)
      let r2 := r1 - α1 • (A *ᵥ p1)
      let β2 := (r1 ⬝ᵥ r1) / (r0 ⬝ᵥ r0)
      (x1 + α1 • p1, r2, r2 + β2 • p1, conjugate_gradient.stepsize A r2 (r2 + β2 • p1), β2)

def conjugate_gradient.x {n : Type*} [Fintype n] (A : Matrix n n ℝ) (x0 b : n → ℝ)  :
    ℕ → (n → ℝ) := fun k ↦ (conjugate_gradient.info A x0 b k).1

def conjugate_gradient.r {n : Type*} [Fintype n] (A : Matrix n n ℝ) (x0 b : n → ℝ)  :
    ℕ → (n → ℝ) := fun k ↦ (conjugate_gradient.info A x0 b k).2.1

def conjugate_gradient.p {n : Type*} [Fintype n] (A : Matrix n n ℝ) (x0 b : n → ℝ)  :
    ℕ → (n → ℝ) := fun k ↦ (conjugate_gradient.info A x0 b k).2.2.1

def conjugate_gradient.α {n : Type*} [Fintype n] (A : Matrix n n ℝ) (x0 b : n → ℝ)  :
    ℕ → ℝ := fun k ↦ (conjugate_gradient.info A x0 b k).2.2.2.1

def conjugate_gradient.β {n : Type*} [Fintype n] (A : Matrix n n ℝ) (x0 b : n → ℝ)  :
    ℕ → ℝ := fun k ↦ (conjugate_gradient.info A x0 b k).2.2.2.2


end conjugate_gradient
