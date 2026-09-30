import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix Set

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

def Matrix.conditionNumber' {n : Type*} [Fintype n] [DecidableEq n]
    (A : GL n ℝ) : ℝ :=
  ‖A.1‖₂ * ‖A.2‖₂

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
    {n α : Type*} [Fintype n] [DecidableEq n] [Field α] {A : Matrix n n α}
    (hA : ∀ i, A i i ≠ 0) : IsUnit (Matrix.diagPart A) := by
  simpa [Matrix.isUnit_diagonal, Pi.isUnit_iff] using hA

theorem Matrix.diagnonzero_diagInvertable'
    {n α : Type*} [Fintype n] [DecidableEq n] [Field α]
    (A : {X : Matrix n n α // ∀ i, X i i ≠ 0}) : IsUnit (Matrix.diagPart A.1) :=
  (A.1).diagnonzero_diagInvertable A.2

end matrix_structure

section iterative_method

def linearsystem.residual {α : Type*} {n : ℕ} [Field α] (A : Matrix (Fin n) (Fin n) α) (b : (Fin n) → α) :
  (Fin n → α) → (Fin n → α) := fun x ↦ b - (A *ᵥ x)

structure Stationary_iterative {α : Type*} {n : ℕ} [Field α] (x0 : (Fin n) → α) where
  M : Matrix (Fin n) (Fin n) α
  g : (Fin n) → α

def Stationary_iterative.x {α : Type*} {n : ℕ} [Field α] {x0 : (Fin n) → α} (self : Stationary_iterative x0) :
    ℕ → ((Fin n) → α)
  | 0 => x0
  | p + 1 => self.M *ᵥ (self.x p) + self.g

lemma Stationary_iterative.x_zero {α : Type*} {n : ℕ} [Field α] {x0 : (Fin n) → α}
    (self : Stationary_iterative x0) : self.x 0 = x0 := rfl

lemma Stationary_iterative.x_succ {α : Type*} {n : ℕ} [Field α] {x0 : (Fin n) → α}
    (self : Stationary_iterative x0) (p : ℕ) : self.x (p + 1) = self.M *ᵥ (self.x p) + self.g := rfl

noncomputable def Jacobi {α : Type*} {n : ℕ} [Field α] (A : Matrix (Fin n) (Fin n) α) (hA : ∀ i, A i i ≠ 0)
    (b : (Fin n) → α) (x0 : (Fin n) → α) : Stationary_iterative x0 :=
  letI Dinv : Matrix (Fin n) (Fin n) α := (A.diagnonzero_diagInvertable hA).unit.inv
  {
    M := Dinv * (A.diagPart - A)
    g := Dinv *ᵥ b
  }

variable {α : Type*} {n : ℕ} [Field α] {x0 : (Fin n) → α} (A : Matrix (Fin n) (Fin n) α) (hA : ∀ i, A i i ≠ 0)
  {b : (Fin n) → α} {x0 : (Fin n) → α}

lemma Jacobi.update (alg := Jacobi A hA b x0) (p : ℕ) :
    alg.x (p + 1) = alg.M *ᵥ alg.x p + alg.g := rfl

end iterative_method

section quad_func

def quad_func (A : Matrix (Fin n) (Fin n) ℝ) (b : (Fin n) → ℝ) :
  (Fin n → ℝ) → ℝ := fun x => x ⬝ᵥ (A *ᵥ x) - 2 * (b ⬝ᵥ x)
variable (A : Matrix (Fin n) (Fin n) ℝ) (b : (Fin n) → ℝ)
local notation "φ" => quad_func A b


lemma inner_x_Ay_eq_inner_y_Ax (hA : A.IsSymm) (x y : (Fin n) → ℝ) : x ⬝ᵥ A *ᵥ y = y ⬝ᵥ A *ᵥ x := by
  have : x ⬝ᵥ A *ᵥ y = x ⬝ᵥ (star (A *ᵥ y)) := by simp
  rw [this, Matrix.star_mulVec]
  have : star y ᵥ* Aᴴ = star (y ᵥ* A) := by
    simp; rw [hA]
  rw [this, Matrix.dotProduct_star]; simp
  exact Eq.symm (dotProduct_mulVec y A x)


lemma dotProduct_nonneg (x :  (Fin n) → ℝ) : x ⬝ᵥ x ≥ 0 := by
    simp [dotProduct]
    refine Fintype.sum_nonneg ?_
    intro j
    simp
    exact mul_self_nonneg (x j)


theorem lin_sys_sol_eq_quad_func_min_1 (hA: A.PosDef) (x : (Fin n) → ℝ) :
  IsMinOn φ univ x → A *ᵥ x = b := by
    intro hmin
    have hy: ∃ y : Fin n → ℝ, A *ᵥ y = b := by
      let y := A⁻¹ *ᵥ b
      use y
      have := Matrix.PosDef.isUnit hA
      simp [y]
      have : A * A⁻¹ = 1 := by
        refine mul_nonsing_inv A ?_
        exact (isUnit_iff_isUnit_det A).mp this
      rw [this]
      simp
    rcases hy with ⟨y, hy⟩
    have h2 : φ x ≤ φ y := by
      apply hmin
      trivial
    have hkey2: φ x - φ y = (x - y) ⬝ᵥ (A *ᵥ (x - y)) := by
      unfold quad_func; simp
      rw [A.mulVec_sub, hy, dotProduct_comm y b]
      rw [dotProduct_sub, dotProduct_sub]
      rw [dotProduct_comm y b, dotProduct_comm x b]
      have hc : x ⬝ᵥ A *ᵥ y = y ⬝ᵥ A *ᵥ x := by
        have Asymm : A = Aᵀ := Eq.symm (IsSymm.eq hA.1)
        have : x ⬝ᵥ A *ᵥ y = x ⬝ᵥ (star (A *ᵥ y)) := by simp
        rw [this, Matrix.star_mulVec]
        have : star y ᵥ* Aᴴ = star (y ᵥ* A) := by simp; rw [← Asymm]
        rw [this, Matrix.dotProduct_star]; simp
        exact Eq.symm (dotProduct_mulVec y A x)
      rw [← hc, hy, dotProduct_comm x b]; ring_nf
    have hkey3 : 0 ≤ (x - y) ⬝ᵥ (A *ᵥ (x - y)) := by
      by_cases h : x - y = 0
      · rw [h]; simp
      obtain hA2 := hA.2 (x - y) h
      simp only [star_trivial] at hA2
      linarith
    have h1 : φ y ≤ φ x := by rwa [← sub_nonneg, hkey2]
    have h5 : φ y = φ x := by linarith
    have hzero : (x - y) ⬝ᵥ (A *ᵥ (x - y)) = 0 := by linarith [hkey2, h5]
    rw [← sub_eq_zero]
    by_cases hxy : x = y
    rw [← hxy] at hy
    exact sub_eq_zero_of_eq hy
    let v := x - y
    by_contra! hne
    have hpos : 0 < v ⬝ᵥ (A *ᵥ v) := by
      apply hA.2 v
      push_neg at hxy
      exact sub_ne_zero_of_ne hxy
    linarith


-- 定理5.1.1(a)：线性方程组的解推出于二次函数的最小值点
theorem lin_sys_sol_eq_quad_func_min_2 (hA : A.PosDef) (x : (Fin n) → ℝ)
    (hB: A *ᵥ x = b) : IsMinOn φ univ x:= by
    intro y; simp
    have key : φ y - φ x = (y - x) ⬝ᵥ (A *ᵥ (y - x)) := by
      unfold quad_func; simp
      rw [A.mulVec_sub, hB, dotProduct_comm x b, dotProduct_sub, dotProduct_sub]
      rw [dotProduct_comm x b, dotProduct_comm y b]
      have : x ⬝ᵥ A *ᵥ y = y ⬝ᵥ A *ᵥ x := by
        obtain hA1 := hA.1
        have Asymm : A = Aᵀ := Eq.symm (IsSymm.eq hA1)
        have : x ⬝ᵥ A *ᵥ y = x ⬝ᵥ (star (A *ᵥ y)) := by simp
        rw [this, Matrix.star_mulVec]
        have : star y ᵥ* Aᴴ = star (y ᵥ* A) := by
          simp; rw [← Asymm]
        rw [this, Matrix.dotProduct_star]
        exact Eq.symm (dotProduct_mulVec y A x)
      rw [this, hB, dotProduct_comm y b]; ring
    have h3 : 0 ≤ (y - x) ⬝ᵥ (A *ᵥ (y - x)) := by
      by_cases h : y - x = 0
      · simp [h]
      obtain hA2 := hA.2 (y - x) h
      simp only [star_trivial] at hA2
      linarith
    linarith

-- thm 5.1.1
theorem lin_sys_sol_eq_quad_func_min (hA: A.PosDef) (x : (Fin n) → ℝ) :
  A *ᵥ x = b ↔ IsMinOn φ univ x :=
  ⟨fun h => lin_sys_sol_eq_quad_func_min_2 A b hA x h,
   fun h => lin_sys_sol_eq_quad_func_min_1 A b hA x h⟩

end quad_func
