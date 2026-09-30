import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib

open Matrix
open scoped ENNReal

noncomputable section Norm
-----定义各种范数
#check Matrix.frobeniusSeminormedAddCommGroup
abbrev FNorm {α m n} [Fintype m] [Fintype n] [SeminormedAddCommGroup α] : Matrix m n α → ℝ :=
  fun X => (Matrix.frobeniusSeminormedAddCommGroup).norm X
#check linfty_opNorm_def

abbrev LinftyNorm {α m n} [Fintype m] [Fintype n] [SeminormedAddCommGroup α] : Matrix m n α → ℝ :=
  fun X => (Matrix.linftyOpSeminormedAddCommGroup).norm X


abbrev LoneNorm {α m n} [Fintype m] [Fintype n] [SeminormedAddCommGroup α] : Matrix m n α → ℝ :=
  fun X => (Matrix.linftyOpSeminormedAddCommGroup).norm Xᵀ

abbrev LtwoNorm {α m n} [Fintype m] [Fintype n] [DecidableEq m] [RCLike α] : Matrix m n α → ℝ :=
  fun X => (Matrix.instL2OpNormedAddCommGroup).norm Xᵀ



/-- 向量 ℓ∞ 范数：max_i |x i| -/
noncomputable def vecInftyNorm {ι : Type*} [Fintype ι][Nonempty ι] (x : ι → ℝ) : ℝ :=
  norm x
-----通过sorry占位，然后不断unfold找到定义
example {ι : Type*} [Fintype ι][Nonempty ι] (x : ι → ℝ) :
    (norm x : ℝ) = sorry := by
  unfold norm
  unfold NormedRing.toNorm
  unfold Pi.normedRing
  -- simp
  unfold SeminormedRing.toNorm
  unfold Pi.seminormedRing
  -- simp
  unfold NonUnitalSeminormedRing.toNorm
  unfold  Pi.nonUnitalSeminormedRing
  -- simp
  sorry


-- instance Pi.seminormedGroup : SeminormedGroup (∀ i, G i) where
--   norm f := ↑(Finset.univ.sup fun b => ‖f b‖₊)
--   dist_eq x y :=
--     congr_arg (toReal : ℝ≥0 → ℝ) <|
--       congr_arg (Finset.sup Finset.univ) <|
--         funext fun a => show nndist (x a) (y a) = ‖x a / y a‖₊ from nndist_eq_nnnorm_div (x a) (y a)

notation:100 "‖" x "‖_vec∞" => vecInftyNorm x
notation:100 "‖" A "‖_F" => FNorm A
notation:100 "‖" A "‖_∞" => LinftyNorm A
notation:100 "‖" A "‖₁" => LoneNorm A
notation:100 "‖" A "‖₂" => LtwoNorm A
------正定矩阵范数
def Norm_ofPosDef {n : Type*} [Fintype n] (A : {X : Matrix n n ℝ // Matrix.PosDef X}) : (n → ℝ) → ℝ :=
  fun x ↦ Real.sqrt (x ⬝ᵥ (A *ᵥ x))

#check PosDef


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

def Matrix.lowerPart {n α : Type*} [Fintype n] [LE n] [DecidableLE n] (X : Matrix n n α) [Zero α] :
  Matrix n n α := fun i j => if j ≥ i then 0 else X i j

def Matrix.upperPart {n α : Type*} [Fintype n] [LE n] [DecidableLE n] (X : Matrix n n α) [Zero α] :
  Matrix n n α := fun i j => if j ≤ i then 0 else X i j

lemma Matrix.transpose_lowerPart_eq_upperPart
    {α : Type*} {n : ℕ} (X : Matrix (Fin n) (Fin n) α) [Zero α] :
    (Matrix.lowerPart X)ᵀ = Matrix.upperPart Xᵀ := by
  ext i j
  simp [lowerPart, upperPart, transpose]

def Matrix.diagPart {n α : Type*} [Fintype n] [LE n] [DecidableEq n] (X : Matrix n n α) [Zero α]:
  Matrix n n α := fun i j => if j = i then X i j else 0

lemma Matrix.diagPart_isDiag {α : Type*} {n : ℕ} (X : Matrix (Fin n) (Fin n) α) [Zero α]:
    (X.diagPart).IsDiag := by
  unfold IsDiag; simp [diagPart]
  intro i j hij
  exact fun a => False.elim (hij (id (Eq.symm a)))


lemma Matrix.part_decompose {α : Type*} {n : ℕ} (X : Matrix (Fin n) (Fin n) α) [Zero α] [Add α]:
    X = Matrix.lowerPart X + Matrix.upperPart X + Matrix.diagPart X := by
  ext i j
  simp [lowerPart, upperPart, diagPart]
  rcases lt_trichotomy i j with h | h | h
  have h₁₁ : ¬ j ≤ i := by exact not_le_of_lt h
  have h₁₂ : ¬ j = i := by exact Fin.ne_of_gt h
  have h₁₃ : i ≤ j := by exact le_of_lt h
  simp[h₁₁,h₁₂,h₁₃]
  repeat sorry

#check Invertible
theorem Matrix.diagnonzero_diagInvertable
    {α : Type*} {n : ℕ} (X : Matrix (Fin n) (Fin n) α) [Field α]
    (h : ∀ i, X i i ≠ 0) : IsUnit (Matrix.diagPart X) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  apply Matrix.isUnit_det_of_right_inverse
  -- 构造右逆，元素类型统一为 α
  let X1 : Matrix (Fin n) (Fin n) α := fun i j =>
    if i = j then (X i i)⁻¹ else 0
  show X.diagPart * X1 = 1
  ext i j
  simp [diagPart, X1, mul_apply, Finset.sum_ite_eq, h]
  <;> split_ifs  <;> try aesop
  simp [Matrix.one_apply, h_1]
  have h_ne : i ≠ j := by
    intro h'
    exact h_1 h'.symm
  simp [h_ne]

theorem Matrix.diagnonzero_diagInvertable'
    {α : Type*} {n : ℕ} [Field α] (A : {X : Matrix (Fin n) (Fin n) α // ∀ i, X i i ≠ 0}) :
    IsUnit (Matrix.diagPart A.1) :=
  Matrix.diagnonzero_diagInvertable A.1 A.2

end matrix_structure

section iterative_method
----定义残差
def linearsystem.residual {α : Type*} {n : ℕ} [Field α] (A : Matrix (Fin n) (Fin n) α) (b : (Fin n) → α) :
  (Fin n → α) → (Fin n → α) := fun x ↦ b - (A *ᵥ x)
----定义变换矩阵M和变换向量
structure Stationary_iterative {α : Type*} {n : ℕ} [Field α] (x0 : (Fin n) → α) where
  M : Matrix (Fin n) (Fin n) α
  g : (Fin n) → α
-----定义迭代
def Stationary_iterative.x {α : Type*} {n : ℕ} [Field α] {x0 : (Fin n) → α} (self : Stationary_iterative x0) :
    ℕ → ((Fin n) → α)
  | 0 => x0
  | p + 1 => self.M *ᵥ (self.x p) + self.g

lemma Stationary_iterative.x_zero {α : Type*} {n : ℕ} [Field α] {x0 : (Fin n) → α}
    (self : Stationary_iterative x0) : self.x 0 = x0 := rfl

lemma Stationary_iterative.x_succ {α : Type*} {n : ℕ} [Field α] {x0 : (Fin n) → α}
    (self : Stationary_iterative x0) (p : ℕ) : self.x (p + 1) = self.M *ᵥ (self.x p) + self.g := rfl

noncomputable def Jacobi {α : Type*} {n : ℕ} [Field α] (A : {X : Matrix (Fin n) (Fin n) α // ∀ i, X i i ≠ 0})
    (b : (Fin n) → α) (x0 : (Fin n) → α) : Stationary_iterative x0 :=
  {
    M := ((A.1).diagPart)⁻¹ * ((A.1).diagPart - A.1)
    g := ((A.1).diagPart)⁻¹ *ᵥ b
  }

variable {α : Type*} {n : ℕ} [Field α] {x0 : (Fin n) → α} {A : {X : Matrix (Fin n) (Fin n) α // ∀ i, X i i ≠ 0}}
  {b : (Fin n) → α} {x0 : (Fin n) → α}

lemma Jacobi.update (alg := Jacobi A b x0) (p : ℕ) :
    alg.x (p + 1) = alg.M *ᵥ alg.x p + alg.g := rfl

--------定理4.2.4，首先先定理G——S迭代算法的矩阵

noncomputable def G_S {α : Type*} {n : ℕ} [Field α] (A : {X : Matrix (Fin n) (Fin n) α // ∀ i, X i i ≠ 0})
    (b : (Fin n) → α) (x0 : (Fin n) → α) : Stationary_iterative x0 :=
  {
    M := ((A.1).diagPart+(A.1).lowerPart)⁻¹ * -((A.1).upperPart)
    g := ((A.1).diagPart+(A.1).lowerPart)⁻¹ *ᵥ b
  }

-----G_S迭代
lemma G_S.update (alg := G_S A b x0) (p : ℕ) :
    alg.x (p + 1) = alg.M *ᵥ alg.x p + alg.g := rfl



--------4.2.6增加的一些定义和小lemma

def twoD_minus_A (A : Matrix (Fin n) (Fin n) ℝ) :=
  2 • A.diagPart - A
-----定义D^(1/2),D^(-1/2)
noncomputable def D_sqrt (D : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ if i = j then Real.sqrt (D i i) else 0

noncomputable def D_sqrt_inv (D : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ if i = j then 1 / Real.sqrt (D i i) else 0
------证明D^(1/2),D^(-1/2)是对角阵
lemma D_sqrt_isDiag (D : Matrix (Fin n) (Fin n) ℝ) : (D_sqrt D).IsDiag := by
  unfold D_sqrt
  unfold IsDiag
  intro i j h
  simp [h]

lemma D_sqrt_inv_isDiag (D : Matrix (Fin n) (Fin n) ℝ) : (D_sqrt_inv D).IsDiag := by
  unfold D_sqrt_inv
  unfold IsDiag
  intro i j h
  simp [h]

lemma D_sqrt_diag_nonzero (h : ∀ i, D i i > 0) :
    ∀ i, (D_sqrt D) i i ≠ 0 := by
  intro i
  simp [D_sqrt]
  exact ne_of_gt (Real.sqrt_pos.2 (h i))

/-- 当 D 的对角线全部大于 0 时，D_sqrt_inv 的对角线全部非零 -/
lemma D_sqrt_inv_diag_nonzero (h : ∀ i, D i i > 0) :
    ∀ i, (D_sqrt_inv D) i i ≠ 0 := by
  intro i
  simp [D_sqrt_inv]
  exact Real.sqrt_ne_zero'.mpr (h i)
-- 对角线元素 > 0 得到非 0
lemma diagpos_to_nonzero
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  :
  ∀ i, A i i ≠ 0
  := by
  exact fun i ↦ Ne.symm (ne_of_lt (hdiag i))

noncomputable def myJacobi
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  (b : Fin n → ℝ)
  (x0 : Fin n → ℝ)
  :=
  Jacobi ⟨A, diagpos_to_nonzero A hdiag⟩ b x0

-- 1. (D_sqrt_inv A) * (D_sqrt A) = 1
lemma D_sqrt_inv_mul_self (A : Matrix (Fin n) (Fin n) ℝ) (hdiag : ∀ i, A i i > 0) :
    (D_sqrt_inv A) * (D_sqrt A) = 1 := by
  have h₂₀ :∀ i, √(A i i) ≠ 0 := by
    intro i
    have h_pos : A i i > 0 := hdiag i
    positivity
  ext i j
  simp [D_sqrt_inv, D_sqrt, mul_apply, Finset.sum_ite_eq, Finset.mem_univ, if_pos, if_neg]
  <;> try aesop
  <;> try positivity
  <;> try field_simp [Real.sqrt_pos.mpr (hA i), Real.sq_sqrt (by linarith : (0 : ℝ) ≤ A i i)]
  <;> try aesop

-- theoremradiction isUnit_D_sqrt (A : Matrix (Fin n) (Fin n) ℝ) (hdiag : ∀ i, A i i > 0) :
--     IsUnit (D_sqrt A) :=
--   letI : Invertible (D_sqrt A) :=
--     invertibleOfLeftInverse _ (D_sqrt_inv A) (D_sqrt_inv_mul_self A hdiag)
--   isUnit_of_invertible (D_sqrt A)


theorem isUnit_D_sqrt_inv (A : Matrix (Fin n) (Fin n) ℝ) (hdiag : ∀ i, A i i > 0) :
    IsUnit (D_sqrt_inv A) :=
  letI : Invertible (D_sqrt_inv A) :=
    invertibleOfRightInverse _ (D_sqrt A) (D_sqrt_inv_mul_self A hdiag)
  isUnit_of_invertible (D_sqrt_inv A)

-- 复数化实矩阵
def complexify
  (B : Matrix (Fin n) (Fin n) ℝ)
  :
  Matrix (Fin n) (Fin n) ℂ
  :=
  Matrix.map B (↑)  -- 将每个实数元素通过强制转换嵌入复数

lemma Matrix.eignevalue
  (B : Matrix (Fin n) (Fin n) ℝ) :
  t ∈ spectrum ℂ (complexify B) ↔ ∃ x : Fin n → ℂ , (complexify B) *ᵥ x = t • x := by
  sorry

-- 定义相似矩阵
def Matrix.Similar
  (A : Matrix (Fin n) (Fin n) ℝ)
  (B : Matrix (Fin n) (Fin n) ℝ)
  :=
  ∃ (P : Matrix (Fin n) (Fin n) ℝ), (IsUnit P.det) ∧ (B = P⁻¹ * A * P)
-- 矩阵特征值的等价 def
--⋄ 因为 lean 中的 def 和我们在高代中学习的 def 似乎不太一样
-- t 是 1 + B 的特征值，则 t - 1 是 B 的特征值
lemma eigenvalue_trans1
  (B : Matrix (Fin n) (Fin n) ℝ) :
  ∀ t, t ∈ spectrum ℂ (complexify (1 + B)) → (t - 1) ∈ spectrum ℂ (complexify B)
  := by
  intro t ht
  have h1 : ∃ x : Fin n → ℂ, (complexify (1 + B)) *ᵥ x = t • x := by
    apply (Matrix.eignevalue (1 + B)).1
    exact ht
  rcases h1 with ⟨x, hx⟩
  have h2 : (complexify B) *ᵥ x = (t - 1) • x := by
    have h21 : (complexify (1 + B)) = 1 + (complexify B) := by
      simp [complexify, Matrix.map_add]
    rw [h21] at hx
    have h22 : (1 + complexify B) *ᵥ x = 1 • x + (complexify B) *ᵥ x := by
      rw [add_mulVec]
      simp only [one_mulVec, one_smul]
    rw [h22] at hx
    have h23 : complexify B *ᵥ x = t • x - 1 • x := by
      rw [eq_sub_iff_add_eq, add_comm]
      exact hx
    rw [h23]
    rw [sub_smul]
    simp only [one_smul]
  have h3 : t - 1 ∈ spectrum ℂ (complexify B) := by
    apply (Matrix.eignevalue B).2
    use x
  exact h3

-- t 是 1 - B 的特征值，则 1 - t 是 B 的特征值
lemma eigenvalue_trans2
  (B : Matrix (Fin n) (Fin n) ℝ)
  :
  ∀ t, t ∈ spectrum ℂ (complexify (1 - B)) → (1 - t) ∈ spectrum ℂ (complexify B)
  := by
  intro t ht
  have h1 : ∃ x : Fin n → ℂ, (complexify (1 - B)) *ᵥ x = t • x := by
    apply (Matrix.eignevalue (1 - B)).1
    exact ht
  rcases h1 with ⟨x, hx⟩
  have h2 : (complexify B) *ᵥ x = (1 - t) • x := by
    have h21 : (complexify (1 - B)) = 1 - (complexify B) := by
      simp [complexify, Matrix.map_sub]
    rw [h21] at hx
    have h22 : (1 - complexify B) *ᵥ x = 1 • x - (complexify B) *ᵥ x := by
      rw [sub_mulVec]
      simp only [one_mulVec, one_smul]
    rw [h22] at hx
    have h23 : complexify B *ᵥ x = 1 • x - t • x := by
      rw [← hx]
      simp only [one_smul, sub_sub_cancel]
    rw [h23]
    rw [sub_smul]
    simp only [one_smul]
  have h3 : 1 - t ∈ spectrum ℂ (complexify B) := by
    apply (Matrix.eignevalue B).2
    use x
  exact h3

-- 1 + B 的特征值 t 可以表示为 1 + t'
lemma eigenvalue_trans3
  (B : Matrix (Fin n) (Fin n) ℝ) :
  ∀ t ∈ spectrum ℂ (complexify (1 + B)), ∃ t' ∈ spectrum ℂ (complexify B), t = 1 + t' := by
  intro t ht
  have h3 : t - 1 ∈ spectrum ℂ (complexify B) := by
    exact eigenvalue_trans1 B t ht
  use t - 1
  constructor
  .
    exact h3
  .
    simp only [add_sub_cancel]

-- 1 - B 的特征值 t 可以表示为 1 - t'
lemma eigenvalue_trans4
  (B : Matrix (Fin n) (Fin n) ℝ)
  :
  ∀ t ∈ spectrum ℂ (complexify (1 - B)), ∃ t' ∈ spectrum ℂ (complexify B), t = 1 - t'
  := by
  intro t ht
  have h3 : 1 - t ∈ spectrum ℂ (complexify B) := by
    exact eigenvalue_trans2 B t ht
  use 1 - t
  constructor
  .
    exact h3
  .
    simp only [sub_sub_cancel]

-- t 是 B 的特征值，则 1 + t 是 1 + B 的特征值
lemma eigenvalue_trans5
  (B : Matrix (Fin n) (Fin n) ℝ)
  :
  ∀ t, t ∈ spectrum ℂ (complexify B) → 1 + t ∈ spectrum ℂ (complexify (1 + B))
  := by
  intro t hin
  have h1 : ∃ x : Fin n → ℂ, (complexify B) *ᵥ x = t • x := by
    apply (Matrix.eignevalue B).1
    exact hin
  rcases h1 with ⟨x, hx⟩
  have h2 : (complexify (1 + B)) *ᵥ x = (1 + t) • x := by
    have h21 : complexify (1 + B) = 1 + complexify B := by
      simp [complexify, Matrix.map_add]
    rw [h21, add_mulVec, hx]
    have h22 : 1 *ᵥ x = 1 • x :=by
      simp only [one_mulVec, one_smul]
    rw [h22, add_smul]
    simp only [one_smul]
  apply (Matrix.eignevalue (1 + B)).2
  use x

-- t 是 B 的特征值，则 1 - t 是 1 - B 的特征值
lemma eigenvalue_trans6
  (B : Matrix (Fin n) (Fin n) ℝ)
  :
  ∀ t, t ∈ spectrum ℂ (complexify B) → 1 - t ∈ spectrum ℂ (complexify (1 - B))
  := by
  intro t hin
  have h1 : ∃ x : Fin n → ℂ, (complexify B) *ᵥ x = t • x := by
    apply (Matrix.eignevalue B).1
    exact hin
  rcases h1 with ⟨x, hx⟩
  have h2 : (complexify (1 - B)) *ᵥ x = (1 - t) • x := by
    have h21 : complexify (1 - B) = 1 - complexify B := by
      simp [complexify, Matrix.map_sub]
    rw [h21, sub_mulVec, hx]
    have h22 : 1 *ᵥ x = 1 • x := by
      simp only [one_mulVec, one_smul]
    rw [h22, sub_smul]
    simp only [one_smul]
  apply (Matrix.eignevalue (1 - B)).2
  use x

lemma diagPart_inv_eq_inv_sq_sqrt (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i, A i i > 0) :
    (A.diagPart)⁻¹ i i = (√(A i i))⁻¹ * (√(A i i))⁻¹ := by
    have h1 : A.diagPart i i = A i i := by
      simp [Matrix.diagPart]
    have h2 : (A.diagPart)⁻¹ i i = (A.diagPart i i)⁻¹ := by
      have h_diag : A.diagPart = Matrix.diagonal (fun i => A i i) := by
        ext i j
        simp [Matrix.diagPart, Matrix.diagonal]
        <;> aesop
      rw [h_diag]
      rw [Matrix.inv_diagonal]
      have h_pos : ∀ i : Fin n, A i i ≠ 0 := by
        intro i
        linarith [hA i]
      have h_unit : IsUnit (fun i : Fin n => A i i) := by
        rw [isUnit_iff_exists]
        use (fun i => (A i i)⁻¹)
        constructor
        · funext i
          simp [h_pos i]
        · funext i
          simp [h_pos i]
      simp [Ring.inverse, h_unit, h_pos, hA]
    rw [h2, h1]
    have h3 : (√(A i i))⁻¹ * (√(A i i))⁻¹ = (√(A i i) * √(A i i))⁻¹ := by
      ring
    rw [h3]
    have h4 : √(A i i) * √(A i i) = A i i := by
      rw [Real.mul_self_sqrt]
      linarith [hA i]
    rw [h4]


lemma diagPart_inv_eq_D_sqrt_inv_sq (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i, A i i > 0) :
    (A.diagPart)⁻¹ = (D_sqrt_inv A) * (D_sqrt_inv A) := by
    ext i j
    simp [diagPart, D_sqrt_inv, mul_apply, Finset.sum_ite_eq, Finset.mem_univ, if_pos, if_neg]
    <;> try aesop
    <;> try field_simp [hdiag i, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ A i i)]
    <;> try aesop
    exact diagPart_inv_eq_inv_sq_sqrt A hA
    have h1 : A.diagPart⁻¹ i j = 0 := by
      have h_diag : A.diagPart = Matrix.diagonal (fun i => A i i) := by
        ext i j
        simp [Matrix.diagPart, Matrix.diagonal]
        <;> aesop
      rw [h_diag]
      simp [Matrix.inv_diagonal, Matrix.diagonal_apply_ne _ h]
    exact h1


------注意这里A.lowerPart的定义与书上不一样
-----------等式4.2.15的证明
lemma cal_of_M  (A : Matrix (Fin n) (Fin n) ℝ)  (b x0 : (Fin n) → ℝ) (hdiag : ∀ i, A i i > 0):
     (myJacobi A hdiag b x0).M=
     (D_sqrt_inv A)*(1-(D_sqrt_inv A)*A*(D_sqrt_inv A))*(D_sqrt A) :=by
  have h₀ : ∀ i, A i i ≠ 0 := by exact fun i => Ne.symm (ne_of_lt (hdiag i))
  have h₁ : IsUnit A.diagPart := by exact Matrix.diagnonzero_diagInvertable A h₀
  calc
  (Jacobi ⟨A, fun i ↦ ne_of_gt (hdiag i)⟩ b x0).M=(A.diagPart)⁻¹ * (A.diagPart - A):=by exact rfl
  _=(1-(A.diagPart)⁻¹ *A) := by
    rw [Matrix.mul_sub]
    simp[h₁]
    refine nonsing_inv_mul A.diagPart ?_
    exact (isUnit_iff_isUnit_det A.diagPart).mp h₁
  _=1-(D_sqrt_inv A)*(D_sqrt_inv A)*A*(D_sqrt_inv A)*(D_sqrt A) := by
    rw [diagPart_inv_eq_D_sqrt_inv_sq A hdiag]
    simp [D_sqrt_inv_mul_self A hdiag]
    <;> aesop
    rw[mul_assoc,mul_assoc]
    simp only[D_sqrt_inv_mul_self A hdiag]
    exact Eq.symm (Matrix.mul_one (D_sqrt_inv A * (D_sqrt_inv A * A)))
  _ = (D_sqrt_inv A) * (1 - (D_sqrt_inv A) * A * (D_sqrt_inv A)) * (D_sqrt A) := by
    simp [Matrix.mul_sub, Matrix.mul_assoc, D_sqrt_inv_mul_self A hdiag]
    <;> aesop
    rw[sub_mul]
    simp [D_sqrt_inv_mul_self A hdiag]
    rw[←mul_assoc,←mul_assoc,←mul_assoc];rw [mul_assoc,mul_assoc]
    simp [D_sqrt_inv_mul_self A hdiag]

lemma cal_of_I_add_M  (A : Matrix (Fin n) (Fin n) ℝ)  (b x0 : (Fin n) → ℝ) (hdiag : ∀ i, A i i > 0):
    (D_sqrt_inv A)*(2-(D_sqrt_inv A)*A*(D_sqrt_inv A))*(D_sqrt A)= 1+(myJacobi A hdiag b x0).M
     := by
  have hM : (Jacobi ⟨A, fun i ↦ ne_of_gt (hdiag i)⟩ b x0).M =
    (D_sqrt_inv A) * (1 - (D_sqrt_inv A) * A * (D_sqrt_inv A)) * (D_sqrt A) := by
    exact cal_of_M A b x0 hdiag
  calc
    (D_sqrt_inv A)*(2-(D_sqrt_inv A)*A*(D_sqrt_inv A))*(D_sqrt A)
      =(D_sqrt_inv A)*(1+1-(D_sqrt_inv A)*A*(D_sqrt_inv A))*(D_sqrt A):=by
      congr 2; simp;exact Eq.symm one_add_one_eq_two
    _ =(D_sqrt_inv A)*(1-(D_sqrt_inv A)*A*(D_sqrt_inv A))*(D_sqrt A)+(D_sqrt_inv A)*1*(D_sqrt A):= by
      rw [sub_eq_add_neg, ← add_mul, ← mul_add,add_comm];
      congr 2
      rw[sub_eq_add_neg,add_comm,add_assoc,add_comm];
    _ =1+(D_sqrt_inv A)*(1-(D_sqrt_inv A)*A*(D_sqrt_inv A))*(D_sqrt A) :=by
      rw [mul_one,add_comm]
      simp[D_sqrt_inv_mul_self A hdiag]
    _ =1 + (Jacobi ⟨A, fun i ↦ ne_of_gt (hdiag i)⟩ b x0).M := by rw[hM]

lemma cal_of_I_minus_M  (A : Matrix (Fin n) (Fin n) ℝ)  (b x0 : (Fin n) → ℝ) (hdiag : ∀ i, A i i > 0):
     1-(myJacobi A hdiag b x0).M=(D_sqrt_inv A)*((D_sqrt_inv A)*A*(D_sqrt_inv A))*(D_sqrt A)
     := by
  calc
    1-(Jacobi ⟨A, fun i ↦ ne_of_gt (hdiag i)⟩ b x0).M
     =1-(D_sqrt_inv A) * (1 - (D_sqrt_inv A) * A * (D_sqrt_inv A)) * (D_sqrt A):=by
      simp; exact cal_of_M A b x0 hdiag
    _=1-(1-(D_sqrt_inv A) * ( (D_sqrt_inv A) * A * (D_sqrt_inv A)) * (D_sqrt A)):= by
      have t : 1-(D_sqrt_inv A) * ( (D_sqrt_inv A) * A * (D_sqrt_inv A)) * (D_sqrt A)
        =(D_sqrt_inv A) * (1 - (D_sqrt_inv A) * A * (D_sqrt_inv A)) * (D_sqrt A) :=by
        rw[mul_sub,sub_mul,mul_one];simp[D_sqrt_inv_mul_self A hdiag]
      simp[t]
    _=(D_sqrt_inv A)*((D_sqrt_inv A)*A*(D_sqrt_inv A))*(D_sqrt A) := by simp

-- (1 - D^-1/2 * A * D^-1/2).IsSymm
lemma symmetric1
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hA_symm : Aᵀ = A)
  :
  IsSymm (1 - (D_sqrt_inv A ) * A * (D_sqrt_inv A))
  := by
  unfold Matrix.IsSymm
  calc
    (1 - (D_sqrt_inv A) * A * (D_sqrt_inv A))ᵀ = 1 - ((D_sqrt_inv A) * A * (D_sqrt_inv A))ᵀ := by
      simp only [transpose_sub, transpose_one, transpose_mul]
    _ = 1 - (D_sqrt_inv A)ᵀ * ((D_sqrt_inv A) * A)ᵀ := by
      simp only [transpose_mul]
    _ = 1 - (D_sqrt_inv A)ᵀ * Aᵀ * (D_sqrt_inv A)ᵀ := by
      rw [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 - (D_sqrt_inv A) * Aᵀ * (D_sqrt_inv A) := by
      congr;
      refine IsSymm.eq ?_
      apply Matrix.IsDiag.isSymm
      exact D_sqrt_inv_isDiag A
      refine IsSymm.eq ?_
      apply Matrix.IsDiag.isSymm
      exact D_sqrt_inv_isDiag A
    _ = 1 - (D_sqrt_inv A) * A * (D_sqrt_inv A) := by
      rw [hA_symm]

-- (1 - D^-1/2 * A * D^-1/2) 对称
lemma hermitian1
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hA_symm : Aᵀ = A)
  :
  IsHermitian (1 - (D_sqrt_inv A) * A * (D_sqrt_inv A))
  := by
  unfold IsHermitian
  simp only [conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_one, transpose_mul, sub_right_inj]
  rw [hA_symm, ← mul_assoc];congr;
  refine IsSymm.eq ?_
  apply Matrix.IsDiag.isSymm
  exact D_sqrt_inv_isDiag A
  refine IsSymm.eq ?_
  apply Matrix.IsDiag.isSymm
  exact D_sqrt_inv_isDiag A

-- 定义所有特征值都是实数
def has_all_real_eigenvalues
  (B : Matrix (Fin n) (Fin n) ℝ)
  :
  Prop
  :=
  ∀ t ∈ spectrum ℂ (complexify B), t.im = 0
--⋄ 实对称矩阵的特征值都为实数
lemma all_real'
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  (hA_symm : Aᵀ = A)
  (b : Fin n → ℝ)
  (x0 : Fin n → ℝ)
  :
  has_all_real_eigenvalues (1 - (D_sqrt_inv A) * A * (D_sqrt_inv A))
  := by
  sorry

theorem SimilarMatrix_eq_eigenvalues
  (A : Matrix (Fin n) (Fin n) ℝ)
  (B : Matrix (Fin n) (Fin n) ℝ) :
  Matrix.Similar A B → spectrum ℂ (complexify A) = spectrum ℂ (complexify B) := by
  sorry


-- B 的特征值均为实数
lemma B_has_all_real_eigenvalues
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  (hA_symm : Aᵀ = A)
  (b : Fin n → ℝ)
  (x0 : Fin n → ℝ)
  :
  has_all_real_eigenvalues (myJacobi A hdiag b x0).M := by
  have h1 : Matrix.Similar (myJacobi A hdiag b x0).M (1 - (D_sqrt_inv A) * A * (D_sqrt_inv A)) := by
    unfold Matrix.Similar
    use D_sqrt_inv A
    rw[cal_of_M]
    constructor
    refine (isUnit_iff_isUnit_det (D_sqrt_inv A)).mp ?_
    exact isUnit_D_sqrt_inv A hdiag
    sorry
    -- rw [negsqrt_inv_eq A hdiag]
    -- conv =>
    --       rhs
    --       rw [← mul_assoc, ← mul_assoc]
    --       rw [mul_assoc, D_sqrt_inv_mul_self A diag, mul_sub]
    --       simp only [mul_one, one_mul]

  have h2 : spectrum ℂ (complexify (myJacobi A hdiag b x0).M) = spectrum ℂ (complexify (1 - (D_sqrt_inv A) * A * (D_sqrt_inv A))) := by
    apply SimilarMatrix_eq_eigenvalues
    exact h1
  have h3 : has_all_real_eigenvalues (1 - (D_sqrt_inv A) * A * (D_sqrt_inv A)) := by
    exact all_real' A hdiag hA_symm b b
  unfold has_all_real_eigenvalues
  intro t ht
  unfold has_all_real_eigenvalues at h3
  apply h3 t
  rw [← h2]
  exact ht

def is_real
  (z : ℂ)
  :
  Prop
  :=
  z.im = 0

lemma real_to_addreal
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  (hA_symm : Aᵀ = A)
  (b : Fin n → ℝ)
  (x0 : Fin n → ℝ)
  :
  has_all_real_eigenvalues (1 + (myJacobi A hdiag b x0).M)
  := by
  let B := (myJacobi A hdiag b x0).M
  have h0 : has_all_real_eigenvalues B := by
    exact B_has_all_real_eigenvalues A hdiag hA_symm b x0
  unfold has_all_real_eigenvalues
  intro t ht
  have h1 : ∃ x : Fin n → ℂ, (complexify (1 + B)) *ᵥ x = t • x := by
    apply (Matrix.eignevalue (1 + B)).1
    exact ht
  rcases h1 with ⟨x, hx⟩
  have h2 : (complexify B) *ᵥ x = (t - 1) • x := by
    calc
      (complexify B) *ᵥ x = (complexify (1 + B) - 1) *ᵥ x := by
        have hh1 : (complexify (1 + B)) = 1 + (complexify B) := by
          simp [complexify, Matrix.map_add]
        rw [hh1]
        simp only [add_sub_cancel_left]
      _ = (complexify (1 + B)) *ᵥ x - 1 *ᵥ x := by
        exact sub_mulVec ((complexify (1 + B))) 1 x
      _ = t • x - 1 *ᵥ x := by
        rw [hx]
      _ = (t - 1) • x := by
        simp only [one_mulVec]
        rw [sub_smul]
        simp only [one_smul]
  have h3 : t - 1 ∈ spectrum ℂ (complexify B) := by
    apply (Matrix.eignevalue B).2
    use x
  have h4 : is_real (t - 1) := by
    unfold has_all_real_eigenvalues at h0
    unfold is_real
    apply h0
    exact h3
  unfold has_all_real_eigenvalues at h0
  unfold is_real at h4
  have h5 : (t - 1).im = t.im := by
    simp only [Complex.sub_im, Complex.one_im, sub_zero]
  have h6 : t.im = 0 := by
    exact
      (AddSemiconjBy.eq_zero_iff (t - 1).im (congrFun (congrArg HAdd.hAdd h5) (t - 1).im)).mp
        (h0 (t - 1) h3)
  exact h6

-- 1 - B 特征值均为实数
lemma real_to_subreal
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  (hA_symm : Aᵀ = A)
  (b : Fin n → ℝ)
  (x0 : Fin n → ℝ) :
  has_all_real_eigenvalues (1 - (myJacobi A hdiag b x0).M)
  := by
  let B := (myJacobi A hdiag b x0).M
  have h0 : has_all_real_eigenvalues B := by
    exact B_has_all_real_eigenvalues A hdiag hA_symm b x0
  unfold has_all_real_eigenvalues
  intro t ht
  have h1 : ∃ x : Fin n → ℂ, (complexify (1 - B)) *ᵥ x = t • x := by
    apply (Matrix.eignevalue (1 - B)).1
    exact ht
  rcases h1 with ⟨x, hx⟩
  have h2 : (complexify B) *ᵥ x = (1 - t) • x := by
    have h21 : 1 • x - (complexify B) *ᵥ x = t • x := by
      calc
        1 • x - (complexify B) *ᵥ x = (complexify (1 - B)) *ᵥ x := by
          have hh1 : (complexify (1 - B)) = 1 - (complexify B) := by
            simp [complexify, Matrix.map_sub]
          rw [hh1, sub_mulVec]
          simp only [one_smul, one_mulVec]
        _ = t • x := by
          exact hx
    have h22 : (complexify B) *ᵥ x = 1 • x - t • x := by
      rw [sub_eq_iff_eq_add] at h21
      rw [h21]
      simp only [add_sub_cancel_left]
    rw [h22, sub_smul]
    simp only [one_smul]
  have h3 : 1 - t ∈ spectrum ℂ (complexify B) := by
    apply (Matrix.eignevalue B).2
    use x
  have h4 : is_real (1 - t) := by
    unfold has_all_real_eigenvalues at h0
    unfold is_real
    apply h0
    exact h3
  unfold has_all_real_eigenvalues at h0
  unfold is_real at h4
  simpa [Complex.sub_im, Complex.one_im] using h4

-- 需要与 SG_4_2_1 对接
def Jacobi_iterative_converges
  (A : Matrix (Fin n) (Fin n) ℝ)
  :
  Prop
  := by
  sorry
-- use Theorem_4_2_1
lemma JacobiIterativeiff
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  (b : Fin n → ℝ)
  (x0 : Fin n → ℝ)
  :
  Jacobi_iterative_converges A ↔ spectralRadius ℂ (complexify (myJacobi A hdiag b x0).M) < 1
  := by
  sorry

-- 谱半径 < 1 → I - B, I + B 特征值 > 0
lemma spectrum_le_one_imply_eginevalue_ge_zero
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  (hA_symm : Aᵀ = A)
  (b : Fin n → ℝ)
  (x0 : Fin n → ℝ)
  :
   spectralRadius ℂ (complexify (myJacobi A hdiag b x0).M) < 1 → (∀ t ∈ spectrum ℂ (complexify (1 + (myJacobi A hdiag b x0).M)), t.re > 0) ∧ (∀ t ∈ spectrum ℂ (complexify (1 - (myJacobi A hdiag b x0).M)), t.re > 0)
  := by

  let B := (myJacobi A hdiag b x0).M
  have h0 : has_all_real_eigenvalues B := by
    exact B_has_all_real_eigenvalues A hdiag hA_symm b x0
  intro h
  -- 每个特征值都 < 1
  have abs_lt_one : ∀ r', r' ∈ spectrum ℂ (complexify B) → ‖r'‖₊ < 1 := by
    intro r' hr'
    have h1_real : is_real r' := by
      exact h0 r' hr'
    have h_le : (↑‖r'‖₊ : ENNReal) ≤ ⨆ k ∈ (spectrum ℂ (complexify B) : Set ℂ), (↑‖k‖₊ : ENNReal) := by
      apply le_iSup₂_of_le r' hr' (le_refl _)
    exact (ENNReal.coe_lt_coe.1 (lt_of_le_of_lt h_le h))

  constructor
  . intro t ht
    have h1 : ∃ t' ∈ spectrum ℂ (complexify B), t = 1 + t' := by
      exact eigenvalue_trans3 B t ht
    rcases h1 with ⟨t', ht',hht'⟩
    have h2 : |t'.re| < 1 := by
      have h21 : ‖t'‖₊ < 1 := by
        exact abs_lt_one t' ht'
      have h211 : |t'.re| ≤ ‖t'‖₊ := by
        exact Complex.abs_re_le_norm t'
      exact lt_of_le_of_lt h211 h21
    have h3 : t'.re > -1 := by
      rw [abs_lt] at h2
      exact h2.1
    have h4 : t.re = 1 + t'.re := by
      rw [hht']
      simp only [Complex.add_re, Complex.one_re]
    have h5 : t.re > 0 := by
      rw [h4]
      exact neg_lt_iff_pos_add'.mp h3
    exact h5
  .
    intro t ht
    have h1 : ∃ t' ∈ spectrum ℂ (complexify B), t = 1 - t' := by
      exact eigenvalue_trans4 B t ht
    rcases h1 with ⟨t', ht',hht'⟩
    have h2 : |t'.re| < 1 := by
      have h21 : ‖t'‖₊ < 1 := by
        exact abs_lt_one t' ht'
      have h211 : |t'.re| ≤ ‖t'‖₊ := by
        exact Complex.abs_re_le_norm t'
      exact lt_of_le_of_lt h211 h21
    have h3 : t'.re < 1 := by
      rw [abs_lt] at h2
      exact h2.2
    have h4 : t.re = 1 - t'.re := by
      rw [hht']
      simp only [Complex.sub_re, Complex.one_re]
    have h5 : t.re > 0 := by
      rw [h4]
      exact sub_pos.mpr h3
    exact h5

-- I + B、I - B 全部特征值 > 0 → 矩阵谱半径 < 1
--⋄ sup 和 max 在有限集中的等价性
lemma eginevalue_gt_zero_imply_spectrum_le_one
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  (hA_symm : Aᵀ = A)
  (b : Fin n → ℝ)
  (x0 : Fin n → ℝ)
  :
  (∀ t ∈ spectrum ℂ (complexify (1 + (myJacobi A hdiag b x0).M)), t.re > 0) ∧ (∀ t ∈ spectrum ℂ (complexify (1 - (myJacobi A hdiag b x0).M)), t.re > 0)  → spectralRadius ℂ (complexify (myJacobi A hdiag b x0).M) < 1
  := by
  let B := (myJacobi A hdiag b x0).M

  have all_real : has_all_real_eigenvalues B := by
    exact B_has_all_real_eigenvalues A hdiag hA_symm b x0
  intro ⟨h_add, h_sub⟩
  have h1 : ∀ t, t ∈ spectrum ℂ (complexify B) → 1 + t.re > 0 ∧ 1 - t.re > 0 := by
    intro t ht
    constructor
    .
      have h11 : (1 + t) ∈ spectrum ℂ (complexify (1 + B)) := by
        exact eigenvalue_trans5 B t ht
      apply h_add (1 + t) h11
    .
      have h12 : (1 - t) ∈ spectrum ℂ (complexify (1 - B)) := by
        exact eigenvalue_trans6 B t ht
      apply h_sub (1 - t) h12
  have h2 : ∃ t, t ∈ spectrum ℂ (complexify B) ∧ ‖t‖₊ = spectralRadius ℂ (complexify B) := by
    -- apply spectrum.exists_nnnorm_eq_spectralRadius (complexify B)
    sorry
  have SR_lt_one : spectralRadius ℂ (complexify B) < 1 := by
    rcases h2 with ⟨t, ht1, ht2⟩
    rw [← ht2]
    rcases h1 t ht1 with ⟨h1_add, h1_sub⟩
    have h : is_real t := by
      exact all_real t ht1
    have h3 : 1 + t.re > 0 := by
      exact h1_add
    have h4 : 1 - t.re > 0 := by
      exact h1_sub
    have h5 : |t.re| < 1 := by
      rw [abs_lt]
      constructor
      . exact neg_lt_iff_pos_add'.mpr h3
      . exact lt_add_neg_iff_lt.mp h4
    have h6 : |t.re| = ‖t‖₊ := by
      simp only [coe_nnnorm, Complex.abs_re_eq_norm]
      exact all_real t ht1
    norm_cast
    have h7 : Real.toNNReal |t.re| = ‖t‖₊ := by
      have h71 : |t.re| ≥ 0 := by
        exact abs_nonneg t.re
      have h72 : (‖t‖₊ : ℝ) ≥ 0 := by
        exact NNReal.zero_le_coe
      rw [Real.toNNReal_of_nonneg h71]
      apply Subtype.ext -- subtype value eq if type value eq
      exact h6
    have h8 : Real.toNNReal |t.re| < 1 := by
      exact Real.toNNReal_lt_one.mpr h5
    rw [← h7]
    exact h8
  exact SR_lt_one

----------------定理：相似矩阵有相同的特征值
--------先定义相似。
def Matrix.Sim (A B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ P : Matrix (Fin n) (Fin n) ℝ, IsUnit P ∧ B = P⁻¹ * A * P
#check Polynomial.X


theorem Matrix.Sim.same_charpoly {A B : Matrix (Fin n) (Fin n) ℝ} (h : Matrix.Sim A B) :
    A.charpoly = B.charpoly := by
  apply Polynomial.funext
  intro r
  rw [Matrix.eval_charpoly, Matrix.eval_charpoly]
  rcases h with ⟨P, hP, hB⟩
  rw [hB]
  have : ((scalar (Fin n)) r - P⁻¹ * A * P).det = (P⁻¹ * ((scalar (Fin n)) r - A) * P).det := by
    congr
    rw [mul_sub, sub_mul]
    simp
    have : diagonal (fun x => r) = r • (1 : Matrix (Fin n) (Fin n) ℝ) := by
      ext i j
      unfold diagonal
      simp
      split_ifs with h
      · rw [h]; simp
      simp; right; simp [h]
    rw [this]
    simp; congr
    rw [Matrix.nonsing_inv_mul]
    exact (isUnit_iff_isUnit_det P).mp hP
  rw [this, det_conj']
  exact hP

theorem Matrix.Sim.same_charpoly_same_spectrum {A B : Matrix (Fin n) (Fin n) ℝ} (h : Matrix.Sim A B) :
    spectrum ℝ A = spectrum ℝ B := by
  ext x
  -- rw [← Module.End.hasEigenvalue_iff_mem_spectrum]
  sorry


  -- rcases h with ⟨P, hP, hB⟩
  -- have hP': IsUnit P.det := by exact (isUnit_iff_isUnit_det P).mp hP
  -- have h₁ : ∀ t :ℝ ,(t•(1 : Matrix (Fin n) (Fin n) ℝ) -B).det=(t•(1 : Matrix (Fin n) (Fin n) ℝ)-A).det:= by
  --   have h₁₁ :∀ t :ℝ, P⁻¹*(t•(1 : Matrix (Fin n) (Fin n) ℝ)-A)* P= t•(1 : Matrix (Fin n) (Fin n) ℝ) -B := by
  --     intro t
  --     calc
  --       P⁻¹ * (t • (1 : Matrix (Fin n) (Fin n) ℝ) - A) * P = (P⁻¹ * (t • 1)-P⁻¹ *A)*P := by rw [@Matrix.mul_sub]
  --       _ = P⁻¹* (t • 1)*P-P⁻¹ *A*P := by rw[sub_mul]
  --       _ = t•(1 : Matrix (Fin n) (Fin n) ℝ) -B := by
  --         rw [hB];simp;rw[show P⁻¹ * P=1 by refine nonsing_inv_mul P ?_;exact (isUnit_iff_isUnit_det P).mp hP]
  --   intro t
  --   have : P.det * P.det⁻¹=1 := by exact IsUnit.mul_inv_cancel hP'
  --   rw[←h₁₁];simp[det_conj'];rw[mul_comm];exact IsUnit.mul_inv_cancel_left hP' (t • 1 - A).det
  -- sorry



-- noncomputable def realEigenvalues (A : Matrix (Fin n) (Fin n) ℝ) : Multiset ℝ :=
--   ((A.map Complex.ofReal).charpoly.roots.map Complex.re).filter
--     (fun r => ((A.map Complex.ofReal).charpoly.roots.filter
--       (fun z => z.im = 0 ∧ z.re = r)).card > 0)

-- def AllEigenvaluesPos (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
--   ∀ r ∈ realEigenvalues A, 0 < r



lemma Matrix.PosDef_iff_spectrum_pos  (A : Matrix (Fin n) (Fin n) ℝ)(h_symm : A.IsSymm) :
    A.PosDef ↔ ∀ c ∈ spectrum ℝ A, c > 0 := by
  constructor
------左推右
  intro hh c hc
  sorry
-----右推左
  have : A.IsHermitian := h_symm
  intro hc
  rw [Matrix.PosDef.posDef_iff_eq_conjTranspose_mul_self]
  rw [Matrix.IsHermitian.spectral_theorem h_symm]
  let D : Matrix (Fin n) (Fin n) ℝ := diagonal (RCLike.ofReal ∘ IsHermitian.eigenvalues h_symm)
  have hdiag: ∀ i, D i i > 0 := by
    intro i; simp [D]
    have : IsHermitian.eigenvalues h_symm i ∈ spectrum ℝ A := by
      rw [Matrix.IsHermitian.eigenvalues_eq_spectrum_real]
      simp; exact this
    exact hc _ this
  let D1 : Matrix (Fin n) (Fin n) ℝ := fun i j ↦ if i = j then Real.sqrt (D i j) else 0 --
  have hD : D = D1ᵀ * D1 := by
    have t₁: D1.IsDiag := by unfold D1 ;unfold IsDiag;intro i j h;simp[h]
    have t₂: D1.IsSymm := by exact IsDiag.isSymm t₁
    rw[t₂];ext i j;
    by_cases h : i = j
    subst h
    simp [D1, mul_apply, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, diagonal_apply_eq]
    refine (Real.sqrt_eq_iff_mul_self_eq ?_ ?_).mp rfl;
    exact le_of_lt (hdiag i);exact Real.sqrt_nonneg (D i i)
-------i≠ j
    simp [D1, mul_apply, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, h]
    exact
      diagonal_apply_ne' (RCLike.ofReal ∘ IsHermitian.eigenvalues h_symm) fun a =>
        h (id (Eq.symm a))
  let P : Matrix (Fin n) (Fin n) ℝ := (IsHermitian.eigenvectorUnitary h_symm)
  use D1 * Pᵀ
  constructor
----------- IsUnit (D1 * Pᵀ)
  have hD1_unit : IsUnit D1 := by
    rw[isUnit_iff_isUnit_det D1]
    have hD1_eq : D1 = diagonal (fun i => √(D i i)) := by
      ext i j
      by_cases h : i = j
      simp [h, D1];simp [h, D1]
    rw [hD1_eq, det_diagonal]
    simp;
    intro h
    have h_pos : ∀ i, √(D i i) > 0 := fun i => Real.sqrt_pos.mpr (hdiag i)
    have h_prod_pos : ∏ i, √(D i i) > 0 := Finset.prod_pos (fun i _ => h_pos i)
    linarith
  have hPt_unit : IsUnit Pᵀ := by
    sorry
  exact IsUnit.mul hD1_unit hPt_unit
  have : (IsHermitian.eigenvectorUnitary h_symm : Matrix (Fin n) (Fin n) ℝ) *
    diagonal (RCLike.ofReal ∘ IsHermitian.eigenvalues h_symm) *
    star ↑(IsHermitian.eigenvectorUnitary h_symm :  Matrix (Fin n) (Fin n) ℝ) = P * D * Pᵀ := by
    simp [P, D]
    rfl
  rw [this]
  simp
  rw [← mul_assoc]
  rw [hD]
  group


lemma A_Pos (A : Matrix (Fin n) (Fin n) ℝ)  (b x0 : (Fin n) → ℝ) (hdiag : ∀ i, A i i > 0)(h_symm : A.IsSymm):
    A.PosDef ↔ ∀ c ∈ spectrum ℝ ((D_sqrt_inv A)*((D_sqrt_inv A)*A*(D_sqrt_inv A))*(D_sqrt A)), c > 0:= by
  -- constructor
  have h1 : spectrum ℝ ((D_sqrt_inv A)*A*(D_sqrt_inv A)) = spectrum ℝ ((D_sqrt_inv A)*((D_sqrt_inv A)*A*(D_sqrt_inv A))*(D_sqrt A)) := by
    apply Matrix.Sim.same_charpoly_same_spectrum
    use (D_sqrt A)
    constructor
    refine exists_left_inverse_iff_isUnit.mp ?_
    use D_sqrt_inv A;exact D_sqrt_inv_mul_self A hdiag
    congr
    refine Eq.symm (inv_eq_left_inv ?_);exact D_sqrt_inv_mul_self A hdiag
  have h2: A.PosDef ↔  ((D_sqrt_inv A)*A*(D_sqrt_inv A)).PosDef := by
    let P := D_sqrt_inv A
    have hP : Invertible P := by
      refine P.invertibleOfRightInverse ?_ ?_ ;exact D_sqrt A;exact D_sqrt_inv_mul_self A hdiag
    constructor
------------A.PosDef → (D_sqrt_inv A * A * D_sqrt_inv A).PosDef
    intro hA
    have h_inj : Function.Injective P.mulVec :=by exact mulVec_injective_of_invertible P
    have :(D_sqrt_inv A) * A * (D_sqrt_inv A)=(D_sqrt_inv A) * A * (D_sqrt_inv A)ᴴ := by
      congr;
      have t:( D_sqrt_inv A).IsSymm:= by apply IsDiag.isSymm (D_sqrt_inv_isDiag A)
      exact Eq.symm (IsHermitian.eq t)
    rw[this]
    refine PosDef.mul_mul_conjTranspose_same hA ?_
    exact vecMul_injective_of_invertible (D_sqrt_inv A)
--------------(D_sqrt_inv A * A * D_sqrt_inv A).PosDef → A.PosDef
    intro hDAD
    have : A=(D_sqrt A)*(D_sqrt_inv A * A * D_sqrt_inv A)*(D_sqrt A):= by
      rw[←mul_assoc,←mul_assoc];rw[mul_assoc];rw[D_sqrt_inv_mul_self A hdiag];rw[mul_one]
      have :D_sqrt A * D_sqrt_inv A =1:=by
        exact mul_eq_one_comm.mpr (D_sqrt_inv_mul_self A hdiag)
      rw[this];simp
    rw[this]
    have :D_sqrt A * (D_sqrt_inv A * A * D_sqrt_inv A) * D_sqrt A=
      D_sqrt A * (D_sqrt_inv A * A * D_sqrt_inv A) * (D_sqrt A)ᴴ:= by
      congr;simp;refine Eq.symm (IsSymm.eq ?_);
      apply IsDiag.isSymm (D_sqrt_isDiag A)
    rw[this]
    refine PosDef.mul_mul_conjTranspose_same hDAD ?_
    refine vecMul_injective_of_isUnit ?_;refine exists_left_inverse_iff_isUnit.mp ?_;
    use D_sqrt_inv A;exact D_sqrt_inv_mul_self A hdiag
  rw [h2, Matrix.PosDef_iff_spectrum_pos]
  ·
    sorry
  sorry
-- ------A.PosDef → (D_sqrt_inv A * (D_sqrt_inv A * A * D_sqrt_inv A) * D_sqrt A).PosDef
--   intro hA
--   have h₀ : (D_sqrt_inv A).IsSymm := (D_sqrt_inv_isDiag A).isSymm
--   have h₁ : ((D_sqrt_inv A)ᴴ * A * D_sqrt_inv A).PosDef := by
--     have h : IsUnit (D_sqrt_inv A) := isUnit_D_sqrt_inv A hdiag
--     apply Matrix.PosDef.conjTranspose_mul_mul_same hA
--     exact mulVec_injective_of_isUnit h
--   have h₂ : ((D_sqrt_inv A)*A*(D_sqrt_inv A)).PosDef := by
--     have h₂₀ :(D_sqrt_inv A)=(D_sqrt_inv A)ᴴ := by exact Eq.symm (IsHermitian.eq h₀)
--     have h₂₁ :((D_sqrt_inv A)*A*(D_sqrt_inv A))=((D_sqrt_inv A)ᴴ * A * D_sqrt_inv A) := by
--       refine (IsUnit.mul_left_inj ?_).mpr ?_
--       exact isUnit_D_sqrt_inv A hdiag
--       exact Mathlib.Tactic.LinearCombination.mul_eq_const h₂₀ A
--     rw[h₂₁];exact h₁
--   have h₃ :∀ i, h₂.1.eigenvalues i > 0 := by exact fun i => PosDef.eigenvalues_pos h₂ i
--   sorry
-- ------------------(D_sqrt_inv A * (D_sqrt_inv A * A * D_sqrt_inv A) * D_sqrt A).PosDef → A.PosDef
--   sorry






















-- #check Matrix.mul_inv_cancel_left_of_invertible
-- def Jacobi_iterative_converges (X : Matrix (Fin n) (Fin n) ℝ) : Prop := by
--   sorry
-- ------左推右
-- lemma jacobi_convergence_iff_left
--     (A : Matrix (Fin n) (Fin n) ℝ)(hsym : IsSymmetric A)(hdiag : ∀ i, A i i > 0) :
--     Jacobi_iterative_converges A ↔PosDef A ∧ PosDef (twoD_minus_A A) := by
--   sorry
-- 需要与 SG_4_2_1 对接


theorem SG_4_2_6
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  (hA_symm : Aᵀ = A)
  (b : Fin n → ℝ)
  (x0 : Fin n → ℝ) :
  Jacobi_iterative_converges A ↔ PosDef A ∧ PosDef (2 • A.diagPart - A) := by

  -- Jacobi_iterative_converges A ↔ spectrum ℂ (complexify B) < 1
  rw [JacobiIterativeiff A hdiag b x0]
  let B := (myJacobi A hdiag b x0).M

  -- 在 B 的特征值都为实数的前提下，谱半径 < 1 ↔ I - B, I + B 特征值 > 0
  have spectrum_le_one_iff_eignevalue_gt_zero_iff : spectralRadius ℂ (complexify B) < 1 ↔ (∀ t ∈ spectrum ℂ (complexify (1 + B)), t.re > 0) ∧ (∀ t ∈ spectrum ℂ (complexify (1 - B)), t.re > 0) := by
    exact
      { mp := spectrum_le_one_imply_eginevalue_ge_zero A hdiag hA_symm b x0 ,
        mpr := eginevalue_gt_zero_imply_spectrum_le_one A hdiag hA_symm b x0 }

  rw [spectrum_le_one_iff_eignevalue_gt_zero_iff]

  have eignevalue_gt_zero_iff_pos : (∀ t ∈ spectrum ℂ (complexify (1 + B)), t.re > 0) ∧ (∀ t ∈ spectrum ℂ (complexify (1 - B)), t.re > 0) ↔ PosDef A ∧ PosDef (2 • A.diagPart - A) := by
    sorry-------这里有A_pos可能可以参考
  rw [eignevalue_gt_zero_iff_pos]





end iterative_method
