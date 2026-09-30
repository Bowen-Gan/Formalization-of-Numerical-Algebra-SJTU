import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.PosDef

section StrictlyDiagonally
open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

--严格对角占优矩阵--
def Matrix.IsStrictlyDiagonallyDominant
    (A : Matrix n n ℝ) : Prop :=
  ∀ i, |A i i| > ∑ j ∈ Finset.univ.erase i, |A i j|
--严格弱对角占优矩阵--
def Matrix.IsWeaklyStrictlyDiagonallyDominant (A : Matrix n n ℝ) : Prop :=
  (∀ i, |A i i| ≥ ∑ j ∈ univ.erase i, |A i j|) ∧
  (∃ k, |A k k| > ∑ j ∈ univ.erase k, |A k j|)
/-- 定义：矩阵A是可约的，当且仅当存在W的两个非空子集S和T，满足S∪T=W，S∩T=∅，
    使得对所有i∈S，j∈T，有A i j = 0 -/
def W (n : Type*) [Fintype n] : Finset n := univ
def Matrix.IsReducible {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℝ) : Prop :=
  ∃ (S T : Finset n),
    S.Nonempty ∧ T.Nonempty ∧
    S ∪ T = W n ∧ S ∩ T = ∅ ∧
    ∀ (i j : n), i ∈ S → j ∈ T → A i j = 0
/-- 定义：矩阵A是不可约的，当且仅当它不是可约的 -/
def Matrix.IsIrreducible {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℝ) : Prop :=
  ¬ A.IsReducible
--不可约对角占优矩阵--
def Matrix.IsIrreduciblyDiagonallyDominant (A : Matrix n n ℝ) : Prop :=
  A.IsIrreducible ∧(A.IsWeaklyStrictlyDiagonallyDominant)


/-- 定理：严格对角占优矩阵是非奇异的 -/
def Matrix.IsNonsingular (A : Matrix n n ℝ) : Prop :=
  A.det ≠ 0
/-- 定义：矩阵A是奇异的，当且仅当其行列式为零 -/
def Matrix.IsSingular (A : Matrix n n ℝ) : Prop :=
  A.det = 0
/-- 定理：若矩阵A是奇异矩阵，那么齐次方程组Ax=0有非0解 -/

theorem singular_matrix_has_nonzero_solution (A : Matrix n n ℝ)
    (hA : A.IsSingular) : ∃ x : n → ℝ, x ≠ 0 ∧ A.mulVec x = 0 := by
  apply Matrix.exists_mulVec_eq_zero_iff.mpr
  exact hA

/-- 向量的无穷范数定义为 ‖x‖∞ = max |x_i| -/
noncomputable def linf_norm (x : n → ℝ)[Nonempty n] : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty (fun i => ‖x i‖)
-- 标准表示法 ‖x‖∞
notation "‖" x "‖∞" => linf_norm x
axiom h_norm_pos [Nonempty n](x : n → ℝ)(x_norm_inf := linf_norm x)  : x_norm_inf > 0

theorem exists_abs_eq_linf_norm [Nonempty n](x : n → ℝ) :
    ∃ i, |x i| = ‖x‖∞ := by
  sorry

theorem h_xj_le_norm [Nonempty n](x : n → ℝ)(x_norm_inf := linf_norm x) :
    ∀ j, |x j| ≤ x_norm_inf := by
  sorry
