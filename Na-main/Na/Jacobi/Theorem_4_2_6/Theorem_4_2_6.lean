/-
Copyright (c) 2025 Tianjue Ke, Zixi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zixi Wang, Tianjue Ke
-/

import Mathlib
import Na.Defs

/-!
# Equivalent Proposition of Jacobi Iterative Method Converges

This file develops an equivalent creteria of Jacobi iterative, i.e. For equation Ax = b, Jacobi iterative method converges for any initial x_0 ↔ A and 2D - A are positive definite matrix. (D is the diag part of A)
-/

section
open Matrix

variable {n : Nat} {A B: Matrix (Fin n) (Fin n) ℝ} {b x0 : Fin n → ℝ} {t : ℂ} {hdiag : ∀ i, A i i > 0}


-- ========= notation def =====================
-- 对角线元素 > 0 得到非 0
lemma diagpos_to_nonzero
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  :
  ∀ i, A i i ≠ 0
  := by
  exact fun i ↦ Ne.symm (ne_of_lt (hdiag i))

-- 需要与 SG_4_2_1 对接
def Jacobi_iterative_converges
  (A : Matrix (Fin n) (Fin n) ℝ)
  :
  Prop
  := by
  sorry

-- def D⁻¹
noncomputable def invdiagPart
  (A : Matrix (Fin n) (Fin n) ℝ)
  :
  Matrix (Fin n) (Fin n) ℝ
  :=
  fun i j ↦ if i = j then 1 / (A i j) else 0

-- def D^1/2
noncomputable def sqrtdiagPart
  (A : Matrix (Fin n) (Fin n) ℝ)
  :
  Matrix (Fin n) (Fin n) ℝ
  :=
  fun i j ↦ if i = j then Real.sqrt (A i j) else 0

-- def D^-1/2
noncomputable def negsqrtdiagPart
  (A : Matrix (Fin n) (Fin n) ℝ)
  :
  Matrix (Fin n) (Fin n) ℝ
  :=
  fun i j ↦ if i = j then 1 / Real.sqrt (A i j) else 0

-- redef Jacobi structure, 因为条件是对角线元素 > 0，myJacobi 可接受这个参数的传入
noncomputable def myJacobi
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  (b : Fin n → ℝ)
  (x0 : Fin n → ℝ)
  :=
  Jacobi A (diagpos_to_nonzero A hdiag) b x0


-- ======= local notation ================
-- 改善 InfoView 阅读体验
local notation "D" => diagPart A
local notation "D⁻¹" => invdiagPart A
local notation "D^1/2" => sqrtdiagPart A
local notation "D^-1/2" => negsqrtdiagPart A
local notation "algJ" => myJacobi A hdiag b x0


-- ======== basic operation def and Thm =================
-- 复数化实矩阵
def complexify
  (B : Matrix (Fin n) (Fin n) ℝ)
  :
  Matrix (Fin n) (Fin n) ℂ
  :=
  Matrix.map B (↑)  -- 将每个实数元素通过强制转换嵌入复数

-- 定义所有特征值都是实数
def has_all_real_eigenvalues
  (B : Matrix (Fin n) (Fin n) ℝ)
  :
  Prop
  :=
  ∀ t ∈ spectrum ℂ (complexify B), t.im = 0

-- 定义相似矩阵
def Matrix.Similar
  (A : Matrix (Fin n) (Fin n) ℝ)
  (B : Matrix (Fin n) (Fin n) ℝ)
  :=
  ∃ (P : Matrix (Fin n) (Fin n) ℝ), (IsUnit P.det) ∧ (B = P⁻¹ * A * P)

-- def real num judge
def is_real
  (z : ℂ)
  :
  Prop
  :=
  z.im = 0

-- 矩阵特征值的等价 def
--⋄ 因为 lean 中的 def 和我们在高代中学习的 def 似乎不太一样
lemma Matrix.eignevalue
  (B : Matrix (Fin n) (Fin n) ℝ) :
  t ∈ spectrum ℂ (complexify B) ↔ ∃ x : Fin n → ℂ , (complexify B) *ᵥ x = t • x := by
  sorry

-- similar matrix have the same charpoly
lemma Matrix.Similar.same_charpoly
  (A : Matrix (Fin n) (Fin n) ℝ)
  (B : Matrix (Fin n) (Fin n) ℝ)
  (hsim : Matrix.Similar A B)
  :
  charpoly A = charpoly B
  := by
  apply Polynomial.funext
  intro r
  rw [Matrix.eval_charpoly, Matrix.eval_charpoly]
  rcases hsim with ⟨P, hP, hB⟩
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
    exact hP
  rw [this, det_conj']
  exact (isUnit_iff_isUnit_det P).mpr hP

-- 相似矩阵有相同特征值
-- 这个 cba 同学已经证明了，不过还没有整合到一起
theorem SimilarMatrix_eq_eigenvalues
  (A : Matrix (Fin n) (Fin n) ℝ)
  (B : Matrix (Fin n) (Fin n) ℝ)
  (hsim : Matrix.Similar A B) :
  spectrum ℂ (complexify A) = spectrum ℂ (complexify B)
  := by

  sorry

-- ================ 矩阵计算需要用到的基本等式 =================
--⋄ 为了便于逐项计算矩阵乘法，我们采用了 if-else 逐项定义了逆矩阵，但是在证明其和 Mathlib 库中逆矩阵 def 一致时遇到了一些麻烦
--  D ⁻¹ = D⁻¹
lemma inv_eq
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  :
  (diagPart A)⁻¹ = invdiagPart A
  := by
  refine ext ?_
  intro i j
  unfold diagPart invdiagPart diagonal
  simp only [one_div]
  by_cases h1 : i = j
  . split_ifs
    rw [inv_def]
    simp only [Ring.inverse_eq_inv', smul_apply, smul_eq_mul]
    refine (IsUnit.inv_mul_eq_iff_eq_mul ?_).mpr ?_
    . have h2 : (diagPart A).det ≠ 0 := by
        unfold diagPart
        simp only [det_diagonal, ne_eq]
        by_contra a
        have h3 : ∏ i, A i i > 0 := by
          exact Finset.prod_pos fun i a ↦ hdiag i
        have h4 : ∏ i, A i i ≠ 0 := by
          exact Ne.symm (ne_of_lt h3)
        contradiction
      exact Ne.isUnit h2
    .
      sorry
  . split_ifs
    sorry

-- D⁻¹ * D = 1
lemma inv_mul_eq
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  :
  (invdiagPart A) * (diagPart A) = 1
  := by
  refine ext ?_
  intro i j
  have h1 : ((invdiagPart A) * (diagPart A)) i j = ∑ k, ((invdiagPart A) i k) * ((diagPart A) k j) := rfl
  unfold invdiagPart diagPart
  by_cases h2 : i = j
  . rw [h2]
    simp only [one_div, mul_diagonal, ↓reduceIte, one_apply_eq]
    refine IsUnit.inv_mul_cancel ?_
    have h3 : A j j ≠ 0 := by
      exact diagpos_to_nonzero A hdiag j
    exact Ne.isUnit h3
  . simp only [one_div, mul_diagonal, ite_mul, zero_mul]
    split_ifs
    exact Eq.symm (one_apply_ne' fun a ↦ h2 (id (Eq.symm a)))

-- D^-1/2 * D^1/2 = 1
lemma sqrt_eq_one
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  :
  (negsqrtdiagPart A) * (sqrtdiagPart A) = 1
  := by
  refine ext ?_
  intro i j
  have h1 : ((negsqrtdiagPart A) * (sqrtdiagPart A)) i j = ∑ k, ((negsqrtdiagPart A) i k) * ((sqrtdiagPart A) k j) := rfl
  rw [h1]
  unfold negsqrtdiagPart sqrtdiagPart
  simp only [one_div, mul_ite, ite_mul, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte]
  by_cases h2 : i = j
  . split_ifs
    refine (IsUnit.inv_mul_eq_iff_eq_mul ?_).mpr ?_
    rw [h2]
    . have h3 : A j j ≠ 0 := by
        exact diagpos_to_nonzero A hdiag j
      have h4 : Real.sqrt (A j j) ≠ 0 := by
        exact Real.sqrt_ne_zero'.mpr (hdiag j)
      exact Ne.isUnit h4
    . rw [h2]
      simp only [one_apply_eq, mul_one]
  . split_ifs
    exact Eq.symm (one_apply_ne' fun a ↦ h2 (id (Eq.symm a)))

-- D^1/2 * D^-1/2 = 1
lemma sqrt_eq_one'
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  :
  (sqrtdiagPart A) * (negsqrtdiagPart A) = 1
  := by
  refine ext ?_
  intro i j
  have h1 : ((sqrtdiagPart A) * (negsqrtdiagPart A)) i j = ∑ k, ((sqrtdiagPart A) i k) * ((negsqrtdiagPart A) k j) := rfl
  rw [h1]
  unfold sqrtdiagPart negsqrtdiagPart
  simp only [one_div, mul_ite, ite_mul, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  by_cases h2 : i = j
  . split_ifs
    rw [h2]
    refine (mul_inv_eq_iff_eq_mul₀ ?_).mpr ?_
    . exact Real.sqrt_ne_zero'.mpr (hdiag j)
    . simp only [one_apply_eq, one_mul]
  . split_ifs
    exact Eq.symm (one_apply_ne' fun a ↦ h2 (id (Eq.symm a)))

--  D^-1/2 * D^-1/2 = D⁻¹
lemma negsqrt_eq
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  :
  (negsqrtdiagPart A) * (negsqrtdiagPart A) = invdiagPart A
  := by
  refine ext ?_
  intro i j
  have h1 : ((negsqrtdiagPart A) * (negsqrtdiagPart A)) i j = ∑ k, ((negsqrtdiagPart A) i k) * ((negsqrtdiagPart A) k j) := rfl
  rw [h1]
  unfold invdiagPart negsqrtdiagPart
  simp only [one_div, mul_ite, ite_mul, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  by_cases h2 : i = j
  . split_ifs
    rw [h2]
    rw [← mul_inv, ← pow_two]
    simp only [_root_.inv_inj]
    refine Real.sq_sqrt ?_
    exact le_of_lt (hdiag j)
  . split_ifs
    rfl

-- D^1/2 * D^1/2 = D
lemma sqrtpos_eq
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  :
  (sqrtdiagPart A) * (sqrtdiagPart A) = diagPart A
  := by
  refine ext ?_
  intro i j
  have h1 : ((sqrtdiagPart A) * (sqrtdiagPart A)) i j = ∑ k, ((sqrtdiagPart A) i k) * ((sqrtdiagPart A) k j) := rfl
  rw [h1]
  unfold sqrtdiagPart diagPart diagonal
  by_cases h2 : i = j
  . simp only [mul_ite, ite_mul, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, of_apply]
    split_ifs
    rw [h2]
    rw [← pow_two]
    refine Real.sq_sqrt ?_
    exact le_of_lt (hdiag j)
  . simp only [mul_ite, ite_mul, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, of_apply]
    split_ifs
    rfl

-- D^-1/2⁻¹ = D^1/2
lemma negsqrt_inv_eq
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  :
  (negsqrtdiagPart A)⁻¹ = sqrtdiagPart A
  := by
  refine ext ?_
  intro i j
  unfold negsqrtdiagPart sqrtdiagPart
  simp only [one_div]
  by_cases h1 : i = j
  . split_ifs
    rw [h1]

    sorry
  . split_ifs

    sorry

-- D^-1/2ᵀ = D^-1/2
lemma sqrt_symm
  (A : Matrix (Fin n) (Fin n) ℝ)
  :
  (negsqrtdiagPart A)ᵀ = negsqrtdiagPart A
  := by
  refine ext ?_
  intro i j
  unfold negsqrtdiagPart
  simp only [one_div, transpose_apply]
  by_cases h1 : i = j
  . rw [h1]
  . split_ifs
    . (expose_names; exact False.elim (h1 (id (Eq.symm h))))
    . rfl

-- D^-1/2.det ≠ 0
lemma Bsqrt_det_nonzero
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  (hA_symm : Aᵀ = A)
  (b : Fin n → ℝ)
  (x0 : Fin n → ℝ)
  :
  (negsqrtdiagPart A).det ≠ 0
  := by
  sorry


-- ========= eignevalue transform by polynomials ============
-- 这里应该可以一般化为所有的多项式，不过由于时间问题没有做这个一般的命题

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
  . exact h3
  . simp only [add_sub_cancel]

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
  . exact h3
  . simp only [sub_sub_cancel]

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


-- ======== 开始对题目进行证明，这里先证明一些等式和比较重要的性质 =====
-- B = D^-1/2 * (1 - D^-1/2 * A * D^-1/2) * D^1/2
lemma eq_4_2_15
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  (b : Fin n → ℝ)
  (x0 : Fin n → ℝ)
  :
  (myJacobi A hdiag b x0).M = (negsqrtdiagPart A) * (1 - (negsqrtdiagPart A) * A * (negsqrtdiagPart A)) * sqrtdiagPart A := by
  calc
    (myJacobi A hdiag b x0).M = (invdiagPart A) * ((diagPart A) - A) := by
      unfold myJacobi Jacobi
      simp only [Units.inv_eq_val_inv, coe_units_inv, IsUnit.unit_spec]
      rw [inv_eq A hdiag]
    _ = 1 - (invdiagPart A) * A := by
      rw [mul_sub]
      rw [inv_mul_eq A hdiag]
    _ = (negsqrtdiagPart A) * (1 - (negsqrtdiagPart A) * A * (negsqrtdiagPart A)) * sqrtdiagPart A := by
      rw [mul_sub]
      simp only [mul_one]
      rw [sub_mul]
      rw [sqrt_eq_one A hdiag]
      simp only [sub_right_inj]
      rw [← mul_assoc, ← mul_assoc]
      rw [negsqrt_eq A hdiag]
      rw [mul_assoc]
      rw [sqrt_eq_one A hdiag]
      simp only [mul_one]

-- (1 - D^-1/2 * A * D^-1/2).IsSymm
lemma symmetric1
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hA_symm : Aᵀ = A)
  :
  IsSymm (1 - (negsqrtdiagPart A) * A * (negsqrtdiagPart A))
  := by
  unfold Matrix.IsSymm
  calc
    (1 - (negsqrtdiagPart A) * A * (negsqrtdiagPart A))ᵀ = 1 - ((negsqrtdiagPart A) * A * (negsqrtdiagPart A))ᵀ := by
      simp only [transpose_sub, transpose_one, transpose_mul]
    _ = 1 - (negsqrtdiagPart A)ᵀ * ((negsqrtdiagPart A) * A)ᵀ := by
      simp only [transpose_mul]
    _ = 1 - (negsqrtdiagPart A)ᵀ * Aᵀ * (negsqrtdiagPart A)ᵀ := by
      rw [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 - (negsqrtdiagPart A) * Aᵀ * (negsqrtdiagPart A) := by
      rw [sqrt_symm A]
    _ = 1 - (negsqrtdiagPart A) * A * (negsqrtdiagPart A) := by
      rw [hA_symm]

-- (1 - D^-1/2 * A * D^-1/2) 对称
lemma hermitian1
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hA_symm : Aᵀ = A)
  :
  IsHermitian (1 - (negsqrtdiagPart A) * A * (negsqrtdiagPart A))
  := by
  unfold IsHermitian
  simp only [conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_one, transpose_mul, sub_right_inj]
  rw [hA_symm, ← mul_assoc, sqrt_symm A]

-- has_all_real_eigenvalues (1 - D^-1/2 * A * D^-1/2)
--⋄ 实对称矩阵的特征值都为实数
lemma all_real'
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  (hA_symm : Aᵀ = A)
  (b : Fin n → ℝ)
  (x0 : Fin n → ℝ)
  :
  has_all_real_eigenvalues (1 - (negsqrtdiagPart A) * A * (negsqrtdiagPart A))
  := by
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
  have h1 : Matrix.Similar (myJacobi A hdiag b x0).M (1 - (negsqrtdiagPart A) * A * (negsqrtdiagPart A)) := by
    unfold Matrix.Similar
    use negsqrtdiagPart A
    rw [eq_4_2_15]
    . constructor
      . refine isUnit_iff_exists_inv.mpr ?_
        use 1 / ((negsqrtdiagPart A).det)
        simp only [one_div]
        refine mul_inv_cancel₀ ?_
        exact Bsqrt_det_nonzero A hdiag hA_symm b b
      . rw [negsqrt_inv_eq A hdiag]
        conv =>
          rhs
          rw [← mul_assoc, ← mul_assoc]
          rw [mul_assoc, sqrt_eq_one' A hdiag, mul_sub]
          simp only [mul_one, one_mul]

  have h2 : spectrum ℂ (complexify (myJacobi A hdiag b x0).M) = spectrum ℂ (complexify (1 - (negsqrtdiagPart A) * A * (negsqrtdiagPart A))) := by
    apply SimilarMatrix_eq_eigenvalues
    exact h1
  have h3 : has_all_real_eigenvalues (1 - (negsqrtdiagPart A) * A * (negsqrtdiagPart A)) := by
    exact all_real' A hdiag hA_symm b b
  unfold has_all_real_eigenvalues
  intro t ht
  unfold has_all_real_eigenvalues at h3
  apply h3 t
  rw [← h2]
  exact ht

-- 1 + B 特征值均为实数
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

lemma eq_4_2_16
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  (b : Fin n → ℝ)
  (x0 : Fin n → ℝ)
  :
  1 - (myJacobi A hdiag b x0).M = (negsqrtdiagPart A) * ((negsqrtdiagPart A) * A *  (negsqrtdiagPart A)) * (sqrtdiagPart A) := by
  rw [eq_4_2_15, ← mul_assoc, ← mul_assoc, negsqrt_eq A hdiag]
  conv =>
    rhs
    rw [mul_assoc, sqrt_eq_one A hdiag]
  simp only [mul_one]
  conv =>
    lhs
    rw [mul_sub]
    simp only [mul_one]
    rw [← mul_assoc, ← mul_assoc, negsqrt_eq A hdiag, sub_mul, sqrt_eq_one A hdiag, mul_assoc, sqrt_eq_one A hdiag]
    simp only [mul_one, sub_sub_cancel]

-- 1 + B = D^-1/2 * (2 - D^-1/2 * A * D^-1/2) * D^1/2
lemma eq_4_2_17
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  (b : Fin n → ℝ)
  (x0 : Fin n → ℝ)
  :
  1 + (myJacobi A hdiag b x0).M = (negsqrtdiagPart A) * ( 2 -(negsqrtdiagPart A) * A * (negsqrtdiagPart A)) * (sqrtdiagPart A)
  := by
  rw [eq_4_2_15]
  --
  have h : 2 = 2 • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    simp only [nsmul_eq_mul, Nat.cast_ofNat, mul_one]
  conv =>
    rhs
    rw [mul_sub, sub_mul]
    rw [h]
    rw [mul_smul_comm]
    simp only [mul_one, nsmul_eq_mul, Nat.cast_ofNat]
    rw [mul_assoc, sqrt_eq_one A hdiag]
    simp only [mul_one]
    rw [← mul_assoc, ← mul_assoc, negsqrt_eq A hdiag, mul_assoc, sqrt_eq_one A hdiag]
    simp only [mul_one]
  conv =>
    lhs
    rw [mul_sub]
    simp only [mul_one]
    rw [← mul_assoc, ← mul_assoc, negsqrt_eq A hdiag, sub_mul, sqrt_eq_one A hdiag, mul_assoc, sqrt_eq_one A hdiag]
    simp only [mul_one]
  rw [add_sub]
  simp only [sub_left_inj]
  exact one_add_one_eq_two


-- ============ 命题中主要引理 ====================
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

-- A is Hermitian
lemma A_isHermitian
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hA_symm : Aᵀ = A)
  :
  A.IsHermitian
  := by
  exact hA_symm

-- all eigenvalues of A are realnum
lemma A_all_real_eigenvalue
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hA_symm : Aᵀ = A)
  :
  has_all_real_eigenvalues A
  := by
  unfold has_all_real_eigenvalues
  intro t ht

  sorry

-- Posdef matrix ↔ all eigenvalues are positive
lemma Matrix.PosDef_iff_spectrum_pos
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0)
  (hA_symm : Aᵀ = A)
  :
  A.PosDef ↔ ∀ c ∈ spectrum ℂ (complexify A), c.re > 0
  := by
  constructor
  .
    intro hh c hc
    sorry
  .
    intro hc
    rw [Matrix.PosDef.posDef_iff_eq_conjTranspose_mul_self]
    rw [Matrix.IsHermitian.spectral_theorem hA_symm]
    let P : Matrix (Fin n) (Fin n) ℝ := (IsHermitian.eigenvectorUnitary hA_symm)
    use (sqrtdiagPart A) * Pᵀ
    constructor
    .
      have A_sqrtPart_unit : IsUnit (sqrtdiagPart A).det := by

        sorry

      sorry
    . sorry

lemma A_Pos
  (A : Matrix (Fin n) (Fin n) ℝ)
  (b x0 : (Fin n) → ℝ)
  (hdiag : ∀ i, A i i > 0)
  (h_symm : A.IsSymm)
  :
  A.PosDef ↔ ∀ c ∈ spectrum ℂ (complexify ((negsqrtdiagPart A)*((negsqrtdiagPart A) * A * (negsqrtdiagPart A)) *(sqrtdiagPart A))), c.re > 0
  := by
  sorry

-- ============= 命题 bodypart =========================
-- 里面还有一个重要的等价命题没有整合
-- Jacobi_iterative_converges A ↔ A.PosDef ∧ (2 • D - A).PosDef
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
    sorry --ke

  rw [eignevalue_gt_zero_iff_pos]
