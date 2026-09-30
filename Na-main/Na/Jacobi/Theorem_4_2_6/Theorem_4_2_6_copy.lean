import Mathlib
import Na.Defs

open Matrix

section
variable {n : Nat} {A : Matrix (Fin n) (Fin n) ℝ}

--
def Jacobi_iterative_converges (A : Matrix (Fin n) (Fin n) ℝ) : Prop := by
  sorry

#check Matrix.IsSymm
#check Matrix.transpose
#check Matrix.transpose_mul
#check Matrix.diag_transpose
#check Matrix.ext_iff
#check PosDef
#check Matrix.IsSymm


def twoD_minus_A (A : Matrix (Fin n) (Fin n) ℝ) :=
  2 • A.diagPart - A

-- 取出 A 的对角阵 D
def A_diag (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then A i i else 0

-----取出任意矩阵的对角矩阵的1/2幂次
noncomputable def D_sqrt (D : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ if i = j then Real.sqrt (D i i) else 0


-----取出任意矩阵的对角矩阵的-1/2幂次
noncomputable def D_sqrt_inv (D : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ if i = j then 1 / Real.sqrt (D i i) else 0

------证明上述方法取出来的矩阵是对角阵
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

-- -- 1. (D_sqrt_inv A) * (D_sqrt A) = 1
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

-- addition lemma

-- 计算 D^1/2 逆 = D^-1/2
lemma D_sqrt_inv_eq (A : Matrix (Fin n) (Fin n) ℝ) (hdiag : ∀ i, A i i > 0) : (D_sqrt A)⁻¹ = D_sqrt_inv A := by
  refine inv_eq_left_inv ?_
  exact D_sqrt_inv_mul_self A hdiag

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


lemma cal_of_M  (A : Matrix (Fin n) (Fin n) ℝ) (b x0 : (Fin n) → ℝ) (hdiag : ∀ i, A i i > 0):
(Jacobi ⟨A, fun i ↦ ne_of_gt (hdiag i)⟩ b x0).M= (D_sqrt_inv A)*(1-(D_sqrt_inv A)*A*(D_sqrt_inv A))*(D_sqrt A) :=by
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

----- D^(-1/2)对称
lemma D_sqrt_inv_symm {n : Nat} (D : Matrix (Fin n) (Fin n) ℝ) : (D_sqrt_inv D)ᵀ = D_sqrt_inv D:= by
    apply Matrix.ext_iff.1
    intro i j
    by_cases h : i = j
    . calc
        (D_sqrt_inv D)ᵀ i j = (D_sqrt_inv D)ᵀ i i := by
          exact congrArg ((D_sqrt_inv D)ᵀ i) (id (Eq.symm h))
        _ = D_sqrt_inv D i i := by
          exact rfl
        _ = D_sqrt_inv D i j := by
          exact congrArg (D_sqrt_inv D i) h
    . calc
        (D_sqrt_inv D)ᵀ i j = 0 := by
          unfold D_sqrt_inv
          simp only [one_div, transpose_apply, ite_eq_right_iff, inv_eq_zero]
          exact fun a => False.elim (h (id (Eq.symm a)))
        _ = D_sqrt_inv D i j := by
          unfold D_sqrt_inv
          exact Eq.symm (if_neg h)

-- I - D_sqrt_inv D * A * D_sqrt_inv D 是对称矩阵
lemma symmetric1 (A : Matrix (Fin n) (Fin n) ℝ) (hA_symm : Aᵀ = A) (D : Matrix (Fin n) (Fin n) ℝ): Matrix.IsSymm (1 - D_sqrt_inv D * A * D_sqrt_inv D) := by
    unfold Matrix.IsSymm
    calc
      (1 - D_sqrt_inv D * A * D_sqrt_inv D)ᵀ = 1 - (D_sqrt_inv D * A * D_sqrt_inv D)ᵀ := by
        simp only [transpose_sub, transpose_one, transpose_mul]
      _ = 1 - (D_sqrt_inv D)ᵀ * (D_sqrt_inv D * A)ᵀ := by
        simp only [transpose_mul]
      _ = 1 - (D_sqrt_inv D)ᵀ * (A)ᵀ * (D_sqrt_inv D)ᵀ := by
        rw [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 - D_sqrt_inv D * (A)ᵀ * D_sqrt_inv D := by
        rw [D_sqrt_inv_symm]
      _ = 1 - D_sqrt_inv D * A * D_sqrt_inv D := by
        rw [hA_symm]

#check Matrix.inv_def
#check Matrix.PosDef.eigenvalues_pos
#check Matrix.finite_spectrum

-- ============================================================== -

--! 将实矩阵复数化
def complexify (B : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.map B (↑)  -- 将每个实数元素通过强制转换嵌入复数

-- 定义相似矩阵
def Matrix.Similar (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin n) ℝ) := ∃ (P : Matrix (Fin n) (Fin n) ℝ), B = P⁻¹ * A * P

--! I - D_sqrt_inv D * A * D_sqrt_inv D 与 B 相似
lemma similar_to_B (A : Matrix (Fin n) (Fin n) ℝ) (hdiag : ∀ i, A i i > 0)  (h_eq_S : S = 1 - D_sqrt_inv A * A * D_sqrt_inv A) (hcalc_B : B = (D_sqrt_inv A) * (1 - (D_sqrt_inv A) * A * (D_sqrt_inv A)) * (D_sqrt A)) : Matrix.Similar S B := by
  use D_sqrt A
  rw [h_eq_S]
  rw [hcalc_B]
  rw [D_sqrt_inv_eq A hdiag]

-- 相似矩阵有相同特征值
theorem SimilarMatrix_eq_eigenvalues (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin n) ℝ) : Matrix.Similar A B → spectrum ℂ (complexify A) = spectrum ℂ (complexify B) := by
  sorry

#check Matrix.IsHermitian.eigenvalues_mem_spectrum_real
#check spectralRadius
#check Set.univ
#check spectrum.map_polynomial_aeval
#check NNReal
#check ENNReal
#check spectrum.mem_iff
#check Module.End.HasEigenvalue  -- 检查定义
#check Matrix.IsHermitian.eigenvalues_eq_spectrum_real

open Polynomial
variable {t : ℂ}



--! 定义所有特征值都是实数
def has_all_real_eigenvalues (B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
∀ t ∈ spectrum ℂ (complexify B), t.im = 0

-- 矩阵特征值
lemma Matrix.eignevalue (B : Matrix (Fin n) (Fin n) ℝ): t ∈ spectrum ℂ (complexify B) ↔ ∃ x : Fin n → ℂ , (complexify B) *ᵥ x = t • x := by
  sorry


--! B 的特征值都是实数 → 1 + B 的特征值都是实数
lemma Matrix.eignevalue_add (B : Matrix (Fin n) (Fin n) ℝ) : has_all_real_eigenvalues (1 + B) := by
  sorry

--! B 的特征值都是实数 → 1 - B 的特征值都是实数
lemma Matrix.eignevalue_sub (B : Matrix (Fin n) (Fin n) ℝ) (hspec_real : has_all_real_eigenvalues B) : has_all_real_eigenvalues (1 - B) := by
  sorry

--! 1 + B 的特征值 t 可以表示为 1 + t'
lemma spectrum_trans_by_add (B : Matrix (Fin n) (Fin n) ℝ) (hspec_real : has_all_real_eigenvalues B) : ∀ t ∈ spectrum ℂ (complexify (1 + B)), ∃ t' ∈ spectrum ℂ (complexify B), t = 1 + t' := by
  sorry
#check Mathlib.Tactic.LinearCombination'.neg_pf
#check map_neg

--! 1 - B 的特征值 t 可以表示为 1 - t'
lemma spectrum_trans_by_sub (B : Matrix (Fin n) (Fin n) ℝ): ∀ t ∈ spectrum ℂ (complexify (1 - B)), ∃ t' ∈ spectrum ℂ (complexify B), t = 1 - t' := by
  sorry

#check ENNReal.coe_lt_coe
#check le_ciSup
#check le_iSup₂_of_le

def is_real (z : ℂ) : Prop := z.im = 0

lemma cast_injective (r : ℂ) (h : is_real r) : ↑(r.re) = r :=
  Complex.ext rfl (by rw [Complex.ofReal_im, h])

--! 由谱集的上确界 < 1，得到每个特征值都 < 1
lemma abs_lt_one (B : Matrix (Fin n) (Fin n) ℝ) (hspec_real : has_all_real_eigenvalues B) (h1 : ⨆ k ∈ spectrum ℂ (complexify B), (↑‖k‖₊ : ENNReal) < 1) (hr' : r' ∈ spectrum ℂ (complexify B)) : ‖r'‖₊ < 1 := by
  sorry

--! 特征值均为实数，则谱半径 < 1 → I - B, I + B 特征值均非负
lemma spectrum_le_one_imply_eginevalue_ge_zero (B : Matrix (Fin n) (Fin n) ℝ) (hspec_real : has_all_real_eigenvalues B): spectralRadius ℂ (complexify B) < 1 → (∀ t ∈ spectrum ℂ (complexify (1 + B)), t.re > 0) ∧ (∀ t ∈ spectrum ℂ (complexify (1 - B)), t.re > 0) := by
  sorry

-- I + B、I - B 全部特征值非负 → 矩阵谱半径 < 1
lemma eginevalue_gt_zero_imply_spectrum_le_one (B : Matrix (Fin n) (Fin n) ℝ) (hspec_real : spectrum ℝ B ⊆ (Set.univ : Set ℝ)): (∀ t ∈ spectrum ℝ (1 + B), t > 0) ∧ (∀ t ∈ spectrum ℝ (1 - B), t > 0) → spectralRadius ℝ B < 1 := by
  sorry

--
theorem four_two_six (A : Matrix (Fin n) (Fin n) ℝ) (hdiag : ∀ i, A i i > 0) (hA_symm : Aᵀ = A) : Jacobi_iterative_converges A ↔ PosDef A ∧ PosDef (twoD_minus_A A) := by

  sorry
