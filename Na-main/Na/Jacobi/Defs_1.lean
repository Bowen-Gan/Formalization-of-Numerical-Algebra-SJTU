import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib
import Na.Defs

open Matrix
open scoped ENNReal

noncomputable section Norm
-----定义各种范数
#check Matrix.frobeniusSeminormedAddCommGroup



/-- 向量 ℓ∞ 范数：max_i |x i| -/
noncomputable def vecInftyNorm {ι : Type*} [Fintype ι][Nonempty ι] (x : ι → ℝ) : ℝ :=
  norm x

notation:100 "‖" x "‖_vec∞" => vecInftyNorm x
------正定矩阵范数

end Norm


#check Invertible
--------定理4.2.4，首先先定理G——S迭代算法的矩阵

variable {α : Type*} [Field α] {A : {X : Matrix (Fin n) (Fin n) α // ∀ i, X i i ≠ 0}} {b x0 : (Fin n) → α}
noncomputable def G_S {α : Type*} {n : ℕ} [Field α] (A : {X : Matrix (Fin n) (Fin n) α // ∀ i, X i i ≠ 0})
    (b : (Fin n) → α) (x0 : (Fin n) → α) : Stationary_iterative x0 :=
  {
    M := ((A.1).diagPart+(A.1).lowerPart)⁻¹ * -((A.1).upperPart)
    g := ((A.1).diagPart+(A.1).lowerPart)⁻¹ *ᵥ b
  }

-----G_S迭代
lemma G_S.update (alg : Stationary_iterative x0) (halg : alg = G_S A b x0) (p : ℕ) :
    alg.x (p + 1) = alg.M *ᵥ (alg.x p) + alg.g := rfl

-----------------定理4.2.4证明------------------------------
-----准备工作：先写出B和L₁矩阵，再写u_i,l_i,μ的定义
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ )
/-- Jacobi 迭代矩阵 B -/
noncomputable def B  : Matrix (Fin n) (Fin n) ℝ :=
  (A.diagPart)⁻¹ * (A.diagPart - A)

#check LinftyNorm B
/-- G-S 迭代矩阵 L₁ -/
noncomputable def L₁ : Matrix (Fin n) (Fin n) ℝ :=
  ((A.diagPart + A.lowerPart)⁻¹ * (- A.upperPart))
------l A i 来表示l_i---再证明l非负
noncomputable def l (i : Fin n) : ℝ :=
  ∑ j : Fin n, if j < i then |B A i j| else 0

lemma l_nonneg (i : Fin n) : 0 ≤ l A i := by
    unfold l
    apply Finset.sum_nonneg
    intro j _; split_ifs <;>
    simp

/-- u_i = ∑_{j > i} |B i j| -/--再证明u非负-/
noncomputable def u (i : Fin n) : ℝ :=
  ∑ j : Fin n, if j > i then |B A i j| else 0

lemma u_nonneg (i : Fin n) : 0 ≤ u A i := by
    unfold u
    apply Finset.sum_nonneg
    intro j _; split_ifs <;>
    simp


noncomputable def μ (A : Matrix (Fin n) (Fin n) ℝ) [NeZero n]: ℝ :=
  have h : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
  Finset.max' (Finset.univ.image (fun i : Fin n => u A i / (1 - l A i))) (by simp [h])

------可以开始证第一个引理，μ<1
lemma μ_lt_one [NeZero n](i : Fin n)(h : ∀ i : Fin n, l A i + u A i < 1) :
    μ A < 1 := by
  have h1 :∀ i : Fin n, 0 < 1 - l A i := by intro i ;linarith[h i,u_nonneg A i]
  have h2 :∀ i : Fin n,u A i ≤ 1 - l A i := by intro i;linarith [h i]
  have h2' : u A i < 1 - l A i := by linarith [h i, u_nonneg A i, l_nonneg A i]
  have step1 :∀ i : Fin n, (l A i + u A i )-(u A i) / (1 - l A i)  ≥ 0 := by
    have t₁ :∀ i : Fin n,(l A i + u A i) - (u A i) / (1 - l A i)=(1-l A i - u A i)*l A i/(1 - l A i):=by
      intro i
      calc
      (l A i + u A i) - (u A i) / (1 - l A i)=((l A i + u A i)*(1-l A i)-u A i)/(1 - l A i):=by
        have denom_ne : 1 - l A i ≠ 0 := by linarith [h1 i]
        field_simp [denom_ne]
      _=(1-l A i - u A i)*l A i/(1 - l A i) :=by ring
    intro i
    rw[t₁]
    have num_nonneg :∀ i : Fin n, (1 - l A i - u A i) * l A i ≥ 0 := by
     intro i
     apply mul_nonneg
     · exact sub_nonneg_of_le (h2 i)      -- 1 - l A i - u A i ≥ 0
     · exact l_nonneg A i   -- l A i ≥ 0
    apply div_nonneg
    exact num_nonneg i
    exact le_of_lt (h1 i)
  have step2 : ∀ i : Fin n,(u A i) / (1 - l A i) ≤ (l A i + u A i) :=by
    intro i;
    exact sub_nonneg.mp (step1 i)
  have step3 : ∀ i : Fin n,u A i / (1 - l A i) < 1 := by
    intro i
    exact lt_of_le_of_lt (step2 i) (h i)
  unfold μ
  simp only [Finset.max'_lt_iff, Finset.mem_image]
  intro r hr
  rcases hr with ⟨i, _, hi⟩
  exact lt_of_eq_of_lt (id (Eq.symm hi)) (step3 i)

----------证明L₁的无穷范数小于1------
#check norm
#check L₁
open scoped Matrix BigOperators
open Matrix Finset
open NNReal
open scoped ENNReal NNReal
#check LinftyNorm
#check linfty_opNorm_def
#check sup'_univ_eq_ciSup
--   norm f := ↑(Finset.univ.sup fun b => ‖f b‖₊)
-----‖A‖ = ((Finset.univ : Finset m).sup fun i : m => ∑ j : n, ‖A i j‖₊ : ℝ≥0)
/-- 定理：存在单位向量 x 使得 ‖A x‖_∞ = ‖A‖_∞ -/

theorem exists_unit_vec_reaches_LinftyNorm [NeZero n](hA : A ≠ 0):
    ∃ (x : (Fin n → ℝ))  ,
      ‖x‖_vec∞=1 ∧ ‖(A *ᵥ x)‖_vec∞  = LinftyNorm A := by
  -- 取使第 k 行 1-范数最大的行号 k
  -- 取使第 i 行 1-范数最大的行号 i
  have h_exists : ∃ i ∈ (Finset.univ : Finset (Fin n)),
  (Finset.univ : Finset (Fin n)).sup' (Finset.univ_nonempty) (fun i => ∑ j : Fin n, |A i j|) =
      (fun i => ∑ j : Fin n, |A i j|) i := by
    apply Finset.exists_mem_eq_sup'
-- 提取这个行号
  let k : Fin n := Classical.choose h_exists
  rcases Classical.choose_spec h_exists with ⟨hk_mem, hk_eq⟩
  have hk2 : ∀ i : Fin n, ∑ l, |A i l| ≤ ∑ l, |A k l| := by
    intro i
    have h1 : (fun i => ∑ l, |A i l|) i ≤ (fun i => ∑ l, |A i l|) k := by
      have h_le : (fun i => ∑ l, |A i l|) i ≤ Finset.univ.sup' (Finset.univ_nonempty) (fun i => ∑ l, |A i l|) := by
        apply Finset.le_sup' _ (Finset.mem_univ i)
      rwa [hk_eq] at h_le
    exact h1
  -- 构造 x 为第 k 行的符号向量
  let x : Fin n → ℝ := fun j => Real.sign (A k j)
  use x
  simp [vecInftyNorm, x, norm]
  constructor-----分开证明‖x‖_∞ = 1和‖(A *ᵥ x)‖_vec∞  = LinftyNorm A
----- 验证 ‖x‖_∞ = 1
  have h_max : ↑(Finset.univ.sup fun i => ‖x i‖₊)  = 1 := by
    apply le_antisymm
-------≤1
    simp only [Finset.sup_le_iff, NNReal.coe_le_one]
    intro i _
    simp [x]
    unfold Real.sign
    split_ifs <;> norm_num
-- -- 证明 ≥ 1
    have h_exists_j : ∃ j : Fin n, A k j ≠ 0 := by
      by_contra h
      push_neg at h
      have t1 : ∑ j : Fin n, |A k j| = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        simp [h j]
      have t2 : ∀ i : Fin n, ∑ l, |A i l| = 0 := by
        intro i
        have h_le : ∑ l, |A i l| ≤ ∑ l, |A k l| := hk2 i
        rw [t1] at h_le
        exact le_antisymm h_le (Finset.sum_nonneg fun l _ => abs_nonneg (A i l))
      have hA_zero : A = 0 := by
        ext i j
        have h_ij : ∑ l, |A i l| = 0 := t2 i
        have : |A i j| = 0 := by
          have h_nonneg : 0 ≤ |A i j| := abs_nonneg _
          have h_le : |A i j| ≤ ∑ l, |A i l| := by
            apply Finset.single_le_sum (fun l _ => abs_nonneg (A i l))
            simp
          rw [h_ij] at h_le
          linarith
        simp at this
        exact this
      contradiction
    rcases h_exists_j with ⟨j, hj⟩
    have h1 : 1 ≤ Finset.univ.sup fun i => ‖x i‖₊ := by
      have h2 : 1 ≤ ‖x j‖₊ := by
        simp [x]
        unfold Real.sign
        split_ifs with h_pos h_neg <;> norm_num
        have : A k j = 0 := by linarith
        contradiction
      have h3 : ‖x j‖₊ ≤ Finset.univ.sup (fun i : Fin n => ‖x i‖₊) := by
        apply Finset.le_sup (f := fun i : Fin n => ‖x i‖₊) (Finset.mem_univ j)
      exact le_trans h2 h3
    exact_mod_cast h1
  exact h_max
  simp [LinftyNorm, linfty_opNorm_def]
  have h1 : ∀ i : Fin n, |(A *ᵥ x) i| ≤ ∑ l, |A i l| := by
    intro i
    calc
      |(A *ᵥ x) i|
        = |∑ l, A i l * Real.sign (A k l)| := by simp [mulVec, dotProduct, x]
      _ ≤ ∑ l, |A i l * Real.sign (A k l)| := by apply Finset.abs_sum_le_sum_abs
      _ = ∑ l, |A i l| * |Real.sign (A k l)| := by simp_rw [abs_mul]
      _ ≤ ∑ l, |A i l| * 1 := by
          apply Finset.sum_le_sum
          intro l _
          have : |Real.sign (A k l)| ≤ 1 := by
            unfold Real.sign
            split_ifs
            <;>norm_num
          gcongr
      _ = ∑ l, |A i l| := by simp
------- 对 k 行，恰好取到等号
  have h2 : |(A *ᵥ x) k| = ∑ l, |A k l| := by
    calc
      |(A *ᵥ x) k|
        = |∑ l, A k l * Real.sign (A k l)| := by simp [mulVec, dotProduct, x]
      _ = ∑ l, |A k l| := by
        have h : ∀ l, A k l * Real.sign (A k l) = |A k l| := by
          intro l
          simp [Real.sign]
          split_ifs <;> simp [abs];linarith;
          (expose_names; exact le_of_lt h_1)
          have h_zero : A k l = 0 := by
            simp at *
            linarith
          rw [h_zero]
          norm_num
        simp_rw [h];simp;refine Fintype.sum_nonneg ?_;apply abs_nonneg

  have h3 : (univ.sup fun b => ‖(A *ᵥ x) b‖₊) = univ.sup fun i => ∑ j, ‖A i j‖₊ := by
    apply le_antisymm
  --------------验证左边小于右边
    apply Finset.sup_le
    intro b
    have h31: ‖(A *ᵥ x) b‖₊ ≤  ∑ j, ‖A b j‖₊:= by
      calc
        ‖(A *ᵥ x) b‖₊
          = |(A *ᵥ x) b|:=rfl
        _ ≤ ∑ l, |A b l| :=by apply h1
        _ = ∑ j, ‖A b j‖₊ := by exact Eq.symm (NNReal.coe_sum univ fun i => ‖A b i‖₊)
    exact fun a => le_sup_of_le a h31
  -------------验证右边小于左边
    apply Finset.sup_le
    intro b
    have h32:∑ j, ‖A b j‖₊ ≤ |(A *ᵥ x) k|:=by
      calc
        ∑ j, ‖A b j‖₊= ∑ j, |A b j| := by exact NNReal.coe_sum univ fun i => ‖A b i‖₊
        _≤ ∑ l, |A k l| := by exact hk2 b
        _= |(A *ᵥ x) k| := by exact id (Eq.symm h2)
    exact fun a => le_sup_of_le hk_mem h32
  exact h3

--------------------公式4.2.11
-- noncomputable def L₁ : Matrix (Fin n) (Fin n) ℝ :=
--   ((A.diagPart + A.lowerPart)⁻¹ * (- A.upperPart))
-- ------l A i 来表示l_i---再证明l非负
-- noncomputable def l (i : Fin n) : ℝ :=
--   ∑ j : Fin n, if j < i then |B A i j| else 0


  -- have h1 : (j : ℕ) = (i : ℕ) := by (expose_names; exact congrArg Fin.val h_1)
            -- have h2 : (j : ℕ) < (i : ℕ) := by exact hh
            -- omega
            -- have h_not_le : ¬(i : ℕ) ≤ (j : ℕ) := by
            --    (expose_names; exact h_2)
            -- apply?
lemma cal_of_4211
    [NeZero n](hdiag : ∀ i, A i i ≠ 0) (x y : Fin n → ℝ)(h : y = (L₁ A) *ᵥ x)  :
     y = (-(A.diagPart)⁻¹ *A.lowerPart )*ᵥ y -((A.diagPart)⁻¹* A.upperPart) *ᵥ x := by
  have h₁: L₁ A =-(A.diagPart)⁻¹*A.lowerPart* (L₁ A)-(A.diagPart)⁻¹* A.upperPart :=by
    have h_def : L₁ A = (A.diagPart + A.lowerPart)⁻¹ * (- A.upperPart) := by
      simp [L₁]
    have h_mul : (A.diagPart + A.lowerPart) * (L₁ A) = - A.upperPart := by
      rw [h_def]
      have h_inv : (A.diagPart + A.lowerPart) * (A.diagPart + A.lowerPart)⁻¹ = 1 := by
          sorry-----在超松弛迭代组有证明
      simp
      rw[←mul_assoc];simp[h_inv]
    have h_expand : A.diagPart * (L₁ A) + A.lowerPart * (L₁ A) = - A.upperPart := by
      have h_eq : (A.diagPart + A.lowerPart) * (L₁ A) = A.diagPart * (L₁ A) + A.lowerPart * (L₁ A) := by
        rw [add_mul]
      rw [h_eq] at h_mul
      exact h_mul
    have h_inv2 : (A.diagPart)⁻¹ *  A.diagPart= 1 := by
      have h_unit : IsUnit (A.diagPart) := Matrix.diagnonzero_diagInvertable A hdiag
      have h_inv : Invertible (A.diagPart) := h_unit.invertible
      rw [← invOf_eq_nonsing_inv]
      simp [invOf_mul_self]
    have h_final : L₁ A = -(A.diagPart)⁻¹ * A.lowerPart * (L₁ A) - (A.diagPart)⁻¹ * A.upperPart := by
      calc
        L₁ A = (A.diagPart)⁻¹ * (A.diagPart * (L₁ A)) := by
          rw[←mul_assoc];simp[h_inv2]
        _ = (A.diagPart)⁻¹ * (A.diagPart * (L₁ A)+A.lowerPart * (L₁ A)-A.lowerPart * (L₁ A)) := by
          simp
        _ =(A.diagPart)⁻¹ *((-A.upperPart) +(-A.lowerPart) * (L₁ A) ) := by
          rw[h_expand];rw [sub_eq_add_neg];simp
        _ = (A.diagPart)⁻¹ *(- A.upperPart) +(A.diagPart)⁻¹ * (-A.lowerPart) * (L₁ A)  := by
           rw [mul_neg];rw [mul_add];rw [mul_neg, mul_neg];rw [← neg_mul, ← neg_mul];simp;rw[mul_assoc]
        _ =-(A.diagPart)⁻¹ * A.lowerPart * (L₁ A) - (A.diagPart)⁻¹ * A.upperPart := by
           rw [neg_mul, neg_mul];simp;rw[add_comm];rw [sub_eq_add_neg]
    exact h_final
  calc
    y=(L₁ A) *ᵥ x := h
    _=(-(A.diagPart)⁻¹*A.lowerPart* (L₁ A)-(A.diagPart)⁻¹* A.upperPart )*ᵥ x := by
      exact congrFun (congrArg mulVec h₁) x
    _=(-(A.diagPart)⁻¹*A.lowerPart* (L₁ A))*ᵥ x-((A.diagPart)⁻¹* A.upperPart) *ᵥ x:= by
      exact sub_mulVec (-A.diagPart⁻¹ * A.lowerPart * L₁ A) (A.diagPart⁻¹ * A.upperPart) x
    _=(-(A.diagPart)⁻¹*A.lowerPart)*ᵥ ((L₁ A)*ᵥ x)-((A.diagPart)⁻¹* A.upperPart) *ᵥ x:= by simp
    _=(-(A.diagPart)⁻¹ *A.lowerPart )*ᵥ y -((A.diagPart)⁻¹* A.upperPart) *ᵥ x := by
      exact congrFun (congrArg HSub.hSub (congrArg (-A.diagPart⁻¹ * A.lowerPart).mulVec (id (Eq.symm h))))
        ((A.diagPart⁻¹ * A.upperPart) *ᵥ x)


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

-- 1. (D_sqrt_inv A) * (D_sqrt A) = 1
lemma D_sqrt_inv_mul_self (A : Matrix (Fin n) (Fin n) ℝ) (hdiag : ∀ i, A i i > 0) :
    (D_sqrt_inv A) * (D_sqrt A) = 1 := by
  have h₂₀ :∀ i, √(A i i) ≠ 0 := by
    intro i
    have h_pos : A i i > 0 := hdiag i
    positivity
  ext i j
  simp [D_sqrt_inv, D_sqrt, mul_apply, Finset.mem_univ, if_pos, if_neg]
  <;> try aesop
  <;> try positivity
  <;> try field_simp [Real.sqrt_pos.mpr (hA i), Real.sq_sqrt (by linarith : (0 : ℝ) ≤ A i i)]
  <;> try aesop

lemma D_sqrt_inv_eq
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hdiag : ∀ i, A i i > 0) :
  (D_sqrt A)⁻¹ = D_sqrt_inv A := by
  refine inv_eq_left_inv ?_
  exact D_sqrt_inv_mul_self A hdiag

lemma D_sqrt_inv_symm {n : Nat}
  (D : Matrix (Fin n) (Fin n) ℝ) :
  (D_sqrt_inv D)ᵀ = D_sqrt_inv D:= by
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

lemma cal_of_M  (A : Matrix (Fin n) (Fin n) ℝ)  (b x0 : (Fin n) → ℝ) (hdiag : ∀ i, A i i > 0):
     (Jacobi A (fun i ↦ ne_of_gt (hdiag i)) b x0).M=
     (D_sqrt_inv A)*(1-(D_sqrt_inv A)*A*(D_sqrt_inv A))*(D_sqrt A) :=by
  have h₀ : ∀ i, A i i ≠ 0 := by exact fun i => Ne.symm (ne_of_lt (hdiag i))
  have h₁ : IsUnit A.diagPart := by exact Matrix.diagnonzero_diagInvertable A h₀
  calc
    (Jacobi A (fun i ↦ ne_of_gt (hdiag i)) b x0).M=(A.diagPart)⁻¹ * (A.diagPart - A):= by
      simp [Jacobi]
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
    (D_sqrt_inv A)*(2-(D_sqrt_inv A)*A*(D_sqrt_inv A))*(D_sqrt A)= 1+(Jacobi A (fun i ↦ ne_of_gt (hdiag i)) b x0).M
     := by
  have hM : (Jacobi A (fun i ↦ ne_of_gt (hdiag i)) b x0).M =
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
    _ =1 + (Jacobi A (fun i ↦ ne_of_gt (hdiag i)) b x0).M := by rw[hM]

lemma cal_of_I_minus_M  (A : Matrix (Fin n) (Fin n) ℝ)  (b x0 : (Fin n) → ℝ) (hdiag : ∀ i, A i i > 0):
     1-(Jacobi A (fun i ↦ ne_of_gt (hdiag i)) b x0).M=(D_sqrt_inv A)*((D_sqrt_inv A)*A*(D_sqrt_inv A))*(D_sqrt A)
     := by
  calc
    1-(Jacobi A (fun i ↦ ne_of_gt (hdiag i)) b x0).M
     =1-(D_sqrt_inv A) * (1 - (D_sqrt_inv A) * A * (D_sqrt_inv A)) * (D_sqrt A):=by
      simp; exact cal_of_M A b x0 hdiag
    _=1-(1-(D_sqrt_inv A) * ( (D_sqrt_inv A) * A * (D_sqrt_inv A)) * (D_sqrt A)):= by
      have t : 1-(D_sqrt_inv A) * ( (D_sqrt_inv A) * A * (D_sqrt_inv A)) * (D_sqrt A)
        =(D_sqrt_inv A) * (1 - (D_sqrt_inv A) * A * (D_sqrt_inv A)) * (D_sqrt A) :=by
        rw[mul_sub,sub_mul,mul_one];simp[D_sqrt_inv_mul_self A hdiag]
      simp[t]
    _=(D_sqrt_inv A)*((D_sqrt_inv A)*A*(D_sqrt_inv A))*(D_sqrt A) := by simp


-- #check PosDef
 #check PosDef.conjTranspose_mul_mul_same
-- #check PosDef.eigenvalues_pos
-- #check Matrix.PosSemidef.transpose
-- #check Matrix.PosDef.of_toQuadraticForm'
-- #check Matrix.det_add_mul
#check Module.End.hasEigenvalue_iff_mem_spectrum
-- #check Module.End.isRoot_of_hasEigenvalue
-- #check Matrix.charpoly
-- #check Matrix.det_conj
-- #check Matrix.det_eq_prod_roots_charpoly
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
  let D1 : Matrix (Fin n) (Fin n) ℝ := fun i j ↦ if i = j then Real.sqrt (D i j) else 0
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
  have hPt_unit : IsUnit Pᵀ := by apply?
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







-- end iterative_method
