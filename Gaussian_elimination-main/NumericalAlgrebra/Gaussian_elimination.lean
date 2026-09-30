import Mathlib

variable {α : Type*}

open Matrix Equiv Nat List

section Basic

variable {n m} (M : Matrix (Fin n) (Fin m) α)


def swap_rows (i j : Fin n) : Matrix (Fin n) (Fin m) α :=
    M.submatrix (swap i j : Perm (Fin n)) id

lemma swap_rows_eq_zero_iff_eq_zero [Zero α] (i j)  :
  swap_rows M i j = 0 ↔ (M : Matrix (Fin n) (Fin m) α) = 0 := by
  constructor
  · unfold swap_rows
    intro h
    have : (M.submatrix (⇑(Equiv.swap i j)) id ).submatrix (⇑(Equiv.swap i j)) id = M := by
      simp
      have : ⇑(Equiv.swap i j) ∘ ⇑(Equiv.swap i j) = id := by
        ext x
        simp
      rw [this]
      simp
    rw [← this]
    calc
      _ = (0: Matrix (Fin n) (Fin m) α).submatrix (⇑(Equiv.swap i j)) id := congrFun (congrFun (congrArg submatrix h) ⇑(Equiv.swap i j)) id
      _ = 0 := by simp
  · intro h
    rw [h]
    simp [swap_rows]

@[simp] lemma swap_rows_self (i) : swap_rows M i i = M := by
  unfold swap_rows
  simp

@[simp] lemma swap_rows_involution (i j) : swap_rows (swap_rows M i j) i j = M := by
  unfold swap_rows
  simp
  have : ⇑(Equiv.swap i j) ∘ ⇑(Equiv.swap i j) = id := by ext x; simp
  rw [this]
  simp

lemma swap_rows_comm (i j) : (swap_rows M i j) = swap_rows M j i := by
  unfold swap_rows
  rw [Equiv.swap_comm]

def swap_cols  (i j : Fin m) : Matrix (Fin n) (Fin m) α :=
   (swap_rows M.transpose i j).transpose

def gaussian_update [Add α] [Mul α] [Sub α]
    (i k : Fin n) (a b : α) : (Fin m) → α :=
  if k ≤ i then M k else a • M k - b • M i

def gaussian_update_row [Add α] [Mul α] [Sub α]
  (i : Fin n) (j : Fin m):
  Matrix (Fin n) (Fin m) α :=
  fun k => gaussian_update M i k (M i j) (M k j)

end Basic

structure Gaussian (n m α) [Ring α] where
  P : Matrix (Fin n) (Fin n) α
  R : Matrix (Fin n) (Fin m) α
  Q : Matrix (Fin m) (Fin m) α
  M : Matrix (Fin n) (Fin m) α
  hm : P * M * Q = R
  -- P M Q = [I_r, 0;
            -- 0, 0]
namespace Gaussian

variable {n m : ℕ}

def transpose [CommRing α] (M : Gaussian n m α) : Gaussian m n α where
  P := M.Q.transpose
  R := M.R.transpose
  Q := M.P.transpose
  M := M.M.transpose
  hm := by
    rw [← M.hm, transpose_mul (M.P * M.M) M.Q, transpose_mul]
    apply Matrix.mul_assoc

@[simp] lemma transpose_transpose [CommRing α] (M : Gaussian n m α) :
  M.transpose.transpose = M := by
  unfold transpose
  rfl

lemma push_R_transpose [CommRing α] (M : Gaussian n m α) :
M.transpose.R = M.R.transpose := by rfl

variable [Ring α]

instance  : SMul (Matrix (Fin n) (Fin n) α) (Gaussian n m α) where
  smul := fun P B => (⟨P * B.P, P * B.R, B.Q, B.M, by simp [B.hm, Matrix.mul_assoc];⟩ : Gaussian n m α)

instance : SMul (Matrix (Fin m) (Fin m) α) (Gaussian n m α) where
  smul := fun Q B => (⟨B.P, B.R * Q, B.Q * Q, B.M, by rw [← B.hm]; simp [Matrix.mul_assoc];⟩ : Gaussian n m α)

/-- Unfolds smul to its def -/
lemma smul_def_right (B : Gaussian n m α) (Q : Matrix (Fin m) (Fin m) α):
  Q • B = (⟨B.P, B.R * Q, B.Q * Q, B.M, by rw [← B.hm]; simp [Matrix.mul_assoc];⟩ : Gaussian n m α)
  := rfl

/-- `(Q * P) • M = P • (Q • M)` -/
lemma mul_smul_right (M : Gaussian n m α)
  (P : Matrix (Fin m) (Fin m) α) (Q : Matrix (Fin m) (Fin m) α) : (Q * P) • M = P • (Q • M) := by
  rcases M with ⟨ MP, MR, MQ, MM, Mhm ⟩
  simp [smul_def_right, Matrix.mul_assoc]

/-- Unfolds smul to its def-/
lemma smul_def_left (P : Matrix (Fin n) (Fin n) α) (B : Gaussian n m α) :
  P • B = (⟨P * B.P, P * B.R, B.Q, B.M, by rw [← B.hm]; simp [Matrix.mul_assoc];⟩ : Gaussian n m α)
  := rfl

/-- `(P * Q) • M = P • (Q • M)` -/
lemma mul_smul_left (M: Gaussian n m α)
  (P : Matrix (Fin n) (Fin n) α) (Q : Matrix (Fin n) (Fin n) α) : (P * Q) • M = P • (Q • M) := by
  rcases M with ⟨ MP, MR, MQ, MM, Mhm ⟩
  simp [smul_def_left, Matrix.mul_assoc]

@[simp] lemma smul_eq_right (M : Gaussian n m α):
  (1 : Matrix (Fin m) (Fin m) α) • M = M := by
  rcases M with ⟨ MP, MR, MQ, MM, Mhm ⟩
  simp [smul_def_right]

@[simp] lemma smul_eq_left (M : Gaussian n m α):
  (1 : Matrix (Fin n) (Fin n) α) • M = M := by
  rcases M with ⟨ MP, MR, MQ, MM, Mhm ⟩
  simp [smul_def_left]

end Gaussian

section Gauss

section

def firstNonZeroIndex {m} [DecidableEq α] [Zero α] (u : Fin m → α) (i : Fin m):
    WithTop (Fin m) :=
  ((finRange m).rtake (m - i)) |>.find? (fun i => u i ≠ 0)

end

def find_pivot_col {n} [Lattice α][AddGroup α][DecidableLT α][NeZero n] (M : Fin n → α) (i : Fin n): Fin n :=
  (argmax (abs ∘ M) ((finRange n).rtake (n - i))).getD 0

variable {n m : ℕ}  [NeZero n] [NeZero m]

-- 目前进行到(i,j)，接下来选取按行来消元
def Gaussian.gaussian_elimination_step_row [CommRing α] (M : Gaussian n m α) (i : Fin n) (j : Fin m)
    : Gaussian n m α where
  P := fun k => gaussian_update M.P i k (M.R i j) (M.R k j)
  R := gaussian_update_row M.R i j
  Q := M.Q
  M := M.M
  hm := by
    funext k
    simp only [gaussian_update, gaussian_update_row, Matrix.mul_apply_eq_vecMul,
      Matrix.vecMul_vecMul, ← M.hm]
    split_ifs with h_le
    simp
    simp [sub_vecMul, Matrix.vecMul_smul, Matrix.vecMul_smul]

omit [NeZero n] [NeZero m] in
lemma Gaussian.push_R_gaussian_elimination_step_rowgaussian_elimination_step_row [CommRing α] (M : Gaussian n m α) (i : Fin n) (j : Fin m)
    : (M.gaussian_elimination_step_row i j).R = gaussian_update_row (M.R) i j
    := by rfl

omit [NeZero n] [NeZero m] in
@[simp] lemma Matrix.gaussian_elimination_step_col_R_eq_zero [CommRing α] (R : Matrix (Fin n) (Fin m) α)
  (i : Fin n) (j j' : Fin m) (h : j < j')
  : (gaussian_update_row Rᵀ j i)ᵀ i j' = 0 := by
  unfold gaussian_update_row gaussian_update
  simp
  split_ifs
  · omega
  · simp
    ring

/-
`gaussian_elimination_step_row` 的整体效果等价于
在原矩阵左侧乘以某个可逆矩阵
-/
omit [NeZero n] [NeZero m] in
lemma Gaussian.gaussian_elimination_step_row_eq_left_mul [Field α] (M : Gaussian n m α) (i : Fin n) (j : Fin m) (MR_ij_nonzero : M.R i j ≠ 0):
    ∃ (P : GL (Fin n) α), P.1 • M = M.gaussian_elimination_step_row i j := by
  let P₁ := M.P
  let R₁ := M.R
  let P₂ := (M.gaussian_elimination_step_row i j).P
  let R₂ := (M.gaussian_elimination_step_row i j).R
  let E : Matrix (Fin n) (Fin n) α := fun k => gaussian_update (1 : Matrix (Fin n) (Fin n) α) i k (M.R i j) (M.R k j)
  let E_inv : Matrix (Fin n) (Fin n) α := fun k => gaussian_update (1 : Matrix (Fin n) (Fin n) α) i k (-M.R i j) (M.R k j)

  have h₀ : E * P₁ = P₂ := by
    ext k l
    simp only [E, gaussian_update, mul_apply, ite_apply]
    split_ifs with hk
    · simp [Matrix.one_apply]
      simp [P₁, P₂, Gaussian.gaussian_elimination_step_row, gaussian_update]
      split_ifs
      rfl
    · simp [Pi.sub_apply, Pi.smul_apply, Matrix.one_apply, mul_comm]
      have : ∑ x, P₁ x l * ((if k = x then M.R i j else 0) - if i = x then M.R k j else 0)
        = ∑ x, ((if k = x then P₁ x l * (M.R i j) else 0) - (if i = x then P₁ x l * M.R k j else 0))  := by
        congr; ext z; split_ifs <;> ring
      rw [this, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
      simp
      simp [P₁, P₂, Gaussian.gaussian_elimination_step_row, gaussian_update]
      split_ifs
      simp [Pi.sub_apply, mul_comm]

  have h₁ : E * R₁ = R₂ := by
    have h1 : P₁ * M.M * M.Q = R₁ := M.hm
    have h2 : P₂ * (M.gaussian_elimination_step_row i j).M * (M.gaussian_elimination_step_row i j).Q = R₂ := (M.gaussian_elimination_step_row i j).hm
    have : (M.gaussian_elimination_step_row i j).M = M.M := by rfl
    rw [this] at h2
    have : (M.gaussian_elimination_step_row i j).Q = M.Q := by rfl
    rw [this, ← h₀, Matrix.mul_assoc E, Matrix.mul_assoc E (P₁ * M.M) M.Q, h1] at h2
    exact h2

  have E_diagonal_nonzero : ∀ i, E i i ≠ 0 := by
    intro j
    simp [E, gaussian_update]
    split_ifs with h_le
    simp
    have : i ≠ j := by exact Ne.symm (ne_of_not_le h_le)
    simp [this, MR_ij_nonzero]

  have E_lowertrangular : E.BlockTriangular ⇑OrderDual.toDual := by
    simp [E, BlockTriangular]
    intro k l k_lt_l
    simp [gaussian_update]
    have k_neq_l : k ≠ l := by exact Fin.ne_of_lt k_lt_l
    split_ifs with h
    exact one_apply_ne' (id (Ne.symm k_neq_l))
    simp; simp at h
    have : i < l := by exact lt_trans h k_lt_l
    have i_neq_l : i ≠ l := by exact Fin.ne_of_lt this
    simp [k_neq_l, i_neq_l]

  have E_det_nonzero : E.det ≠ 0 := by
    rw [Matrix.det_of_lowerTriangular]
    exact Finset.prod_ne_zero_iff.mpr fun a a_1 => E_diagonal_nonzero a
    apply E_lowertrangular

  have E_invertible : IsUnit E.det := by exact Ne.isUnit E_det_nonzero

  let P : GL (Fin n) α := E.nonsingInvUnit E_invertible
  use P
  simp [P, nonsingInvUnit, SMul.smul, HSMul.hSMul, gaussian_elimination_step_row]
  constructor
  · rw [h₀]; rfl
  · rw [h₁]; rfl

-- 目前进行到(i,j)，接下来选取列主元
def Gaussian.gaussian_elimination_pivot_row [Lattice α] [DecidableLT α] [CommRing α]
    (M : Gaussian n m α)  (i : Fin n) (j : Fin m) :
    Gaussian n m α :=
  -- 取出第j列，从第i行开始的最大元素的下标
  let z := (find_pivot_col (fun k => M.R k j) i)
  -- 如果最大元素的下标和本身一样，。。。
  if z = i then M
  else
    {
    P := swap_rows M.P z i
    R := swap_rows M.R z i
    Q := M.Q
    M := M.M
    hm := by
      funext k
      simp only [←M.hm]
      rfl
    }

omit [NeZero m] in
lemma Gaussian.gaussian_elimination_pivot_row_R [Lattice α] [DecidableLT α] [CommRing α]
    (M : Gaussian n m α)  (i : Fin n) (j : Fin m) :
  (M.gaussian_elimination_pivot_row i j).R =swap_rows M.R (find_pivot_col (fun k => M.R k j) i) i
  := by
  unfold gaussian_elimination_pivot_row
  simp
  split_ifs
  · expose_names
    rw [h]
    simp [swap_rows]
  · simp

/-
`gaussian_elimination_pivot_row` 的整体效果等价于
在原矩阵左侧乘以某个可逆矩阵
-/
omit [NeZero m] in
lemma Gaussian.gaussian_elimination_pivot_row_eq_left_mul [Lattice α] [DecidableLT α] [CommRing α] (M : Gaussian n m α)  (i : Fin n) (j : Fin m) :
    ∃ (P : GL (Fin n) α), P.1 • M = M.gaussian_elimination_pivot_row i j := by
  let P₁ := M.P
  let R₁ := M.R
  let P₂ := (M.gaussian_elimination_pivot_row i j).P
  let R₂ := (M.gaussian_elimination_pivot_row i j).R
  let z := (find_pivot_col (fun k => M.R k j) i)
  have hz : z = find_pivot_col (fun k => M.R k j) i := by rfl
  let E : Matrix (Fin n) (Fin n) α := swap_rows (1 : Matrix (Fin n) (Fin n) α) z i
  have hE : E = swap_rows (1 : Matrix (Fin n) (Fin n) α) z i := by rfl

  have swap_self : swap_rows (1 : Matrix (Fin n) (Fin n) α) i i = 1 := by
    ext k l
    simp [swap_rows]
    exact rfl

  have h₀ : E * P₁ = P₂ := by
    simp [P₁, P₂, gaussian_elimination_pivot_row, E]
    split_ifs with h
    · simp [z]; rw [h]
      rw [swap_self]
      exact Matrix.one_mul M.P

    · simp [swap_rows, submatrix, one_apply, Equiv.swap, swapCore]; rw [← hz]
      funext k l
      simp
      split_ifs with h' h''
      · simp [Matrix.mul_apply]; simp [h']
      · simp [Matrix.mul_apply]; simp [h'']; split_ifs with h'''; simp [h''']; rfl
      · simp [Matrix.mul_apply]; simp [h', h'']

  have h₁ : E * R₁ = R₂ := by
    have h1 : P₁ * M.M * M.Q = R₁ := M.hm
    have h2 : P₂ * (M.gaussian_elimination_pivot_row i j).M * (M.gaussian_elimination_pivot_row i j).Q = R₂ := (M.gaussian_elimination_pivot_row i j).hm
    have : (M.gaussian_elimination_pivot_row i j).M = M.M := by
      simp [gaussian_elimination_pivot_row]
      split_ifs; rfl; rfl
    rw [this] at h2
    have : (M.gaussian_elimination_pivot_row i j).Q = M.Q := by
      simp [gaussian_elimination_pivot_row]
      split_ifs; rfl; rfl
    rw [this, ← h₀, Matrix.mul_assoc E, Matrix.mul_assoc E (P₁ * M.M) M.Q, h1] at h2
    exact h2

  have : E * E = 1 := by simp [E, swap_rows]
  let P : GL (Fin n) α := ⟨E, E, this, this⟩
  use P
  simp [P, gaussian_elimination_pivot_row, E]
  split_ifs with h
  simp [z]; rw [h]; rw [swap_self]; simp; simp [SMul.smul, HSMul.hSMul]
  constructor
  rw [← hE, h₀]; simp [P₂, gaussian_elimination_pivot_row]; split_ifs; rfl;
  rw [← hE, h₁]; simp [R₂, gaussian_elimination_pivot_row]; split_ifs; rfl;

def Gaussian.gaussian_elimination_row_aux [Lattice α] [DecidableEq α] [DecidableLT α] [CommRing α] (M : Gaussian n m α)
    (row : ℕ) (hr : row < n) (col : ℕ) (hc : col < m) :
    Gaussian n m α :=

  let rown : Fin n := ⟨row, hr⟩
  let colm : Fin m := ⟨col, hc⟩

  let pivotA := Gaussian.gaussian_elimination_pivot_row M rown colm
  if ht : (row < n - 1) ∧ (col < m - 1) then
    if pivotA.R rown colm = 0 then
      gaussian_elimination_row_aux M row hr (col + 1) (add_lt_of_lt_sub ht.2)

    else
      let nextA := Gaussian.gaussian_elimination_step_row pivotA rown colm
      gaussian_elimination_row_aux nextA (row + 1) (add_lt_of_lt_sub ht.1) (col + 1) (add_lt_of_lt_sub ht.2)
  else
    pivotA

-- lemma aa : n > 0 := by exact pos_of_neZero n

/-
`gaussian_elimination_pivot_row` 的整体效果等价于
在原矩阵左侧乘以某个可逆矩阵
-/
omit [NeZero m] in
lemma Gaussian.gaussian_elimination_step_pivot_row_eq_left_mul [Lattice α] [DecidableLT α] [Field α] (M : Gaussian n m α) (i : Fin n) (j : Fin m) (pivot_nonzero : (M.gaussian_elimination_pivot_row i j).R i j ≠ 0):
    ∃ (P : GL (Fin n) α), P.1 • M = (M.gaussian_elimination_pivot_row i j).gaussian_elimination_step_row i j := by
  rcases (Gaussian.gaussian_elimination_pivot_row_eq_left_mul M i j) with ⟨E₁, h₀⟩
  rcases (Gaussian.gaussian_elimination_step_row_eq_left_mul (M.gaussian_elimination_pivot_row i j) i j pivot_nonzero) with ⟨E₂, h₁⟩
  use (E₂ * E₁); simp; rw [Gaussian.mul_smul_left, h₀, h₁]

/-
`gaussian_elimination_row_aux` 的整体效果等价于
在原矩阵左侧乘以某个可逆矩阵
-/
omit [NeZero m] in
lemma Gaussian.gaussian_elimination_row_aux_eq_left_mul_induction [Lattice α] [DecidableEq α] [DecidableLT α] [Field α] :
  ∀ (k : ℕ), ∀ (row col : ℕ) (hr : row < n) (hc : col < m), k = (n - row) + (m - col) →
      ∀ (M : Gaussian n m α), ∃ (P : GL (Fin n) α), P.1 • M = M.gaussian_elimination_row_aux row hr col hc := by
  intro k
  induction' k using Nat.strong_induction_on with k IH
  intro row col hr hc hk M
  unfold gaussian_elimination_row_aux ; split_ifs with h
  · simp; split_ifs with h0
    · let col' := col + 1; have hc' : col' < m := by omega
      have hk' : (n - row) + (m - col') < k := by omega
      have IH_rec := IH ((n - row) + (m - col')) hk' row col' hr hc' (by simp [col']) M; exact IH_rec
    · let pivotA := M.gaussian_elimination_pivot_row ⟨row, hr⟩ ⟨col, hc⟩
      obtain ⟨P_pivot, h_pivot⟩ := Gaussian.gaussian_elimination_pivot_row_eq_left_mul M ⟨row, hr⟩ ⟨col, hc⟩
      let nextA := pivotA.gaussian_elimination_step_row ⟨row, hr⟩ ⟨col, hc⟩
      obtain ⟨P_step, h_step⟩ := pivotA.gaussian_elimination_step_row_eq_left_mul ⟨row, hr⟩ ⟨col, hc⟩ h0
      let row' := row + 1; let col' := col + 1
      have hr' : row' < n := by omega
      have hc' : col' < m := by omega
      have hk' : (n - row') + (m - col') < k := by omega
      have IH_rec := IH ((n - row') + (m - col')) hk' row' col' hr' hc' rfl nextA
      obtain ⟨P_rec, h_rec⟩ := IH_rec; use P_rec * P_step * P_pivot
      rw [GeneralLinearGroup.coe_mul, Gaussian.mul_smul_left, h_pivot,GeneralLinearGroup.coe_mul,
          Gaussian.mul_smul_left, h_step, h_rec]
  · obtain ⟨P_pivot, h_pivot⟩ := Gaussian.gaussian_elimination_pivot_row_eq_left_mul M ⟨row, hr⟩ ⟨col, hc⟩
    use P_pivot

/-
`gaussian_elimination_row_aux` 的整体效果等价于
在原矩阵左侧乘以某个可逆矩阵
-/
omit [NeZero m] in
lemma Gaussian.gaussian_elimination_row_aux_eq_left_mul [Lattice α] [DecidableEq α] [DecidableLT α] [Field α] (M : Gaussian n m α)  (i : Fin n) (j : Fin m) :
    ∃ (P : GL (Fin n) α), P.1 • M = M.gaussian_elimination_row_aux i.1 i.2 j.1 j.2 := by
  exact Gaussian.gaussian_elimination_row_aux_eq_left_mul_induction ((n - i.1) + (m - j.1)) i.1 j.1 i.2 j.2 (by rfl) M


def Gaussian.gaussian_elimination_row [Lattice α] [DecidableEq α] [DecidableLT α] [CommRing α] (M : Gaussian n m α)  : Gaussian n m α :=
  if h : 0 < n ∧ 0 < m then gaussian_elimination_row_aux M 0 h.1 0 h.2
  else M

def Gaussian.gaussian_elimination_col_aux [Lattice α] [DecidableEq α] [DecidableLT α] [CommRing α] (M : Gaussian n m α)
    (row : ℕ) (hr : row < n) (col : ℕ) (hc : col < m) :
    Gaussian n m α :=

  let rown : Fin n := ⟨row, hr⟩
  let colm : Fin m := ⟨col, hc⟩

  if ht : (row < n - 1) ∧ (col < m - 1) then
    if M.R rown colm = 0 then M.gaussian_elimination_col_aux (row + 1) (add_lt_of_lt_sub ht.1) col hc
    else
      let nextA := Gaussian.gaussian_elimination_step_row M rown colm
      nextA.gaussian_elimination_col_aux (row + 1) (add_lt_of_lt_sub ht.1) (col + 1) (add_lt_of_lt_sub ht.2)
  else
    M


def Gaussian.gaussian_elimination_col [Lattice α] [DecidableEq α] [DecidableLT α]  [CommRing α] (M : Gaussian n m α)  : Gaussian n m α :=
  if h : 0 < n ∧ 0 < m then (M.transpose.gaussian_elimination_col_aux 0 h.2 0 h.1).transpose
  else M

section swr

def Gaussian.gaussian_elimination_col_aux' [Lattice α] [DecidableEq α] [DecidableLT α] [CommRing α] (M : Gaussian n m α)
    (row : ℕ) (hr : row < n) (col : ℕ) (hc : col < m) :
    Gaussian n m α :=

  if ht : (row < n - 1) ∧ (col < m - 1) then
    if M.R ⟨row, hr⟩ ⟨col, hc⟩ = 0 then
      M.gaussian_elimination_col_aux' row hr (col+1) (add_lt_of_lt_sub ht.2)
    else
      let nextA := (Gaussian.gaussian_elimination_step_row M.transpose ⟨col, hc⟩ ⟨row, hr⟩).transpose
      nextA.gaussian_elimination_col_aux' (row + 1) (add_lt_of_lt_sub ht.1) (col + 1) (add_lt_of_lt_sub ht.2)
  else
    M

def Matrix.gaussian_elimination_col_aux'_R [Lattice α] [DecidableEq α] [DecidableLT α] [CommRing α] (R : Matrix (Fin n) (Fin m) α)
    (row : ℕ) (hr : row < n) (col : ℕ) (hc : col < m) :
    Matrix (Fin n) (Fin m) α :=

  if ht : (row < n - 1) ∧ (col < m - 1) then
    if R ⟨row, hr⟩ ⟨col, hc⟩ = 0 then
      R.gaussian_elimination_col_aux'_R row hr (col+1) (add_lt_of_lt_sub ht.2)
    else
      let nextA := (gaussian_update_row R.transpose ⟨col, hc⟩ ⟨row, hr⟩).transpose
      nextA.gaussian_elimination_col_aux'_R (row + 1) (add_lt_of_lt_sub ht.1) (col + 1) (add_lt_of_lt_sub ht.2)
  else
    R

omit [NeZero n] [NeZero m] in
@[simp] lemma Gaussian.push_R_gaussian_elimination_col_aux' [Lattice α] [DecidableEq α] [DecidableLT α] [CommRing α] (M : Gaussian n m α)
    (row : ℕ) (hr : row < n) (col : ℕ) (hc : col < m) :
  (M.gaussian_elimination_col_aux' row hr col hc).R
  = M.R.gaussian_elimination_col_aux'_R row hr col hc
  := by
  unfold  Matrix.gaussian_elimination_col_aux'_R Gaussian.gaussian_elimination_col_aux'
  simp
  split_ifs with ht hM
  · exact push_R_gaussian_elimination_col_aux' M row hr (col+1) (by omega)
  · rw [push_R_gaussian_elimination_col_aux'
    (M.transpose.gaussian_elimination_step_row ⟨col, hc⟩ ⟨row, hr⟩).transpose
    (row+1) (by omega) (col+1) (by omega)]
    congr
  · rfl

omit [NeZero n] [NeZero m] in
lemma Gaussian.gaussian_elimination_col_aux'_eq_col_aux [Lattice α] [DecidableEq α] [DecidableLT α] [CommRing α] (M : Gaussian n m α)
    (row : ℕ) (hr : row < n) (col : ℕ) (hc : col < m) :
    M.gaussian_elimination_col_aux' row hr col hc = (M.transpose.gaussian_elimination_col_aux col hc row hr).transpose
    := by
    by_cases h1 : row < n - 1 ∧ col < m - 1
    · by_cases h2 : M.R ⟨row, hr⟩ ⟨col, hc⟩ = 0
      · unfold Gaussian.gaussian_elimination_col_aux' Gaussian.gaussian_elimination_col_aux
        simp [h1,h2]
        have : M.transpose.R ⟨col, hc⟩ ⟨row, hr⟩  = 0 := by
          simp [Gaussian.transpose]
          exact h2
        simp [this]
        apply Gaussian.gaussian_elimination_col_aux'_eq_col_aux
      · conv =>
          lhs
          unfold Gaussian.gaussian_elimination_col_aux'
          simp [h1,h2]
        conv =>
          rhs
          unfold Gaussian.gaussian_elimination_col_aux
          simp [h1,h2]
        have : M.transpose.R ⟨col, hc⟩ ⟨row, hr⟩ ≠ 0 := by
          simp [Gaussian.transpose]
          exact h2
        simp [this]
        have := Gaussian.gaussian_elimination_col_aux'_eq_col_aux
          M (row +1) (by omega) (col) hc
        rw [Gaussian.gaussian_elimination_col_aux'_eq_col_aux (row:=row+1) (col:=col+1)]
        simp
    · by_cases h3 : row = n-1
      · simp[h3]
        unfold Gaussian.gaussian_elimination_col_aux
        unfold Gaussian.gaussian_elimination_col_aux'
        simp
      · have : col =m-1 := by omega
        simp [this]
        unfold Gaussian.gaussian_elimination_col_aux
        unfold Gaussian.gaussian_elimination_col_aux'
        simp


omit [NeZero n] [NeZero m] in
lemma Gaussian.gaussian_elimination_col_aux_eq_col_aux' [Lattice α] [DecidableEq α] [DecidableLT α] [CommRing α] (M : Gaussian n m α)
    (row : ℕ) (hr : row < n) (col : ℕ) (hc : col < m) :
    M.gaussian_elimination_col_aux row hr col hc = (M.transpose.gaussian_elimination_col_aux' col hc row hr).transpose
  := by
  have := M.transpose.gaussian_elimination_col_aux'_eq_col_aux
  simp at this
  rw [this]
  simp

end swr

omit [NeZero n] [NeZero m] in
lemma Gaussian.gaussian_elimination_col_aux_eq_left_mul_induction [Lattice α] [DecidableEq α] [DecidableLT α] [Field α] :
  ∀ {k : ℕ}, ∀ (row col : ℕ) (hr : row < n) (hc : col < m), k = (n - row) + (m - col) →
      ∀ (M : Gaussian n m α), ∃ (P : GL (Fin n) α), P.1 • M = gaussian_elimination_col_aux M row hr col hc := by
  intro k
  induction' k using Nat.strong_induction_on with k IH
  intro row col hr hc hk M
  unfold gaussian_elimination_col_aux ; split_ifs with h
  · simp; split_ifs with h0
    · let row' := row + 1; have hr' : row' < n := by omega
      have hk' : (n - row') + (m - col) < k := by omega
      have IH_rec := IH ((n - row') + (m - col)) hk' row' col hr' hc (by simp) M
      exact IH_rec
    · obtain ⟨P_step_row, h_step_row⟩ := M.gaussian_elimination_step_row_eq_left_mul ⟨row, hr⟩ ⟨col, hc⟩ h0
      let row' := row + 1; let col' := col + 1
      have hr' : row' < n := by omega
      have hc' : col' < m := by omega
      have hk' : (n - row') + (m - col') < k := by omega
      let nextA := M.gaussian_elimination_step_row ⟨row, hr⟩ ⟨col, hc⟩
      have IH_rec := IH ((n - row') + (m - col')) hk' row' col' hr' hc' (by rfl) nextA
      obtain ⟨P_rec, h_rec⟩ := IH_rec; use P_rec * P_step_row
      rw [GeneralLinearGroup.coe_mul, Gaussian.mul_smul_left, h_step_row, h_rec]
  · use 1; simp

omit [NeZero n] [NeZero m] in
lemma Gaussian.gaussian_elimination_col_aux_eq_left_mul [Lattice α] [DecidableEq α] [DecidableLT α] [Field α] (M : Gaussian n m α)
  (i : Fin n) (j : Fin m): ∃ (P : GL (Fin n) α), P.1 • M = gaussian_elimination_col_aux M i.1 i.2 j.1 j.2 := by
  exact Gaussian.gaussian_elimination_col_aux_eq_left_mul_induction i.1 j.1 i.2 j.2 (by rfl) M

/--
`gaussian_elimination_col` 的整体效果等价于
在原矩阵右侧乘以某个可逆矩阵
-/
lemma Gaussian.gaussian_elimination_col_eq_right_mul [Lattice α] [DecidableEq α] [DecidableLT α] [Field α] (M : Gaussian n m α) :
  ∃ (Q : GL (Fin m) α), Q.1 • (M.gaussian_elimination_row) = (M.gaussian_elimination_row).gaussian_elimination_col := by
  let Mr := (M.gaussian_elimination_row)
  show ∃ (Q : GL (Fin m) α), Q.1 • Mr = Mr.gaussian_elimination_col
  unfold gaussian_elimination_col
  split_ifs with h
  · obtain ⟨Q_col, h_col⟩ := Gaussian.gaussian_elimination_col_aux_eq_left_mul Mr.transpose ⟨0, h.2⟩ ⟨0, h.1⟩
    have h1 : (Q_col.1)ᵀ * ((Q_col⁻¹).1)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Units.inv_mul Q_col, Matrix.transpose_one]
    have h2 : ((Q_col⁻¹).1)ᵀ * (Q_col.1)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Units.mul_inv Q_col, Matrix.transpose_one]
    use ⟨Q_col.1.transpose, (Q_col⁻¹).1.transpose, h1, h2⟩
    rw [← h_col]; simp; rw [smul_def_right, smul_def_left]
    unfold transpose; congr
    · simp
    · simp
  · have : 0 < n := by exact pos_of_neZero n
    have : 0 < m := by exact pos_of_neZero m
    omega

def findNonZeroIndex [DecidableEq α] [Zero α] (u : Matrix (Fin n) (Fin m) α) (i : Fin n) (j : Fin m) :
    Fin m := (firstNonZeroIndex (u i) j).getD j

def Gaussian.gaussian_elimination_step_final [Lattice α] [DecidableEq α] [DecidableLT α] [CommRing α]
    (M : Gaussian n m α) (i : Fin n) (j : Fin m) : Gaussian n m α :=
  -- 取出第j列，从第i行开始的不为0的下标
  let z := findNonZeroIndex M.R i j
  -- 如果下标和本身一样，。。。
  if z = j then M
  else
    {
      P := M.P
      R := swap_cols M.R z j
      Q := swap_cols M.Q z j
      M := M.M
      hm := by
        funext k
        simp only [←M.hm]
        rfl
    }

omit [NeZero n] [NeZero m] in
/-- `gaussian_elimination_step_final` 的整体效果等价于在原矩阵右侧乘以某个可逆矩阵 -/
lemma Gaussian.gaussian_elimination_step_final_eq_right_mul [Lattice α] [DecidableEq α] [DecidableLT α]
    [CommRing α] (M : Gaussian n m α) (i : Fin n) (j : Fin m) :
    ∃ (Q : GL (Fin m) α), Q.1 • M = M.gaussian_elimination_step_final i j := by
  let Q₁ := M.Q; let R₁ := M.R
  let Q₂ := (M.gaussian_elimination_step_final i j).Q
  let R₂ := (M.gaussian_elimination_step_final i j).R
  let z := findNonZeroIndex M.R i j
  have hz : z = findNonZeroIndex M.R i j := by rfl
  let E : Matrix (Fin m) (Fin m) α := swap_cols (1 : Matrix (Fin m) (Fin m) α) z j
  have hE : E = swap_cols (1 : Matrix (Fin m) (Fin m) α) z j := by rfl

  have swap_self : swap_cols (1 : Matrix (Fin m) (Fin m) α) j j = 1 := by
    ext k l; simp [swap_cols, swap_rows]
    by_cases hk : k = l
    rw [hk]; rw [one_apply_ne' fun a ↦ hk (id (Eq.symm a)), one_apply_ne' hk]

  have h₀ : Q₁ * E = Q₂ := by
    simp [Q₁, Q₂, gaussian_elimination_step_final, E]
    split_ifs with h
    · simp [z]; rw [h]; rw [swap_self]; exact Matrix.mul_one M.Q
    · simp [swap_cols, swap_rows, Matrix.transpose, submatrix, one_apply, Equiv.swap, swapCore]; rw [← hz]
      funext k l; simp; split_ifs with h' h''
      · simp [Matrix.mul_apply]; simp [h']
      · simp [Matrix.mul_apply]; simp [h'']; split_ifs with h'''; simp [h''']; rfl
      · simp [Matrix.mul_apply]; simp [h', h'']

  have h₁ : R₁ * E = R₂ := by
    have h1 : M.P * M.M * Q₁ = R₁ := M.hm
    have h2 : (M.gaussian_elimination_step_final i j).P * (M.gaussian_elimination_step_final i j).M * Q₂ = R₂ := (M.gaussian_elimination_step_final i j).hm
    have : (M.gaussian_elimination_step_final i j).M = M.M := by
      simp [gaussian_elimination_step_final]
      split_ifs; rfl; rfl
    rw [this] at h2
    have : (M.gaussian_elimination_step_final i j).P = M.P := by
      simp [gaussian_elimination_step_final]; split_ifs; rfl; rfl
    rw [this, ← h₀, ← Matrix.mul_assoc, h1] at h2
    exact h2

  have : E * E = 1 := by simp [E, swap_cols, swap_rows]
  let P : GL (Fin m) α := ⟨E, E, this, this⟩
  use P; simp [P, gaussian_elimination_step_final, E]
  split_ifs with h
  simp [z]; rw [h]; rw [swap_self]; simp; simp [SMul.smul, HSMul.hSMul]
  constructor
  rw [← hE, h₁]; simp [R₂, gaussian_elimination_step_final]; split_ifs; rfl;
  rw [← hE, h₀]; simp [Q₂, gaussian_elimination_step_final]; split_ifs; rfl;

def gaussian_elimination_final_aux [Lattice α] [DecidableEq α] [DecidableLT α]
    [CommRing α] (M : Gaussian n m α) (idx : ℕ) (h : idx < n ∧ idx < m) :
    Gaussian n m α :=
  let nextM := M.gaussian_elimination_step_final ⟨idx, h.1⟩ ⟨idx, h.2⟩
  if ht : (idx < n - 1) ∧ (idx < m - 1) then
    gaussian_elimination_final_aux nextM (idx + 1) ⟨add_lt_of_lt_sub ht.1, add_lt_of_lt_sub ht.2⟩
  else
    nextM
termination_by min n m - idx

/-- Lemma for `gaussian_elimination_final_aux_eq_right_mul`.-/
lemma Gaussian._GEFA_pred_min_m_n_eq_right_mul [Lattice α] [DecidableEq α] [DecidableLT α]
  [CommRing α] (M : Gaussian n m α) (h) :
  ∃ (Q : GL (Fin m) α), Q.1 • M = gaussian_elimination_final_aux M (m.min n -1) h := by
  unfold gaussian_elimination_final_aux
  have : m≠ 0 := NeZero.ne m
  have : n≠ 0 := NeZero.ne n
  simp
  split_ifs with hif
  · have ⟨ Q1, hQ1⟩ := gaussian_elimination_step_final_eq_right_mul M
      ⟨ m.min n -1, by omega⟩ ⟨m.min n -1, by omega⟩
    rw [← hQ1]
    have: m.min n-1+1 = m.min n := by
      have: m.min n ≠ 0:= by intro h;simp at h;cases h;contradiction;contradiction
      omega
    simp [this]
    simp at hif
    have := (min_eq_iff (a:=m) (b:=n) (c:=m.min n)).1 rfl;
    cases this
    · omega
    · omega
  · exact
    gaussian_elimination_step_final_eq_right_mul M
      ⟨m.min n - 1, gaussian_elimination_final_aux._proof_1 (m.min n - 1) h⟩
      ⟨m.min n - 1, gaussian_elimination_final_aux._proof_2 (m.min n - 1) h⟩

omit [NeZero n][NeZero m] in
/-- Lemma for `gaussian_elimination_final_aux_eq_right_mul`.-/
lemma Gaussian._GEFA_eq_right_mul_of_GEFA_succ_eq_right_mul [Lattice α] [DecidableEq α] [DecidableLT α] [CommRing α] (idx h₁ h₂) :
  (∀ M:Gaussian n m α, ∃ (Q : GL (Fin m) α), Q.1 • M = gaussian_elimination_final_aux M (idx+1) h₁)
  →
  ∀ M:Gaussian n m α, ∃ (Q : GL (Fin m) α), Q.1 • M = gaussian_elimination_final_aux M (idx) h₂
  := by
  intro h M
  unfold gaussian_elimination_final_aux
  simp
  split_ifs with ht
  · let ⟨Q2, hQ2⟩ :=
      Gaussian.gaussian_elimination_step_final_eq_right_mul M ⟨idx, h₂.1⟩ ⟨idx, h₂.2⟩
    rw [← hQ2]
    specialize h (Q2.1 • M)
    obtain ⟨ Q1, hQ1⟩ := h
    use Q2 * Q1
    rw [← hQ1]
    simp [Gaussian.mul_smul_right]
  · simp at ht
    omega

/--
`gaussian_elimination_final_aux` 的整体效果等价于
在原矩阵右侧乘以某个可逆矩阵
-/
lemma Gaussian.gaussian_elimination_final_aux_eq_right_mul [Lattice α] [DecidableEq α] [DecidableLT α] [CommRing α] (M : Gaussian n m α)  (idx h) :
    ∃ (Q : GL (Fin m) α), Q.1 • M = gaussian_elimination_final_aux M idx h := by
  have := NeZero.ne m; have := NeZero.ne n
  by_cases h1 : idx = m.min n -1
  · simp [h1]
    apply Gaussian._GEFA_pred_min_m_n_eq_right_mul
  · by_cases h2 : idx > m.min n -1
    · simp at h2;
      have hh:m.min n ≤ idx := by omega
      simp at hh
      omega
    · have h2: idx < m.min n - 1:= by omega --now idx < m.min n - 1
      unfold gaussian_elimination_final_aux
      simp
      split_ifs with h3
      · have ⟨ Q1, hQ1⟩ :=
          Gaussian.gaussian_elimination_step_final_eq_right_mul M ⟨ idx, h.1⟩ ⟨ idx, h.2⟩
        rw [← hQ1]
        have ⟨ Q2, hQ2⟩ :=
          Gaussian.gaussian_elimination_final_aux_eq_right_mul (M:=Q1.1 • M) (idx+1) (by omega)
        rw [← hQ2]
        use Q1 * Q2
        simp [mul_smul_right]
      · exact
        gaussian_elimination_step_final_eq_right_mul M
          ⟨idx, gaussian_elimination_final_aux._proof_1 idx h⟩
          ⟨idx, gaussian_elimination_final_aux._proof_2 idx h⟩

def Gaussian.gaussian_elimination_final [Lattice α] [DecidableEq α] [DecidableLT α] [CommRing α] (M : Gaussian n m α)  : Gaussian n m α :=
  if h : 0 < n ∧ 0 < m then gaussian_elimination_final_aux M 0 h
  else M

/--
`gaussian_elimination_final` 的整体效果等价于
在原矩阵右侧乘以某个可逆矩阵
-/
lemma Gaussian.gaussian_elimination_final_eq_right_mul [Lattice α] [DecidableEq α] [DecidableLT α][ CommRing α] (M : Gaussian n m α)  :
  ∃ (Q : GL (Fin m) α), Q.1 • M = gaussian_elimination_final M := by
  unfold Gaussian.gaussian_elimination_final
  split_ifs with h
  · exact Gaussian.gaussian_elimination_final_aux_eq_right_mul M 0 (by omega)
  · use (1 : GL (Fin m) α); simp

def Gaussian.gaussian_elimination [Lattice α] [DecidableEq α] [DecidableLT α] [CommRing α] (M : Gaussian n m α)  : Gaussian n m α :=
  M.gaussian_elimination_row.gaussian_elimination_col.gaussian_elimination_final

def Gaussian.init [Ring α] (A : Matrix (Fin n) (Fin m) α) : Gaussian n m α :=
    ⟨1, A, 1, A, by simp⟩

-- #check Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec
-- #eval!
--   (Gaussian.init !![1, 2, (3 : ℤ), 4 ;
--                     1, 2, (5 : ℤ), 6 ;
--                     1, 2, (7 : ℤ), 8 ]).gaussian_elimination
-- #eval !![1, 0, 0; -1, 0, 1; -2, 4, -2] * !![1, 2, 3, (4 : ℤ); 1, 2, 5, 6; 1, 2, 7, 8] * !![1, -3, -2, -4; 0, 0, 1, 0; 0, 1, 0, -4; 0, 0, 0, 4]
def rankStdBlock (K : Type*) [Zero K] [One K]
    (m n r : ℕ) : Matrix (Fin m) (Fin n) K :=
  fun i j => if (i : ℕ) < r ∧ (j : ℕ) < r then
            if (i : ℕ) = j then 1 else 0
          else 0

end Gauss

section

variable {m n : ℕ }
variable [NeZero m] [DecidableEq α] [Zero α] (M : Matrix (Fin n) (Fin m) α)

def Matrix.NonZeroIndex := fun i ↦ firstNonZeroIndex (M i) 0

@[simp] lemma ne_zero_of_eq_NonZeroIndex (i : Fin n) (j : Fin m): (↑j = M.NonZeroIndex i) → M i j ≠ 0 :=
  by
  unfold NonZeroIndex firstNonZeroIndex
  intro h
  have h := Eq.symm h
  change find? (fun i_1 ↦ decide (M i i_1 ≠ 0)) ((finRange m).rtake (m - ↑0)) = Option.some j at h
  simp [find?_eq_some_iff_getElem] at h
  exact h.1

lemma some_eq_NonZeroIndex_iff (i : Fin n) (j : Fin m) :
  (↑j = M.NonZeroIndex i) ↔ (M i j ≠ 0  ∧ ∀ j' < j, M i j' = 0) :=
  by
  unfold NonZeroIndex firstNonZeroIndex
  rw [Eq.comm]
  change find? (fun i_1 ↦ decide (M i i_1 ≠ 0)) ((finRange m).rtake (m - ↑0)) = Option.some j ↔ M i j ≠ 0 ∧ ∀ j' < j, M i j' = 0
  simp [find?_eq_some_iff_getElem, rtake]
  intro h
  constructor
  · intro ⟨i₁, ⟨i₁m, i₁j , f⟩ ⟩
    obtain ⟨j,hj⟩:=j
    subst_eqs
    exact fun j' a ↦ f (↑j') a
  · intro f
    use j, j.2
    simp
    exact fun j' a ↦ f ⟨j', by omega⟩ a

@[simp] lemma some_eq_NonZeroIndex_of_le_NonZeroIndex_of_ne_zero (i : Fin n) (j : Fin m) :
  M i j ≠ 0 → ↑j ≤ M.NonZeroIndex i → (↑j = M.NonZeroIndex i) :=
  by
  by_cases h : ∃ c, WithTop.some c = M.NonZeroIndex i
  · obtain ⟨c,h⟩:= h
    rw[←h]
    rw [some_eq_NonZeroIndex_iff] at h
    intro h1 h2
    rw [le_iff_lt_or_eq] at h2
    aesop
  · simp at h
    have h : ∀ (x : Fin m),  M.NonZeroIndex i ≠ Option.some x :=
      fun x a ↦ h x (id (Eq.symm a))
    rw [←Option.eq_none_iff_forall_ne_some] at h
    unfold NonZeroIndex firstNonZeroIndex at h
    simp [find?_eq_none, rtake] at h
    aesop

@[simp] lemma eq_zero_of_left_of_NonZeroIndex (A : Matrix (Fin n) (Fin m) α) (i) :
  ∀ j : Fin m, WithTop.some j < A.NonZeroIndex i → A i j = 0 := by
  by_cases  h : ∃ c, WithTop.some c = A.NonZeroIndex i
  · obtain ⟨c,h⟩:= h
    rw[←h]
    rw [some_eq_NonZeroIndex_iff] at h
    aesop
  · simp at h
    have h : ∀ (x : Fin m),  A.NonZeroIndex i ≠ Option.some x :=
      fun x a ↦ h x (id (Eq.symm a))
    rw [←Option.eq_none_iff_forall_ne_some] at h
    unfold NonZeroIndex firstNonZeroIndex at h
    simp [find?_eq_none, rtake] at h
    aesop

/--
矩阵某行无非零元，当且仅当该行全是零
-/
@[simp] lemma Matrix.NonZeroIndex_eq_top_iff {i}: M.NonZeroIndex i = ⊤ ↔ M i = 0 := by
  unfold Matrix.NonZeroIndex firstNonZeroIndex finRange rtake
  simp
  change find? (fun i_1 ↦ !decide (M i i_1 = 0)) (ofFn fun i ↦ i) = none ↔ M i = 0
  simp [find?_eq_none]
  exact Iff.symm funext_iff

/--
子矩阵的某行非零项等于...
-/
@[simp] lemma NonZeroIndex_of_submatrix_id {n'} {f : Fin n' → Fin n} :
  (M.submatrix f id).NonZeroIndex = fun i ↦ (M.NonZeroIndex (f i)) := by
  unfold NonZeroIndex
  ext i
  congr

@[class]
structure Matrix.IsRowEchelon : Prop where
  pivot_right_move :
    ∀ {i j}, i < j → M.NonZeroIndex i < M.NonZeroIndex j ∨ M.NonZeroIndex j = ⊤

/-- `fun x => x+r `-/
def Fin.sub_aux (n r : ℕ) : Fin (n - r) → Fin n :=
    fun i ↦ ⟨i.1 + r , add_lt_of_lt_sub i.2⟩

@[simp] lemma Fin.sub_aux_val_eq (n r : ℕ) (x): Fin.sub_aux n r x = x.1 + r := rfl
@[simp] lemma Fin.sub_aux_eq (n r : ℕ) (x): Fin.sub_aux n r x = ⟨x.1 + r, by omega⟩  := rfl

/--
后n - r行已经做好了
-/
def Matrix.IsSemiRowEchelon (r : Nat) :=
    (M.submatrix (Fin.sub_aux n r) id).IsRowEchelon

lemma NonZeroIndex_submatrix_sub_aux_eq (r i)
  (hr : r < n) :
  (M.submatrix (Fin.sub_aux n r) id).NonZeroIndex (i : Fin (n-r))
  = M.NonZeroIndex ⟨i.1 + r, by omega⟩ := by
  simp [Fin.sub_aux]


lemma IsSemiRowEchelon_succ_of_IsSemiRowEchelon (r : Nat) (h₂ : r + 1 < n ) :
  M.IsSemiRowEchelon (r + 1) →
  (M.NonZeroIndex ⟨r, by omega⟩ < M.NonZeroIndex ⟨r + 1, by omega⟩
  ∨ M.NonZeroIndex ⟨ r+1, by omega⟩ = ⊤
  )  →
    M.IsSemiRowEchelon r := by
    intro ⟨RE⟩ h
    constructor
    intro i j hij
    simp
    simp at RE
    by_cases hi : i ≠ ⟨0, by omega⟩
    · specialize @RE ⟨i-1, by omega⟩ ⟨j-1, by omega⟩
      simp at RE
      have : i.1 ≠ 0 := hi ∘ (Fin.val_eq_val i ⟨0, _⟩).1
      specialize RE (by omega)
      simp [(by omega : i.1 - 1 + (r + 1) = i+r),
       (by omega : ↑j - 1 + (r + 1) = j+r)
       ] at RE
      exact RE
    · simp at hi
      simp [hi]
      specialize @RE ⟨0, by omega⟩ ⟨j-1, by omega⟩
      by_cases hj : j.1 = 1
      · simp [hj]
        simp [(by omega : r+1=1+r)] at h
        exact h
      · specialize RE (by simp; omega)
        simp [(by omega : j.1 - 1 + (r + 1) = j + r)] at RE
        rcases RE with RE | RE
        · left
          rcases h with h | h
          · exact gt_trans RE h
          · simp [h] at RE
        · right
          exact RE


#check  (Matrix.IsRowEchelon !![1,0;0,1])
structure Matrix.IsReducedRowEchelon extends Matrix.IsRowEchelon M where
  pivot_row_zero :
    ∀ {i j c}, M.NonZeroIndex i = some c → c < j → M i j = 0
-- ∀ {i j}, j > M.NonZeroIndex i → j = ⊤ ∧ M i j = 0
end

section swr

variable {m n : ℕ }
variable [NeZero m]

variable {α : Type*} [DecidableEq α] [Field α] [Lattice α] [DecidableLT α]

omit [Lattice α] [DecidableLT α] in
@[simp] lemma NonZeroIndex_congr (A B: Matrix (Fin n) (Fin m) α) (i) :
    A i = B i → A.NonZeroIndex i = B.NonZeroIndex i := by
    simp [NonZeroIndex, firstNonZeroIndex]
    intro h
    rw [h]

omit [Lattice α] [DecidableLT α] in
@[simp] lemma firstNonZeroIndex_eq_firstNonZeroIndex_of_left_eq_left (A B: (Fin m) → α) :
    (∀ j : Fin m, ↑j ≤ (firstNonZeroIndex A 0) → A j = B j)
    → firstNonZeroIndex A 0 = firstNonZeroIndex B 0
    := by
    intro heq
    by_cases hA : ∃ c, firstNonZeroIndex A 0 = some c
    · simp [firstNonZeroIndex, finRange, rtake]
      simp [firstNonZeroIndex, finRange, rtake] at hA heq
      obtain ⟨c, hc⟩ := hA
      rw [hc]; rw [hc] at heq
      rw [find?_eq_some_iff_getElem] at hc
      simp at hc
      obtain ⟨Aine0, i, im, iv, lti⟩  := hc
      subst_vars
      symm; rw [find?_eq_some_iff_getElem]
      simp
      split_ands
      · specialize heq ⟨i,im⟩ (by rfl)
        simp [← heq]
        exact Aine0
      · use im
        intro j hj
        have jm : j < m := by linarith
        specialize heq ⟨j, jm⟩ (by
          change (WithTop.some ⟨j,jm⟩ : WithTop (Fin m)) ≤ (WithTop.some ⟨i, im⟩ : WithTop (Fin m))
          rw [WithTop.coe_le_coe]
          change j ≤ i
          omega)
        rw [← heq]
        exact lti j hj
    · push_neg at hA
      have :  ∀ (c : Fin m), some c ≠ firstNonZeroIndex A 0 := fun c a ↦ hA c (id (Eq.symm a))
      rw [←Option.eq_none_iff_forall_some_ne] at this
      rw [this]; rw [this] at heq
      unfold firstNonZeroIndex; unfold firstNonZeroIndex at this
      symm
      rw [find?_eq_none]; rw [find?_eq_none] at this
      simp [rtake]; simp [rtake] at this
      intro x
      specialize heq x (right_eq_inf.mp rfl)
      rw [← heq]
      exact this x

omit [Lattice α] [DecidableLT α] in
@[simp] lemma firstNonZeroIndex_eq_firstNonZeroIndex_of_left_approx_left (A B: (Fin m) → α) :
    (∀ j : Fin m, ↑j ≤ (firstNonZeroIndex A 0) → ((A j = 0) ↔ (B j=0)))
    → firstNonZeroIndex A 0 = firstNonZeroIndex B 0
    := by
    intro heq
    by_cases hA : ∃ c, firstNonZeroIndex A 0 = some c
    · simp [firstNonZeroIndex, finRange, rtake]
      simp [firstNonZeroIndex, finRange, rtake] at hA heq
      obtain ⟨c, hc⟩ := hA
      rw [hc]; rw [hc] at heq
      rw [find?_eq_some_iff_getElem] at hc
      simp at hc
      obtain ⟨Aine0, i, im, iv, lti⟩  := hc
      subst_vars
      symm; rw [find?_eq_some_iff_getElem]
      simp
      split_ands
      · specialize heq ⟨i,im⟩ (by rfl)
        simp [← heq]
        exact Aine0
      · use im
        intro j hj
        have jm : j < m := by linarith
        specialize heq ⟨j, jm⟩ (by
          change (WithTop.some ⟨j,jm⟩ : WithTop (Fin m)) ≤ (WithTop.some ⟨i, im⟩ : WithTop (Fin m))
          rw [WithTop.coe_le_coe]
          change j ≤ i
          omega)
        rw [← heq]
        exact lti j hj
    · push_neg at hA
      have :  ∀ (c : Fin m), some c ≠ firstNonZeroIndex A 0 := fun c a ↦ hA c (id (Eq.symm a))
      rw [←Option.eq_none_iff_forall_some_ne] at this
      rw [this]; rw [this] at heq
      unfold firstNonZeroIndex; unfold firstNonZeroIndex at this
      symm
      rw [find?_eq_none]; rw [find?_eq_none] at this
      simp [rtake]; simp [rtake] at this
      intro x
      specialize heq x (right_eq_inf.mp rfl)
      rw [← heq]
      exact this x

@[simp] lemma IsRowEchelon_of_IsRowEchelon_of_NonZeroIndex_eq_NonZeroIndex {α : Type*} [Lattice α] [DecidableEq α] [DecidableLT α]
    [Field α] (A B: Matrix (Fin n) (Fin m) α) :
    A.NonZeroIndex = B.NonZeroIndex → A.IsRowEchelon → B.IsRowEchelon
    := by
    intro heq ⟨hA⟩
    constructor
    rw [heq] at hA
    exact hA

omit [Lattice α] [DecidableLT α] in
@[simp] lemma NonZeroIndex_eq_NonZeroIndex_of_left_eq_left (A B: Matrix (Fin n) (Fin m) α) :
    (∀ (i : Fin n) (j : Fin m), ↑j ≤ (A.NonZeroIndex i) → A i j = B i j) →
    A.NonZeroIndex = B.NonZeroIndex := by
    unfold NonZeroIndex
    intro h
    ext i
    exact firstNonZeroIndex_eq_firstNonZeroIndex_of_left_eq_left (A i) (B i) (h i)

omit [Lattice α] [DecidableLT α] in
/-- 条件弱化到 零性相等，而非严格相等-/
@[simp] lemma NonZeroIndex_eq_NonZeroIndex_of_left_approx_left (A B: Matrix (Fin n) (Fin m) α) :
    (∀ (i : Fin n) (j : Fin m), ↑j ≤ (A.NonZeroIndex i) → ((A i j =0) ↔ (B i j=0))) →
    A.NonZeroIndex = B.NonZeroIndex := by
    unfold NonZeroIndex
    intro h
    ext i
    exact firstNonZeroIndex_eq_firstNonZeroIndex_of_left_approx_left (A i) (B i) (h i)


@[simp] lemma IsRowEchelon_of_IsRowEchelon_of_left_eq_left (A B: Matrix (Fin n) (Fin m) α) :
    (∀ i : Fin n, ∀ j : Fin m, j ≤ A.NonZeroIndex i → A i j = B i j ) →
    A.IsRowEchelon → B.IsRowEchelon :=
  fun h =>
    IsRowEchelon_of_IsRowEchelon_of_NonZeroIndex_eq_NonZeroIndex A B
      (NonZeroIndex_eq_NonZeroIndex_of_left_eq_left A B h)

@[simp] lemma WithTop.succ_coe_le_iff_lt {n} (x : Nat) (h : x + 1 < n ) (y : WithTop (Fin n)) :
  ↑(⟨x+1, h⟩ : Fin n) ≤ y ↔ ↑(⟨x, by omega⟩ : Fin n ) < y:= by
  let xn : Fin n := ⟨x, by omega⟩
  let sxn : Fin n := ⟨x+1, by omega⟩
  rcases y with top | y
  · constructor
    · intros
      show (↑(⟨x, _⟩ : Fin n): WithTop (Fin n)) < ⊤
      simp
    · intros
      show (↑(⟨x+1, _⟩ : Fin n): WithTop (Fin n)) ≤ ⊤
      simp
  · show ↑sxn ≤ WithTop.some y ↔ ↑xn < WithTop.some y
    simp [WithTop.coe_le_coe]
    obtain ⟨y,yn⟩:=y
    exact add_one_le_iff

omit [Lattice α] [DecidableLT α] in
@[simp] lemma Matrix.gaussian_elimination_step_col_R_NonZeroIndex_of_eq_NonZeroIndex (A : Matrix (Fin n) (Fin m) α) [A.IsRowEchelon]
  (i : Fin n) (j : Fin m) (h : ↑j = A.NonZeroIndex i) :
  (gaussian_update_row Aᵀ j i)ᵀ.NonZeroIndex = A.NonZeroIndex := by
  unfold gaussian_update_row gaussian_update
  symm
  apply NonZeroIndex_eq_NonZeroIndex_of_left_approx_left
  intro i₁ j₁ hj₁i₁
  simp
  split_ifs with hj₁j
  · rfl
  · simp
    suffices  A i j₁ * A i₁ j = 0 from by
      rw[this]
      simp
      intros
      have : A i j ≠ 0 := ne_zero_of_eq_NonZeroIndex A i j h
      contradiction
    simp at hj₁j
    simp
    right
    apply eq_zero_of_left_of_NonZeroIndex
    have : WithTop.some j < WithTop.some j₁ := by simp [hj₁j]
    exact lt_of_lt_of_le this hj₁i₁


instance Matrix.gaussian_elimination_step_col_R_IsEchelon_of_eq_NonZeroIndex (A : Matrix (Fin n) (Fin m) α) [inst : A.IsRowEchelon]
  (i : Fin n) (j : Fin m) (h : ↑j = A.NonZeroIndex i) :
  (gaussian_update_row Aᵀ j i)ᵀ.IsRowEchelon := by
  apply IsRowEchelon_of_IsRowEchelon_of_NonZeroIndex_eq_NonZeroIndex (A:=A)
  symm
  apply A.gaussian_elimination_step_col_R_NonZeroIndex_of_eq_NonZeroIndex
  · exact h
  · exact inst




@[simp] lemma Matrix.gaussian_elimination_col_aux'_R_NonZeroIndex (A : Matrix (Fin n) (Fin m) α) [inst : A.IsRowEchelon]
  (i : Fin n) (j : Fin m) (h : j ≤ A.NonZeroIndex i) :
  (A.gaussian_elimination_col_aux'_R i.1 i.2 j.1 j.2).NonZeroIndex = A.NonZeroIndex := by
  unfold gaussian_elimination_col_aux'_R
  simp
  split_ifs with ht Aij
  · refine A.gaussian_elimination_col_aux'_R_NonZeroIndex i ⟨j.1+1, by omega⟩ ?_
    simp
    suffices ↑j ≠ A.NonZeroIndex i from by exact lt_of_le_of_ne h this
    intro hf
    have : A i j ≠ 0 := by exact ne_zero_of_eq_NonZeroIndex A i j hf
    contradiction
  · have : ↑j = A.NonZeroIndex i := some_eq_NonZeroIndex_of_le_NonZeroIndex_of_ne_zero A i j Aij h
    have : (gaussian_update_row Aᵀ j i)ᵀ.IsRowEchelon :=
      A.gaussian_elimination_step_col_R_IsEchelon_of_eq_NonZeroIndex i j this
    have := Matrix.gaussian_elimination_col_aux'_R_NonZeroIndex (i:=⟨i.1+1,by omega⟩) (j:=⟨j.1+1,by omega⟩)
      (A := (gaussian_update_row Aᵀ j i)ᵀ)
    rw [this]
    · expose_names
      exact gaussian_elimination_step_col_R_NonZeroIndex_of_eq_NonZeroIndex A i j this_1
    · have : (gaussian_update_row Aᵀ j i)ᵀ.NonZeroIndex = A.NonZeroIndex := by
        expose_names;
        exact gaussian_elimination_step_col_R_NonZeroIndex_of_eq_NonZeroIndex A i j this_1
      rw [this]
      simp
      obtain ⟨inst⟩ := inst
      specialize @inst i ⟨i.1+1, by omega⟩ (by
        rw[← Fin.val_fin_lt]
        exact lt_add_one ↑i
      )
      rcases inst with h | h
      · expose_names
        rw [this_1]
        exact h
      · rw[h]; simp
  · rfl
termination_by m-j.1

@[simp] lemma Matrix.gaussian_elimination_col_aux'_R_IsRowEchelon (A : Matrix (Fin n) (Fin m) α) [inst : A.IsRowEchelon]
  (i : Fin n) (j : Fin m) (h : j ≤ A.NonZeroIndex i) :
  (A.gaussian_elimination_col_aux'_R i.1 i.2 j.1 j.2).IsRowEchelon := by
  apply IsRowEchelon_of_IsRowEchelon_of_NonZeroIndex_eq_NonZeroIndex (A:=A)
  · symm
    exact A.gaussian_elimination_col_aux'_R_NonZeroIndex i j h
  · exact inst


@[simp] lemma Gaussian.gaussian_elimination_col_aux'_isRowEchelon {α : Type*} [Lattice α] [DecidableEq α] [DecidableLT α]
    [Field α] (A : Gaussian n m α) {row col: ℕ} (hr : row < n) (hc : col < m)
    (h : WithTop.some ⟨col, hc⟩ ≤ A.R.NonZeroIndex ⟨row, hr⟩)
    [inst : A.R.IsRowEchelon] :
    (A.gaussian_elimination_col_aux' row hr col hc).R.IsRowEchelon := by
  rw [Gaussian.push_R_gaussian_elimination_col_aux']
  exact A.R.gaussian_elimination_col_aux'_R_IsRowEchelon ⟨row, hr⟩ ⟨col,hc⟩ h

/--
`gaussian_elimination_col` preserves row‑echelon structure:

若 `M.R` 已满足 `IsRowEchelon`,  则消除列主元得到的 `(gaussian_elimination_col M).R` 仍然行阶梯形。
-/
theorem Gaussian.gaussian_elimination_col_isRowEchelon {α : Type*} [Lattice α] [DecidableEq α] [DecidableLT α]
    [Field α] (A : Gaussian n m α) (h : A.R.IsRowEchelon ) :
    (A.gaussian_elimination_col).R.IsRowEchelon := by
    unfold Gaussian.gaussian_elimination_col
    split_ifs
    · rw [←Gaussian.gaussian_elimination_col_aux'_eq_col_aux]
      apply A.gaussian_elimination_col_aux'_isRowEchelon
      (expose_names;
        exact
          StrictMono.minimal_preimage_bot (fun ⦃a b⦄ a ↦ a) rfl
            (A.R.NonZeroIndex ⟨0, gaussian_elimination_row._proof_1 h_1⟩))
    · exact h

end swr

section Lemmas

variable  {α : Type*} {n m : ℕ} [Field α] (M : Gaussian n m α) [NeZero n] [NeZero m]
  [Lattice α] [DecidableEq α] [DecidableLT α]

/-- ① `gaussian_elimination_row` 产出的 `R` 为行阶梯形矩阵 -/
lemma gaussian_elimination_row_is_row_echelon :
    M.gaussian_elimination_row.R.IsRowEchelon := by
  -- 待补证明
  sorry

/--
② `gaussian_elimination_row` 的整体效果等价于
在原矩阵左侧乘以某个可逆矩阵
-/
lemma Gaussian.gaussian_elimination_row_eq_left_mul:
    ∃ (P : GL (Fin n) α), P.1 • M = M.gaussian_elimination_row := by
  unfold Gaussian.gaussian_elimination_row
  split_ifs with h
  · obtain ⟨P_aux, h_aux⟩ := Gaussian.gaussian_elimination_row_aux_eq_left_mul M 0 0
    use P_aux; exact h_aux
  · use 1; simp only [Units.val_one, Gaussian.smul_eq_left]


lemma Gaussian.gaussian_elimination_col_preserves_reduced_row_echelon_aux
    (hM : M.R.IsRowEchelon) : ∀ {i j c}, M.gaussian_elimination_col.R.NonZeroIndex i = some c →
    c < j → M.gaussian_elimination_col.R i j = 0 := sorry

lemma Gaussian.gaussian_elimination_col_preserves_reduced_row_echelon
    (hM : M.R.IsRowEchelon) : M.gaussian_elimination_col.R.IsReducedRowEchelon :=
    ⟨M.gaussian_elimination_col_isRowEchelon hM,
     M.gaussian_elimination_col_preserves_reduced_row_echelon_aux hM⟩

/-- `gaussian_elimination_row` + `gaussian_elimination_col` 产出的 `R` 为简化行阶梯形矩阵 -/
lemma Gaussian.gaussian_elimination_row_col_is_row_reduced_echelon :
    M.gaussian_elimination_row.gaussian_elimination_col.R.IsReducedRowEchelon := by
  -- 待补证明
  sorry

-- /--
-- `gaussian_elimination_final` 保持行阶梯结构：
-- 若输入 `G.R` 是行阶梯形矩阵，则执行该函数后得到的 `R` 仍为行阶梯形。
-- -/
-- lemma gaussian_elimination_final_preserves_row_echelon
--     (hM : M.R.IsRowEchelon) : M.gaussian_elimination_final.R.IsRowEchelon := by
--   sorry

-- /--
-- `gaussian_elimination_final` 保持简化阶梯结构：
-- 若输入 `G.R` 是简化行阶梯形（RREF），则执行该函数后仍为 RREF。
-- -/
-- lemma gaussian_elimination_final_preserves_rref
--     (hM : M.R.IsReducedRowEchelon) : M.gaussian_elimination_final.R.IsReducedRowEchelon := by
--   sorry

end Lemmas



section Row

open Submodule Set
variable {K : Type*}
variable {m n : ℕ}

lemma left_mul_in_span [CommRing K] (P : GL (Fin m) K) (A : Matrix (Fin m) (Fin n) K) (i : Fin m) :
    (P.1 * A) i ∈ span K (Set.range A) := by
  show (fun k => dotProduct (P.1 i) (A · k)) ∈ _
  simp only [dotProduct]
  rw [mem_span_range_iff_exists_fun]
  use P.1 i
  ext k
  simp

theorem rowSpace_left_mul_invariant_mp [CommRing K] {x}
    (P : GL (Fin m) K) (A : Matrix (Fin m) (Fin n) K) :
     x ∈ span K (Set.range (P.1 * A)) → x ∈ span K (Set.range A) := by
  let P' := (P : Matrix (Fin m) (Fin m) K)
  let Q := P⁻¹
  intro hx
  rw [mem_span_set] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  refine sum_mem ?_
  intro c hc
  have hc_ne_zero : s c ≠ 0 := Finsupp.mem_support_iff.mp hc
  have hc_range : c ∈ Set.range (P' * A) := by
    apply hs
    exact Finsupp.mem_support_iff.mpr hc_ne_zero
  rw [Set.mem_range] at hc_range
  obtain ⟨i, rfl⟩ := hc_range
  show s ((P' * A) i) • (P' * A) i ∈ span K (range A)
  exact smul_mem _ _ (left_mul_in_span P A i)

theorem rowSpace_left_mul_invariant_mpr {x} [CommRing K]
    (P : GL (Fin m) K) (A : Matrix (Fin m) (Fin n) K) :
     x ∈ Submodule.span K (Set.range A) → x ∈ Submodule.span K (Set.range (P.1 * A)) := by
  let P' := (P : Matrix (Fin m) (Fin m) K)
  let Q := P⁻¹
  intro hx
  rw [mem_span_set] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  refine sum_mem ?_
  intro c hc
  have hc_ne_zero : s c ≠ 0 := Finsupp.mem_support_iff.mp hc
  have hc_range : c ∈ Set.range A := by
    apply hs
    exact Finsupp.mem_support_iff.mpr hc_ne_zero
  rw [Set.mem_range] at hc_range
  obtain ⟨i, rfl⟩ := hc_range
  show s (A i) • A i ∈ span K (range (P' * A))
  have h_row : A i = (Q.1 * (P' * A)) i := by
    rw [←Matrix.mul_assoc]
    unfold Q P'
    simp only [coe_units_inv, isUnits_det_units, nonsing_inv_mul, Matrix.one_mul]
  rw [h_row]
  exact smul_mem _ _ (left_mul_in_span Q (P' * A) i)


theorem rowSpace_left_mul_invariant [CommRing K]
    (P : GL (Fin m) K) (A : Matrix (Fin m) (Fin n) K) :
    span K (range (P.1 * A)) = span K (range A) := by
  let P' := (P : Matrix (Fin m) (Fin m) K)
  let Q := P⁻¹
  apply Submodule.ext
  intro x
  constructor
  · exact rowSpace_left_mul_invariant_mp P A
  · exact rowSpace_left_mul_invariant_mpr P A

theorem rowSpace_gauss_invariant [Field K] [NeZero n] [NeZero m] [Lattice K]
    [DecidableEq K] [DecidableLT K] (M : Gaussian n m K) :
    span K (range M.gaussian_elimination_row.R) = span K (range M.R) := by
  obtain ⟨P, hP⟩ := M.gaussian_elimination_row_eq_left_mul
  rw [← hP]
  have h : (P.1 • M).R = P.1 * M.R := by rfl
  rw [h, ← M.hm]
  exact rowSpace_left_mul_invariant _ _

end Row

section RankNormalForm


variable {m n : ℕ} [NeZero m] [NeZero n] {K : Type*} [Lattice K] [DecidableEq K] [DecidableLT K] (A : Matrix (Fin m) (Fin n) K)

theorem Matrix.gaussian_elimination_rank_normal_form [CommRing K] [NoZeroDivisors K] :
  ∀ (i : Fin m) (j : Fin n),
          if (i : ℕ) < A.rank ∧ (j : ℕ) < A.rank ∧ (i : ℕ) = j then
              (Gaussian.init A).gaussian_elimination.R i j ≠ 0
          else (Gaussian.init A).gaussian_elimination.R i j = 0 := by
   sorry

theorem Matrix.exists_rank_normal_form [Field K] [NoZeroDivisors K] :
    ∃ (P : GL (Fin m) K) (Q : GL (Fin n) K),
      ∀ (i : Fin m) (j : Fin n),
          if (i : ℕ) < A.rank ∧ (j : ℕ) < A.rank ∧ (i : ℕ) = j then
            (P.1 * A * Q.1) i j ≠ 0
          else (P.1 * A * Q.1) i j = 0 := by
  let G := Gaussian.init A
  let R := (Gaussian.init A).gaussian_elimination.R
  have hR : ∃ (P : GL (Fin m) K) (Q : GL (Fin n) K), R = P.1 * A * Q.1 := by
    obtain ⟨P, hP₁⟩ := G.gaussian_elimination_row_eq_left_mul
    obtain ⟨Q₁, hQ₁⟩ := G.gaussian_elimination_col_eq_right_mul
    obtain ⟨Q₂, hQ₂⟩ := G.gaussian_elimination_row.gaussian_elimination_col.gaussian_elimination_final_eq_right_mul
    have hR_def : R = G.gaussian_elimination_row.gaussian_elimination_col.gaussian_elimination_final.R := by exact
      rfl
    rw[ hR_def,<-hQ₂,<-hQ₁,<-hP₁]
    simp [Matrix.mul_assoc]
    use P, Q₁ * Q₂
    let Q : GL (Fin n) K := Q₁ * Q₂
    simp [Gaussian.smul_def_right, Gaussian.smul_def_left, G, Gaussian.init,  Matrix.mul_assoc]
  have h_rank : ∀ (i : Fin m) (j : Fin n),
          if (i : ℕ) < A.rank ∧ (j : ℕ) < A.rank ∧ (i : ℕ) = j then
              R i j ≠ 0
          else R i j = 0 := by
    apply Matrix.gaussian_elimination_rank_normal_form
  rcases hR with ⟨P, Q, hPQ⟩
  use P, Q
  intro i j
  rw [<-hPQ]
  apply h_rank

-- #checkBasis.SmithNormalForm
-- f i = j then
      --   if i < A.rank ∧ j < A.rank then 1 / A i j
      --   else 1
      -- else 0

-- def Gaussian.gaussian_elimination_final_scale [Lattice α] [DecidableEq α] [DecidableLT α] [CommRing α]
--   (M : Gaussian n m α) : Gaussian n m α where
--   P :=
--   fun i =>
--     if fun k => M.R k i ≠ 0 then
--       fun j =>
--         if i = j then M.R i ⟨i, sorry⟩
--         else 0
--     else
--       fun j =>
--         if i = j then 1
--         else 0
--   R := fun i =>
--     if M.R i ≠ 0 then
--       fun j =>
--         if i.1 = j.1 then 1
--         else 0
--     else 0
--   Q := M.Q
--   M := M.M
--   hm := by
--     sorry

-- /--
-- `gaussian_elimination_final_scale` 的整体效果等价于
-- 在原矩阵左侧乘以某个可逆矩阵
-- -/
-- lemma Gaussian.gaussian_elimination_final_scale_eq_right_mul [Lattice α] [DecidableEq α] [DecidableLT α] [CommRing α] (M : Gaussian n m α) :
--     ∃ (P : GL (Fin n) α), P.1 • M = M.gaussian_elimination_final_scale := by
--   sorry

theorem Matrix.exists_rank_standard_form [Field K]:
    ∃ (P : GL (Fin m) K) (Q : GL (Fin n) K),
      P.1 * A * Q.1 = rankStdBlock K m n A.rank := by
  sorry

end RankNormalForm

section Classification

variable {K : Type*}  -- Extra condition : K is nontrivial
variable {m n : ℕ} [NeZero m] [NeZero n]

def rankEquiv [CommRing K] [Nontrivial K] (A B : Matrix (Fin m) (Fin n) K) : Prop :=
  ∃ (P : GL (Fin m) K) (Q : GL (Fin n) K), B = P.1 * A * Q.1

omit [NeZero m] [NeZero n] in
theorem rankEquiv_to_rank_eq_on_CommRing [CommRing K] [Nontrivial K] (A B : Matrix (Fin m) (Fin n) K) :
    rankEquiv A B → rank A = rank B := by
      rintro ⟨P, Q, h⟩
      rw [h]
      have h₀ : StrongRankCondition K := by apply commRing_strongRankCondition
      have h1 : rank (A * Q.1) = rank A := by
        apply le_antisymm
        apply rank_mul_le_left
        have h₁ : A * Q.1 * (Q⁻¹).1 = A := by simp
        have h₂ : rank A ≤ rank (A * Q.1) := by
          nth_rw 1 [← h₁]
          apply rank_mul_le_left
        exact h₂
      have h2 : rank (P.1 * A * Q.1) = rank (A * Q.1) := by
        have h₁ : P.1 * (A * Q.1) = P.1 * A * Q.1 := by
          rw [← Matrix.mul_assoc]
        rw [← h₁]
        apply le_antisymm
        apply rank_mul_le_right
        have h₂ : (P⁻¹).1 * (P.1 * (A * Q.1)) = (A * Q.1) := by simp
        nth_rw 1 [← h₂]
        apply rank_mul_le_right
      rw [h2, h1]

theorem rankEquiv_to_rank_eq_on_Field [Field K] [Lattice K] [DecidableEq K] [DecidableLT K] (A B : Matrix (Fin m) (Fin n) K) :
    rankEquiv A B ↔ rank A = rank B := by
      constructor
      apply rankEquiv_to_rank_eq_on_CommRing
      rintro rank_eq
      rcases exists_rank_standard_form A with ⟨P₁, Q₁, hA⟩
      rcases exists_rank_standard_form B with ⟨P₂, Q₂, hB⟩
      have : P₁.1 * A * Q₁.1 = P₂.1 * B * Q₂.1 := by
        rw [hA, hB, rank_eq]
      have h : (P₂⁻¹).1 * (P₁.1 * A * Q₁.1) * (Q₂⁻¹).1 = B := by
        rw [this, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.mul_assoc, Units.mul_inv]
        simp
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc] at h
      have h' : ((P₂⁻¹) * P₁).1 * A * (Q₁ * (Q₂⁻¹)).1 = B := by
        simp
        rw [← Matrix.mul_assoc, ← coe_units_inv, ← coe_units_inv, h]
      use ((P₂⁻¹) * P₁)
      use (Q₁ * (Q₂⁻¹))
      rw [h']

instance rankEquiv_setoid [CommRing K] [Nontrivial K]: Setoid (Matrix (Fin m) (Fin n) K) where
  r := rankEquiv
  iseqv := by
    apply Equivalence.mk
    · intro A
      use 1, 1
      simp only [Matrix.one_mul, Matrix.mul_one, Units.val_one]
    · intro A B ⟨P, Q, h⟩
      use P⁻¹, Q⁻¹
      rw [h]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
      simp only [coe_units_inv, isUnits_det_units, nonsing_inv_mul, Matrix.one_mul,
        mul_nonsing_inv_cancel_right]
    · intro A B C ⟨P₁, Q₁, h₁⟩ ⟨P₂, Q₂, h₂⟩
      use P₂ * P₁, Q₁ * Q₂
      rw [h₂, h₁]
      simp only [← Matrix.mul_assoc, Units.val_mul]

theorem rankEquiv_to_rankStdBlock [Field K] [Lattice K] [DecidableEq K] [DecidableLT K] (A : Matrix (Fin m) (Fin n) K) :
    rankEquiv A (rankStdBlock K m n A.rank) := by
      rcases exists_rank_standard_form A with ⟨P, Q, h⟩
      use P; use Q; rw [h]

end Classification

section LU

open Equiv Equiv.Perm
variable {K : Type*} [Field K]

#check Matrix.BlockTriangular
#check Equiv.Perm.permMatrix

theorem Matrix.exists_LU_decomposition
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    ∃ (σ : Perm (Fin n)) (L U : Matrix (Fin n) (Fin n) K),
      L.BlockTriangular id   ∧
      U.BlockTriangular (-id) ∧
      (∀ i, L i i = 1) ∧
      (permMatrix K σ) * A = L * U := by
  sorry

end LU

section Fullrankfactorization

variable {K : Type*} [Field K] [Lattice K] [DecidableEq K] [Nontrivial K]
  [DecidableLT K] [NoZeroDivisors K]

def fullRank_factorization_of_rank_normal_form (m n r : ℕ) (M : Matrix (Fin m) (Fin n) K)
    (h_rm : r ≤ m)
    (h_elem : ∀ (i : Fin m) (j : Fin n),
      if i < r ∧ j < r ∧ (i : ℕ) = j then M i j ≠ 0 else M i j = 0) :
    {D : (Matrix (Fin m) (Fin r) K) × (Matrix (Fin r) (Fin n) K) // M = D.1 * D.2} := by
  constructor; swap
  · exact ⟨rankStdBlock K m r r,
    fun i j => if (i : ℕ) = j then M (Fin.mk i.1 (by omega)) j else 0⟩
  · ext i j
    unfold rankStdBlock; simp [mul_apply]; specialize h_elem i j
    let f (x : Fin r) := if (x : ℕ) = j then if i < r then if (i : ℕ) = x
      then M ⟨x, Fin.val_lt_of_le x h_rm⟩ j
    else 0 else 0 else 0
    split_ifs at h_elem with ifs
    · obtain ⟨ir, jr, ij⟩ := ifs
      have : M i j = f (Fin.mk i.1 (by omega)) := by
        unfold f; simp only [← ij]; exact Eq.symm (if_pos ir)
      rw [this]; symm
      apply Finset.sum_eq_single (Fin.mk i ir)
      · simp
        intro b bnei beqj
        have : b = ⟨i.1, ir⟩ := Fin.eq_mk_iff_val_eq.mpr (by simp [ij, beqj])
        contradiction
      · simp
    · rw [h_elem]; symm
      exact Fintype.sum_eq_zero f (by
        intro k; unfold f; simp only [ite_eq_right_iff]
        intro kj ir ik; simp [kj, ik] at ifs; omega)

theorem exists_fullRank_factorization {m n} (A : Matrix (Fin m) (Fin n) K) :
    ∃ (B : Matrix (Fin m) (Fin A.rank) K) (C : Matrix (Fin A.rank) (Fin n) K),
    A = B * C := by
  induction m with
  | zero =>
    use Fin.elim0, fun _ _ => 0
    exact ext_of_single_vecMul (congrFun rfl)
  | succ => induction n with
    | zero =>
      use fun _ _ => 0, fun _ j => Fin.elim0 j
      exact Eq.symm (ext_of_mulVec_single (congrFun rfl))
    | succ =>
      have ⟨P, Q, is_normal⟩ := Matrix.exists_rank_normal_form A
      have ⟨⟨M,N⟩, heq⟩ := fullRank_factorization_of_rank_normal_form _ _ A.rank
        (h_rm := Matrix.rank_le_height A) (h_elem := is_normal)
      use (P⁻¹).1 * M, N * (Q⁻¹).1
      calc
        _ = ((P⁻¹).1 * P.1) * A * (Q.1 * (Q⁻¹).1) := by
          simp_rw [Units.mul_inv Q, Units.inv_mul P]
          simp
        _ = (P⁻¹).1 * (P.1 * A * Q.1) * (Q⁻¹).1 := by simp [Matrix.mul_assoc]
        _ = _ := by simp [heq, Matrix.mul_assoc]


end Fullrankfactorization
