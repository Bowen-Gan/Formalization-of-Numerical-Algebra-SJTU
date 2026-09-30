import Mathlib

variable {α : Type*}

open Matrix Equiv

section Basic

variable {n m} (M : Matrix (Fin n) (Fin m) α)
def swap_rows  (i j : Fin n) : Matrix (Fin n) (Fin m) α :=
    M.submatrix  (swap i j : Perm (Fin n)) id

#eval swap_rows !![0,0;1,1] 0 1

variable {𝕜} [SMul 𝕜 α]

def scale_row (i : Fin n) (c : 𝕜) : Matrix (Fin n) (Fin m) α :=
    updateRow M i <| c • (M i)
#eval scale_row !![0,0;1,1] 1 2

def add_row_multiple [Add α] (i j : Fin n) (c : 𝕜) : Matrix (Fin n) (Fin m) α :=
    updateRow M i <| (M i) + c • (M j)

#eval add_row_multiple !![0,0;1,1] 0 1 2

-- def gaussian_update [Add α] [Mul α] [Sub α] [Neg α][NeZero n] [NeZero m]
--     (a b : α) (i k : Fin n) : (Fin m) → α :=  a • M k - b • M i

def gaussian_update [Add α] [Mul α] [Sub α] [Neg α][NeZero n] [NeZero m]
    (i k : Fin n) (a b : α) : (Fin m) → α :=
    if k ≤ i then M k
    else a • M k - b • M i
    -- gaussian_update M (M i ⟨i, hi⟩) (M k ⟨i, hi⟩) i k

def gaussian_update_row [Add α] [Mul α] [Sub α] [Neg α][NeZero n] [NeZero m]
  (i : Fin n) (hi : i < m):
  Matrix (Fin n) (Fin m) α :=
  -- gaussian_update (M i ⟨i, hi⟩) (M k ⟨i, hi⟩)
  -- gaussian_update (M 0 0) (M k 0)
  fun k =>
    gaussian_update M i k (M i ⟨i, hi⟩) (M k ⟨i, hi⟩)
    -- if k < i then M k
    -- else gaussian_update M (M i ⟨i, hi⟩) (M k ⟨i, hi⟩) i k
  -- gaussian_update M (M i ⟨i, hi⟩) (M k 0) k
  -- if k = 0 then M k else (M 0 0) • M k - (M k 0) • M 0

-- def gaussian_update_scale_row [Add α] [Mul α] [Sub α] [Neg α][NeZero n] [NeZero m]
--   (a : α) (k : Fin n) : (Fin m) → α := if k = 0 then M k else a • M k

-- def gaussian_update_scale [Add α] [Mul α] [Sub α] [Neg α][NeZero n] [NeZero m] :
--   Matrix (Fin n) (Fin m) α :=
--   fun k => gaussian_update_scale_row M ((M 0 0) * (M 0 0)) k

def A := !![2,1,3;1,2,8;9,10,11]
-- #eval gaussian_update_row !![2,1,3;1,2,8;9,10,11]
-- #eval gaussian_update_scale !![2,1,3;1,2,8;9,10,11] 2
end Basic

structure Gaussian (n m α) [Ring α] where
  P : Matrix (Fin n) (Fin n) α
  R : Matrix (Fin n) (Fin m) α
  Q : Matrix (Fin m) (Fin m) α
  M : Matrix (Fin n) (Fin m) α
  hm : P * M * Q = R
  -- P M Q = [I_r, 0; 0, 0]

section Gauss


variable {n m} [Ring α] (M : Gaussian n m α) [NeZero n] [NeZero m]

-- def finListRec {n : ℕ} (i : Fin n) : List (Fin n)
-- | ⟨i, hi⟩ =>
--   if h : i + 1 < n then
--     ⟨i, hi⟩ :: finListRec ⟨i + 1, h⟩
--   else
--     [⟨i, hi⟩]

#check List.finRange


def finListRec {n : ℕ} : Fin n → List (Fin n)
  | ⟨i, hi⟩ => go i hi
where
  go : ∀ (i : ℕ) (_ : i < n), List (Fin n)
    | i, hi =>
      if h : i + 1 < n then
        ⟨i, hi⟩ :: go (i + 1) h
      else
        [⟨i, hi⟩]

omit [NeZero n] in
def find_pivot_row [LinearOrder α] (M : Fin n → α) (i : Fin n): Fin n :=
  -- (List.argmax (abs ∘ M) (List.ofFn (id : Fin n → Fin n))).getD 0
  (List.argmax (abs ∘ M) (finListRec i)).getD 0
  -- (List.ofFn (abs ∘ M))
-- List Fin n [i, i + 1, ... , n - 1]

#check Finset.Ici
#check List.range
#check List.range'

#eval find_pivot_row (fun (i : Fin 4) =>(if i = 0 then -4 else 5 : ℤ) )

def gaussian_elimination_step_row (i : Fin n) (hi : i < m) (hM : M.R i ⟨i, hi⟩ ≠ 0)
    : Gaussian n m α where
  P :=
  -- gaussian_update_row M.P
    fun k =>
      gaussian_update M.P i k (M.R i ⟨i, hi⟩) (M.R k ⟨i, hi⟩)
  -- gaussian_update M.P (M.R i ⟨i, hi⟩) (M.R i ⟨i, hi⟩) k
  R := gaussian_update_row M.R i hi
  Q := M.Q
  M := M.M
  -- gaussian_update_scale M.M
  hm := sorry

#eval! gaussian_elimination_step_row (Gaussian.mk 1 !![(3 : ℤ),2;2,3] 1 !![(3 : ℤ),2;2,3] (by simp)) 0 (by simp) (by simp)

#eval! gaussian_elimination_step_row (Gaussian.mk 1 !![(2 : ℤ),2;2,3] 1 !![(2 : ℤ),2;2,3] (by simp)) 0 (by simp) (by simp)


#eval find_pivot_row (fun n : Fin 2 => if n = 0 then (2 : ℤ) else 3)
def gaussian_elimination_pivot_row [LinearOrder α] (i : Fin n) (hi : i < m) :
    Gaussian n m α :=
  let j := (find_pivot_row (fun k => M.R k ⟨i, hi⟩) i)
  if j = i then M
  else
    {
    P := swap_rows M.P j i
    R := swap_rows M.R j i
    Q := M.Q
    M := M.M
    hm := sorry
    }
#eval! gaussian_elimination_pivot_row (Gaussian.mk 1 !![(2 : ℤ),2;3,3] 1 !![(2 : ℤ),2;3,3] (by simp)) 0 (by simp)

def gaussian_elimination_row_aux [LinearOrder α] (M : Gaussian n m α) (hnm : n ≤ m) (idx : ℕ) (hidx : idx < n) :
    Gaussian n m α :=
  have hi := lt_of_lt_of_le hidx hnm
  let idxn : Fin n := ⟨idx, hidx⟩

  let pivotA := gaussian_elimination_pivot_row M idxn hi

  let nextA := if h : pivotA.R idxn ⟨idx, hi⟩ = 0 then pivotA
    else gaussian_elimination_step_row pivotA idxn hi h

  if ht : idx < n - 1 then
    gaussian_elimination_row_aux nextA hnm (idx + 1) (Nat.add_lt_of_lt_sub ht)--(Nat.lt_of_lt_pred ht)
  else
    nextA
termination_by n - idx
decreasing_by
  rw [tsub_lt_tsub_iff_left_of_le]
  simp
  linarith

def gaussian_elimination_row [LinearOrder α] (hnm : n ≤ m) : Gaussian n m α :=
  if h : 0 < n then gaussian_elimination_row_aux M hnm 0 h
  else M

#check Gaussian.mk 1 !![(2 : ℤ),2;2,3] 1 !![(2 : ℤ),2;2,3] (by simp)

#eval! gaussian_elimination_row (Gaussian.mk 1 !![(3 : ℤ),2;2,3] 1 !![(3 : ℤ),2;2,3] (by simp)) (by simp)
#eval (!![1, 0; -3, 3]) * (!![3, 2; 2, 3])

#eval! gaussian_elimination_row (Gaussian.mk 1 !![(2 : ℤ),2,4;7,3,1;3,9,10] 1 !![(2 : ℤ),2,4;7,3,1;3,9,10] (by simp)) (by simp)

#eval (!![0, 1, 0; 0, -3, 7; 378, -84, -56]) * (!![2, 2, 4; 7, 3, 1; 3, 9, 10])

end Gauss
