/-
Copyright (c) 2023 Boang Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boang Chen, Yi Peng, Chenyi Li
-/
import Na.Defs
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.Normed.Algebra.Spectrum
open Matrix Finset Filter Topology spectrum
open BigOperators

noncomputable section GS_4_2_5

variable {α : Type*} {n : ℕ} [NormedField α]
variable (A : Matrix (Fin n) (Fin n) α) (b : (Fin n) → α) (x0 : (Fin n) → α)
variable (hA : ∀ i, A i i ≠ 0)

local notation "‖" x "‖ᵥ₁" => @Norm.norm _ (PiLp.instNorm 1 fun _ ↦ α) x
local notation "‖" x "‖ᵥ₂" => @Norm.norm _ (PiLp.instNorm 2 fun _ ↦ α) x

-- local notation "l_i" alg => fun i ↦ (∑ j ∈ Ioi i, ‖Stationary_iterative.M alg i j‖)
-- local notation "u_i" alg => fun i ↦ (∑ j ∈ Iio i, ‖Stationary_iterative.M alg i j‖)
local notation "u_j" alg => fun j ↦ (∑ i ∈ Ioi j, ‖Stationary_iterative.M alg i j‖)
local notation "l_j" alg => fun j ↦ (∑ i ∈ Iio j, ‖Stationary_iterative.M alg i j‖)
local notation "sr" alg => ‖(u_j alg)‖
local notation "mur" alg => ‖fun (k : (Fin n)) ↦ (((l_j alg) k) / (1 - ((u_j alg) k)))‖

#check u_j (Jacobi A hA b x0)
#check fun (j : Fin n) ↦ ((u_j (Jacobi A hA b x0)) j)
#check fun j ↦ (1 - ((u_j (Jacobi A hA b x0)) j))
#check sr (Jacobi A hA b x0)
#check mur (Jacobi A hA b x0)

lemma norm_eq_max_abs (ja := Jacobi A hA b x0) : ∀ i, ‖(u_j ja) i‖ ≤ ‖u_j ja‖ := by
  intro i
  apply norm_le_pi_norm (f := (fun j ↦ ∑ i ∈ Ioi j, ‖ja.M i j‖))

lemma lemma_eq_0_1 (hA : ∀ i, A i i ≠ 0) :
    let A_inv := Matrix.diagonal (fun i => (A i i)⁻¹)
    A_inv = (A.diagPart)⁻¹ := by
  simp [Matrix.inv_def]
  ext i j
  simp [diagonal]
  rcases (ne_or_eq i j) with (neq | eq)
  · simp [neq]
  simp [eq]
  have : ∏ i ∈ univ.erase j, A i i = (∏ i , A i i) * (A j j)⁻¹ := by
    field_simp [hA j]
    rw [Finset.prod_erase_mul]
    simp
  rw [this]
  rw [← mul_assoc, inv_mul_cancel₀ (lemma_le_0_1 A hA), one_mul]

lemma lemma_eq_0_2 (hA : ∀ i, A i i ≠ 0) :
    -- let D := A.diagPart
    let L := -A.lowerPart
    -- let U := -A.upperPart
    let I : Matrix (Fin n) (Fin n) α := 1
    let Dinv : Matrix (Fin n) (Fin n) α := (A.diagnonzero_diagInvertable hA).unit.inv
    let M : Matrix (Fin n) (Fin n) α := (I - Dinv * L)
    ∀ i, IsUnit (M i i) := by
  intro L I Dinv M
  simp [M]
  intro i hi
  simp [I, Dinv, L] at hi
  rw [mul_apply] at hi
  have : ∀ j, A.diagPart⁻¹ i j * A.lowerPart j i = 0 := by
    intro j
    rcases (ne_or_eq i j) with (neq | eq)
    · rw [← lemma_eq_0_1 A hA]
      simp [lowerPart]
      intro hj
      left
      simp [diagonal]
      intro hj2
      contradiction
    · rw [← lemma_eq_0_1 A hA]
      rw [eq]
      simp [lowerPart]
  have : ∑ j, A.diagPart⁻¹ i j * A.lowerPart j i = 0 := by
    exact Fintype.sum_eq_zero (fun a ↦ A.diagPart⁻¹ i a * A.lowerPart a i) this
  rw [this] at hi
  simp at hi

instance : Invertible A.diagPart := by
  let A_inv := Matrix.diagonal (fun i => (A i i)⁻¹)
  refine ⟨A_inv, ?_, ?_⟩
  · ext i j
    simp [A_inv]
    -- #check ne_or_eq
    -- #check diagonal
    rcases (ne_or_eq i j) with (neq | eq)
    · simp [diagonal, neq]
    · rw [eq]
      simp [diagonal]
      exact inv_mul_cancel₀ (hA j)
  · ext i j
    simp [A_inv]
    rcases (ne_or_eq i j) with (neq | eq)
    · simp [neq]
    · rw [eq]
      simp
      exact mul_inv_cancel₀ (hA j)

lemma lemma_Invertable_1 :
    -- let D := A.diagPart
    let L := -A.lowerPart
    -- let U := -A.upperPart
    let I : Matrix (Fin n) (Fin n) α := 1
    let Dinv : Matrix (Fin n) (Fin n) α := (A.diagnonzero_diagInvertable hA).unit.inv
    let M : Matrix (Fin n) (Fin n) α := (I - Dinv * L)
    IsUnit M := by
  intro L I Dinv M
  have h_diag : ∀ i, IsUnit (M i i) := by
    exact lemma_eq_0_2 A hA
  have hi : I.BlockTriangular ⇑OrderDual.toDual := by
    simp [I]
    exact blockTriangular_one
  have hd : Dinv.BlockTriangular ⇑OrderDual.toDual := by
    simp [Dinv]
    haveI : Invertible A.diagPart := by exact instInvertibleMatrixFinDiagPart A hA
    apply Matrix.blockTriangular_inv_of_blockTriangular
    exact blockTriangular_diagonal fun i ↦ A i i
  have hl : L.BlockTriangular ⇑OrderDual.toDual := by
    unfold L
    unfold lowerPart
    unfold BlockTriangular
    simp
    intro i j hij hji
    absurd hij
    simpa using hji.le
  have h : M.BlockTriangular ⇑OrderDual.toDual := by
    have hld : (Dinv * L).BlockTriangular ⇑OrderDual.toDual := by
      exact Matrix.BlockTriangular.mul hd hl
    exact BlockTriangular.sub hi hld
  have det_eq : M.det = ∏ i : (Fin n), M i i := det_of_lowerTriangular M h
  have det_unit : IsUnit M.det := by
    rw [det_eq]
    simp
    push_neg
    simp at h_diag
    push_neg at h_diag
    exact lemma_le_0_1 M h_diag
  exact (isUnit_iff_isUnit_det M).mpr det_unit

lemma lemma_eq_1 {gs} (hgs : gs = GaussSeidel A hA b x0) :
    -- let D := A.diagPart
    let L := -A.lowerPart
    let U := -A.upperPart
    let I : Matrix (Fin n) (Fin n) α := 1
    let Dinv : Matrix (Fin n) (Fin n) α := (A.diagnonzero_diagInvertable hA).unit.inv
    let Minv : Matrix (Fin n) (Fin n) α := (lemma_Invertable_1 A hA).unit.inv
    gs.M = Minv * (Dinv * U * Minv) * (I - Dinv * L) := by
  intro L U I Dinv Minv
  have : Minv * (I - Dinv * L) = 1 := by
    -- simp only [Minv]
    have : Minv = (I - Dinv * L)⁻¹ := by
      simp [Minv, Dinv, I, L]
    rw [this]
    rw [Matrix.nonsing_inv_mul]
    rw [← Matrix.isUnit_iff_isUnit_det]
    exact lemma_Invertable_1 A hA
  have :  Minv * (Dinv * U * Minv) * (I - Dinv * L) = Minv * Dinv * U := by
    calc
      _ = Minv * Dinv * U * (Minv * (I - Dinv * L)) := by group
      _ = Minv * Dinv * U := by
        rw [this]; simp
  rw [this]
  unfold Stationary_iterative.M
  rw [hgs]; unfold GaussSeidel
  simp
  simp [Minv, Dinv, U]
  have :  (A.diagPart + A.lowerPart)⁻¹ =(1 + A.diagPart⁻¹ * A.lowerPart)⁻¹ * A.diagPart⁻¹ := by
    rw [← Matrix.mul_inv_rev]
    congr
    rw [mul_add]; simp
    rw [← Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv]
    · simp
    rw [← Matrix.isUnit_iff_isUnit_det]
    apply Matrix.diagnonzero_diagInvertable
    exact hA
  rw [this]

variable {gs : Stationary_iterative x0} {hgs : gs = GaussSeidel A hA b x0} {ja : Stationary_iterative x0} {hja : gs = Jacobi A hA b x0}
#check lemma_eq_1 A b x0 hA hgs

#check spectralRadius

def Matrix.Similar (B : Matrix (Fin n) (Fin n) α) (C : Matrix (Fin n) (Fin n) α) := ∃ (P : Matrix (Fin n) (Fin n) α), IsUnit P ∧ B = P⁻¹ * C * P

theorem SimilarMatrix_eq_eigenvalues (B : Matrix (Fin n) (Fin n) α) (C : Matrix (Fin n) (Fin n) α) :
    Matrix.Similar B C → spectrum α B = spectrum α C := by
  intro h
  simp [Similar] at h
  rcases h with ⟨P, ⟨hP, hB⟩⟩
  rw [hB]
  simp [spectrum, resolventSet]
  simp [isUnit_iff_isUnit_det]
  ext lambda
  simp
  -- simp [algebraMap]
  -- rw [Algebra.algebraMap_eq_smul_one lambda]
  let lambdaI := lambda • (1 : Matrix (Fin n) (Fin n) α)
  have h1 : algebraMap α (Matrix (Fin n) (Fin n) α) lambda = lambdaI := by
    rw [Algebra.algebraMap_eq_smul_one lambda]
  rw [h1]
  have eq0 : IsUnit P.det := by
    exact (isUnit_iff_isUnit_det P).mp hP
  have eq1 : (lambdaI - P⁻¹ * C * P) = P⁻¹ * (lambdaI - C)* P := by
    rw [mul_sub, sub_mul]
    simp
    have : P⁻¹ * lambdaI = lambdaI * P⁻¹ := by
      simp [lambdaI]
    rw [this]
    rw [nonsing_inv_mul_cancel_right]
    exact eq0
  have eq2 : (lambdaI - P⁻¹ * C * P).det = (lambdaI - C).det := by
    rw [eq1, det_mul, det_mul]
    rw [mul_comm, ← mul_assoc, ← det_mul]
    have : (P * P⁻¹).det = 1 := by
      rw [Matrix.mul_nonsing_inv]
      · simp
      · exact eq0
    rw [this]
    simp
  rw [eq2]

theorem SimilarMatrix_eq_spectralRadius (B : Matrix (Fin n) (Fin n) α) (C : Matrix (Fin n) (Fin n) α) : Matrix.Similar B C → (spectralRadius α B).toNNReal = (spectralRadius α C).toNNReal := by
  intro h
  have eq1 := SimilarMatrix_eq_eigenvalues B C
  simp [Similar] at h
  rcases h with ⟨P, ⟨hP, hB⟩⟩
  -- apply SpectrumRestricts.spectralRadius_eq
  sorry

lemma lemma_eq_2 {gs}
    (hgs : gs = GaussSeidel A hA b x0) :
    let _ := A.diagPart
    let _ := -A.lowerPart
    let U := -A.upperPart
    let _ : Matrix (Fin n) (Fin n) α := 1
    let Dinv : Matrix (Fin n) (Fin n) α := (A.diagnonzero_diagInvertable hA).unit.inv
    let Minv : Matrix (Fin n) (Fin n) α := (lemma_Invertable_1 A hA).unit.inv
    (spectralRadius α gs.M).toNNReal = (spectralRadius α (Dinv * U * Minv)).toNNReal := by
  intro D L U I Dinv Minv
  have eq1 := lemma_eq_1 A b x0 hA hgs
  simp at eq1 L U I Dinv Minv
  apply SimilarMatrix_eq_spectralRadius gs.M (Dinv * U * Minv)
  simp [Similar]
  use (I - Dinv * L)
  constructor
  · exact lemma_Invertable_1 A hA
  · simp [U, L, I, Dinv, Minv]
    exact eq1

#check lemma_eq_2 A b x0 hA hgs

#check (GaussSeidel A hA b x0).x 1

-- The same in file GaussDef
instance : IsUnit (A.diagPart + A.lowerPart) := by
  have det_unit : IsUnit (A.diagPart + A.lowerPart).det := by
    exact lemma_3_1 A hA
  exact (isUnit_iff_isUnit_det (A.diagPart + A.lowerPart)).mpr det_unit

instance : Invertible (A.diagPart + A.lowerPart) := by
  have := diagnonzero_diag_minus_lowerPart_Invertable A hA
  simp at this
  exact IsUnit.invertible this

lemma lemma_eq_3_1 (hA : ∀ i, A i i ≠ 0) : IsUnit A.diagPart.det := by
  have h_diag : ∀ i, (A.diagPart i i) ≠ 0 := by
    simpa
  have hd : A.diagPart.BlockTriangular ⇑OrderDual.toDual := by
    simp [diagPart]
    exact blockTriangular_diagonal fun i ↦ A i i
  have det_eq : A.diagPart.det = ∏ i : (Fin n), A.diagPart i i := det_of_lowerTriangular A.diagPart hd
  have det_unit : IsUnit A.diagPart.det := by
    rw [det_eq]
    simp
    push_neg
    simp at h_diag
    push_neg at h_diag
    exact lemma_le_0_1 A h_diag
  exact det_unit

#check mulVec_sub
lemma lemma_eq_3 {gs} {ja} (hgs : gs = GaussSeidel A hA b x0) (hja : ja = Jacobi A hA b x0) (k : ℕ) (i : (Fin n)) :
    let D := A.diagPart
    let L := -A.lowerPart
    let U := -A.upperPart
    let I : Matrix (Fin n) (Fin n) α := 1
    let Dinv : Matrix (Fin n) (Fin n) α := (A.diagnonzero_diagInvertable hA).unit.inv
    gs.x (k + 2) - gs.x (k + 1) = (Dinv * L) *ᵥ (gs.x (k + 2) - gs.x (k + 1)) + (Dinv * U) *ᵥ (gs.x (k + 1) - gs.x k) := by
  intro D L U I Dinv
  have eq_1 (p : ℕ) := @GaussSeidel.update _ _ _ A hA b x0 gs p
  have eq1 (m : ℕ) : (D - L) *ᵥ (gs.x (m + 1)) = U *ᵥ (gs.x m) + b := by
    rw [eq_1 m]
    simp [D, L, U]
    rw [mulVec_add (A.diagPart + A.lowerPart) (gs.M *ᵥ gs.x m) gs.g]
    refine Mathlib.Tactic.LinearCombination.add_eq_eq ?_ ?_
    · simp [hgs, GaussSeidel]
      rw [← mul_assoc, mul_nonsing_inv (A.diagPart + A.lowerPart) (lemma_3_1 A hA)]
      simp
    · simp [hgs, GaussSeidel]
      rw [mul_nonsing_inv (A.diagPart + A.lowerPart) (lemma_3_1 A hA)]
      simp
  have eq2 : D *ᵥ (gs.x (k + 2) - gs.x (k + 1)) = L *ᵥ (gs.x (k + 2) - gs.x (k + 1)) + (L - D + U) *ᵥ gs.x (k + 1) + b := by
    rw [mulVec_sub, mulVec_sub,add_mulVec, add_assoc, add_assoc, ← eq1 (k + 1)]
    simp [sub_mulVec, add_assoc]
    ring
  have eq3 : (L - D + U) *ᵥ gs.x (k + 1) + b = U *ᵥ (gs.x (k + 1) - gs.x k) := by
    have : (L - D) *ᵥ gs.x (k + 1) = - (U *ᵥ gs.x k + b) := by
      rw [← eq1 k]
      rw [← neg_mulVec]
      simp
    rw [add_mulVec, add_assoc, this, mulVec_sub]
    group
  have eq4 : D *ᵥ (gs.x (k + 2) - gs.x (k + 1)) = L *ᵥ (gs.x (k + 2) - gs.x (k + 1)) + U *ᵥ (gs.x (k + 1) - gs.x k) := by
    rw [eq2, add_assoc, eq3]
  have eq5 : (gs.x (k + 2) - gs.x (k + 1)) = Dinv *ᵥ (L *ᵥ (gs.x (k + 2) - gs.x (k + 1))) + Dinv *ᵥ (U *ᵥ (gs.x (k + 1) - gs.x k)) := by
    rw [← mulVec_add]
    simp [Dinv]
    simp [D] at eq4
    rw [← eq4]
    simp
    sorry
  rw [eq5]
  simp
  sorry

-- #check lemma_eq_3 A b x0 hA hgs hja
lemma lemma_eq_4_1_1 :
    let B : (Matrix (Fin n) (Fin n) α) := fun m n => if m ≥ n then 0 else -A m n * (A m m)⁻¹
    (-(A.diagPart⁻¹ * A.lowerPart)) = B := by
  sorry

lemma lemma_eq_4_1_2 (i : (Fin n)) (k : ℕ) (x : ℕ -> (Fin n) → α) :
    let B : (Matrix (Fin n) (Fin n) α) := fun m n => if m ≥ n then 0 else -A m n * (A m m)⁻¹
    ∑ j ∈ Ioi i, ((A.diagPart⁻¹ * (A.diagPart - A)) i j) * (x (k + 2) j - x (k + 1) j) = (B *ᵥ (x (k + 2) - x (k + 1))) i := by
  sorry

lemma lemma_eq_4_1 {gs} {ja} (_ : gs = GaussSeidel A hA b x0) (hja : ja = Jacobi A hA b x0) (k : ℕ) (i : (Fin n)) :
    (-(A.diagPart⁻¹ * A.lowerPart) *ᵥ (gs.x (k + 2) - gs.x (k + 1))) i = ∑ j ∈ Ioi i, ja.M i j * (gs.x (k + 2) j - gs.x (k + 1) j) := by
  have eq_1 := lemma_eq_4_1_1 A
  have eq_2 := lemma_eq_4_1_2 A i k gs.x
  rw [hja]
  simp [Jacobi]
  rw [eq_2, eq_1]

lemma lemma_eq_4_2_1 :
    let B : (Matrix (Fin n) (Fin n) α) := fun m n => if m ≥ n then 0 else -A m n * (A m m)⁻¹
    (-(A.diagPart⁻¹ * A.upperPart)) = B := by
  sorry

lemma lemma_eq_4_2_2 (i : (Fin n)) (k : ℕ) (x : ℕ -> (Fin n) → α) :
    let B : (Matrix (Fin n) (Fin n) α) := fun m n => if m ≥ n then 0 else -A m n * (A m m)⁻¹
    ∑ j ∈ Iio i, ((A.diagPart⁻¹ * (A.diagPart - A)) i j) * (x (k + 1) j - x k j) = (B *ᵥ (x (k + 1) - x k)) i := by
  sorry

lemma lemma_eq_4_2 {gs} {ja} (_ : gs = GaussSeidel A hA b x0) (hja : ja = Jacobi A hA b x0) (k : ℕ) (i : (Fin n)) :
    (-(A.diagPart⁻¹ * A.upperPart) *ᵥ (gs.x (k + 1) - gs.x k)) i = ∑ j ∈ Iio i, ja.M i j * (gs.x (k + 1) j - gs.x k j) := by
  have eq_1 := lemma_eq_4_2_1 A
  have eq_2 := lemma_eq_4_2_2 A i k gs.x
  rw [hja]
  simp [Jacobi]
  rw [eq_2, eq_1]

lemma lemma_eq_4 {gs} {ja} (hgs : gs = GaussSeidel A hA b x0) (hja : ja = Jacobi A hA b x0) (k : ℕ) (i : (Fin n)) :
    gs.x (k + 2) i - gs.x (k + 1) i = ∑ j ∈ Ioi i, ja.M i j * (gs.x (k + 2) j - gs.x (k + 1) j) + ∑ j ∈ Iio i, ja.M i j * (gs.x (k + 1) j - gs.x k j) := by
  have eq1 := lemma_eq_3 A b x0 hA hgs hja k i
  simp at eq1
  have eq2 : gs.x (k + 2) i - gs.x (k + 1) i = (gs.x (k + 2) - gs.x (k + 1)) i := by
    rfl
  have eq3 {x : (Fin n) → α} {y : (Fin n) → α} : x i + y i = (x + y) i := by
    rfl
  rw [eq2, eq1, ← eq3]
  have := lemma_eq_4_1 A b x0 hA hgs hja
  rw [this]
  have := lemma_eq_4_2 A b x0 hA hgs hja
  rw [this]

#check norm
lemma lemma_le_5 (gs := GaussSeidel A hA b x0) (ja := Jacobi A hA b x0) (k : ℕ) (i : (Fin n)) :
    ‖∑ j ∈ Ioi i, ja.M i j * (gs.x (k + 2) j - gs.x (k + 1) j) + ∑ j ∈ Iio i, ja.M i j * (gs.x (k + 1) j - gs.x k j)‖ ≤ (∑ j ∈ Ioi i, ‖ja.M i j‖ * ‖gs.x (k + 2) j - gs.x (k + 1) j‖ + ∑ j ∈ Iio i, ‖ja.M i j‖ * ‖gs.x (k + 1) j - gs.x k j‖) := by
  have le_1 : ‖∑ j ∈ Ioi i, ja.M i j * (gs.x (k + 2) j - gs.x (k + 1) j) + ∑ j ∈ Iio i, ja.M i j * (gs.x (k + 1) j - gs.x k j)‖ ≤ ‖∑ j ∈ Ioi i, ja.M i j * (gs.x (k + 2) j - gs.x (k + 1) j)‖ + ‖∑ j ∈ Iio i, ja.M i j * (gs.x (k + 1) j - gs.x k j)‖ := by
    let a := ∑ j ∈ Ioi i, ja.M i j * (gs.x (k + 2) j - gs.x (k + 1) j)
    let b := ∑ j ∈ Iio i, ja.M i j * (gs.x (k + 1) j - gs.x k j)
    exact norm_add_le a b
  have le_2 : ∀ (set : Finset (Fin n)) (m : ℕ), ‖∑ j ∈ set, ja.M i j * (gs.x (m + 1) j - gs.x m j)‖ ≤ ∑ j ∈ set, ‖ja.M i j * (gs.x (m + 1) j - gs.x m j)‖ := by
    intro set m
    apply norm_sum_le
  have le_3 : ∀ (set : Finset (Fin n)) (m : ℕ), ∑ j ∈ set, ‖ja.M i j * (gs.x (m + 1) j - gs.x m j)‖ ≤ ∑ j ∈ set, ‖ja.M i j‖ * ‖gs.x (m + 1) j - gs.x m j‖ := by
    intro set m
    apply sum_le_sum
    intro j hj
    apply norm_mul_le
  calc
    ‖∑ j ∈ Ioi i, ja.M i j * (gs.x (k + 2) j - gs.x (k + 1) j) + ∑ j ∈ Iio i, ja.M i j * (gs.x (k + 1) j - gs.x k j)‖ ≤ ‖∑ j ∈ Ioi i, ja.M i j * (gs.x (k + 2) j - gs.x (k + 1) j)‖ + ‖∑ j ∈ Iio i, ja.M i j * (gs.x (k + 1) j - gs.x k j)‖ := by
      exact le_1
    _ ≤ ∑ j ∈ Ioi i, ‖ja.M i j * (gs.x (k + 2) j - gs.x (k + 1) j)‖ + ∑ j ∈ Iio i, ‖ja.M i j * (gs.x (k + 1) j - gs.x k j)‖ := by
      exact add_le_add (le_2 (Ioi i) (k + 1)) (le_2 (Iio i) k)
    _ ≤ ∑ j ∈ Ioi i, ‖ja.M i j‖ * ‖gs.x (k + 2) j - gs.x (k + 1) j‖ + ∑ j ∈ Iio i, ‖ja.M i j‖ * ‖gs.x (k + 1) j - gs.x k j‖ := by
      exact add_le_add (le_3 (Ioi i) (k + 1)) (le_3 (Iio i) k)

lemma lemma_le_6 {gs} {ja} (hgs : gs = GaussSeidel A hA b x0) (hja : ja = Jacobi A hA b x0) (k : ℕ) :
    ∑ i , ‖gs.x (k + 2) i - gs.x (k + 1) i‖ ≤ ∑ i , (∑ j ∈ Ioi i, ‖ja.M i j‖ * ‖gs.x (k + 2) j - gs.x (k + 1) j‖ + ∑ j ∈ Iio i, ‖ja.M i j‖ * ‖gs.x (k + 1) j - gs.x k j‖) := by
  apply sum_le_sum
  intro i hi
  rw [lemma_eq_4 A b x0 hA hgs hja k i]
  exact lemma_le_5 A b x0 hA gs ja k i

/--
TODO : To prove this lemma, we should establish an equality between two double summations of matrix-vector product terms.

∑ j , (∑ i ∈ Ioi j, ‖ja.M i j‖ * ‖gs.x (k + 2) j - gs.x (k + 1) j‖ + ∑ i ∈ Iio j, ‖ja.M i j‖ * ‖gs.x (k + 1) j - gs.x k j‖) = ∑ i , (∑ j ∈ Ioi i, ‖ja.M i j‖ * ‖gs.x (k + 2) j - gs.x (k + 1) j‖ + ∑ j ∈ Iio i, ‖ja.M i j‖ * ‖gs.x (k + 1) j - gs.x k j‖)

The left side sums over all rows `i`, then for each row:
- a.1 Sums above-diagonal terms for i (Ioi i) using iteration (k+2) and (k+1) differences
- a.2 Sums below-diagonal terms for i (Iio i) using iteration (k+1) and k differences

The right side reverses the summation order, first summing over columns `j`, then for each column:
- b.1 Sums below-diagonal terms for j (Ioi j) using iteration (k+2) and (k+1) differences (equals to a.1)
- b.2 Sums above-diagonal terms for j (Iio j) using iteration (k+1) and k differences (equals to a.2)

This inequality will be useful for comparing convergence rates between Jacobi and Gauss-Seidel iterations.
-/
lemma lemma_le_7 (gs := GaussSeidel A hA b x0) (ja := Jacobi A hA b x0) (k : ℕ) (i : (Fin n)) :
    ∑ i , ‖gs.x (k + 2) i - gs.x (k + 1) i‖ ≤ ∑ j , (∑ i ∈ Ioi j, ‖ja.M i j‖ * ‖gs.x (k + 2) j - gs.x (k + 1) j‖ + ∑ i ∈ Iio j, ‖ja.M i j‖ * ‖gs.x (k + 1) j - gs.x k j‖) := by
  sorry

lemma lemma_le_8 (gs := GaussSeidel A hA b x0) (ja := Jacobi A hA b x0) (k : ℕ) (i : (Fin n)) :
    ∑ i , ‖gs.x (k + 2) i - gs.x (k + 1) i‖ ≤ ∑ j , (((u_j ja) j) * ‖gs.x (k + 2) j - gs.x (k + 1) j‖ + ((l_j ja) j) * ‖gs.x (k + 1) j - gs.x k j‖) := by
  have eq1 : ∀ (j : Fin n), ((u_j ja) j) * ‖gs.x (k + 2) j - gs.x (k + 1) j‖ = ∑ i ∈ Ioi j, ‖ja.M i j‖ * ‖gs.x (k + 2) j - gs.x (k + 1) j‖ := by
    intro j
    simp
    apply sum_mul
  have eq2 : ∀ j, ((l_j ja) j) * ‖gs.x (k + 1) j - gs.x k j‖ = ∑ i ∈ Iio j, ‖ja.M i j‖ * ‖gs.x (k + 1) j - gs.x k j‖ := by
    intro j
    simp
    apply sum_mul
  apply le_trans (lemma_le_7 A b x0 hA gs ja k i)
  apply sum_le_sum
  intro i hi
  simp
  rw [eq1, eq2]

lemma lemma_le_9 (gs := GaussSeidel A hA b x0) (ja := Jacobi A hA b x0) (k : ℕ) (i : (Fin n)) :
    ∑ j , (1 - ((u_j ja) j)) * ‖gs.x (k + 2) j - gs.x (k + 1) j‖ ≤ ∑ j , ((l_j ja) j) * ‖gs.x (k + 1) j - gs.x k j‖ := by
  have eq1 : ∑ j , (1 - ((u_j ja) j)) * ‖gs.x (k + 2) j - gs.x (k + 1) j‖ = ∑ j , ‖gs.x (k + 2) j - gs.x (k + 1) j‖ - ∑ j , ((u_j ja) j) * ‖gs.x (k + 2) j - gs.x (k + 1) j‖ := by
    have : ∀ j, (1 - ((u_j ja) j)) * ‖gs.x (k + 2) j - gs.x (k + 1) j‖ = ‖gs.x (k + 2) j - gs.x (k + 1) j‖ - ((u_j ja) j) * ‖gs.x (k + 2) j - gs.x (k + 1) j‖ := by
      intro j
      apply one_sub_mul
    rw [← Finset.sum_sub_distrib]
    apply sum_congr
    · rfl
    · intro j hj
      exact this j
  have eq2 : ∑ j , (((u_j ja) j) * ‖gs.x (k + 2) j - gs.x (k + 1) j‖ + ((l_j ja) j) * ‖gs.x (k + 1) j - gs.x k j‖) = ∑ j , (((u_j ja) j) * ‖gs.x (k + 2) j - gs.x (k + 1) j‖) + ∑ j , (((l_j ja) j) * ‖gs.x (k + 1) j - gs.x k j‖) := by
    exact sum_add_distrib
  rw [eq1]
  have := lemma_le_8 A b x0 hA gs ja k i
  rw [eq2] at this
  exact tsub_le_iff_left.mpr this

/--
TODO : Here are some lemmas about matrix 1-norm and the sum of absolute values of some entries in matrix `M`.
-/
lemma lemma_eq_10_1 (M : Matrix (Fin n) (Fin n) α) (j : (Fin n)) : ∑ i , ‖M i j‖ < ‖M‖₁ := by
  unfold LoneNorm
  sorry

#check Ioi
lemma lemma_le_10_2 (M : Matrix (Fin n) (Fin n) α) (j : (Fin n)) (set : Finset (Fin n)): ∑ i ∈ set, ‖M i j‖ < ‖M‖₁ := by
  have le1 := lemma_eq_10_1 M j
  sorry

lemma lemma_le_10_3 (M : Matrix (Fin n) (Fin n) α) : ‖fun (j : (Fin n)) ↦ ∑ i ∈ (Ioi j), ‖M i j‖‖ < ‖M‖₁ := by
  -- have le1 := lemma_eq_10_2 M j set
  unfold LoneNorm
  sorry

#check mur (Jacobi A hA b x0)
lemma lemma_le_10 (gs := GaussSeidel A hA b x0) (ja := Jacobi A hA b x0) (hja : ‖ja.M‖₁ < 1) (k : ℕ) :
    ∑ j , ((l_j ja) j) * ‖gs.x (k + 1) j - gs.x k j‖ ≤ (mur ja) * ∑ j , (1 - ((u_j ja) j)) * ‖gs.x (k + 1) j - gs.x k j‖ := by
  have le_0 : ∀ j, (1 - ∑ i ∈ Ioi j, ‖ja.M i j‖) > 0 := by
    intro j
    have le1 := lemma_le_10_2 ja.M j (Ioi j)
    linarith
  have eq1 : ∀ j, ((l_j ja) j) * ‖gs.x (k + 1) j - gs.x k j‖ = (((l_j ja) j) / (1 - ((u_j ja) j))) * (1 - ((u_j ja) j)) * ‖gs.x (k + 1) j - gs.x k j‖ := by
    intro j
    have := le_0 j
    simp
    left
    field_simp
  rw [mul_sum]
  simp
  have le_1 : ∀ j, (((l_j ja) j) / (1 - ((u_j ja) j))) ≤ (mur ja) := by
    intro j
    simp
    let k := fun j ↦ (((l_j ja) j) / (1 - ((u_j ja) j)))
    have le1 : k j ≤ ‖k j‖ := by
      exact Real.le_norm_self (k j)
    have le2 := norm_le_pi_norm (f := k) j
    exact le_trans le1 le2
  have le_2 : ∀ j, 0 ≤ ‖gs.x (k + 1) j - gs.x k j‖ := by
    intro j
    exact norm_nonneg _
  have le_3 : ∀ j, ((l_j ja) j) * ‖gs.x (k + 1) j - gs.x k j‖ ≤ (mur ja) * ((1 - ((u_j ja) j)) * ‖gs.x (k + 1) j - gs.x k j‖) := by
    intro j
    rw [← mul_assoc, eq1]
    simp
    apply mul_le_mul_of_nonneg_right _ (le_2 j)
    have := le_1 j
    simp at this
    have le_4: 0 ≤ (1 - ∑ i ∈ Ioi j, ‖ja.M i j‖) := by
      have := le_0 j
      linarith
    apply mul_le_mul_of_nonneg_right this le_4
  apply sum_le_sum
  intro j hj
  have := le_3 j
  simp at this
  exact this

lemma lemma_le_11 (gs := GaussSeidel A hA b x0) (ja := Jacobi A hA b x0) (hja : ‖ja.M‖₁ < 1) (k : ℕ) (i : (Fin n)) :
    ∑ j , (1 - ((u_j ja) j)) * ‖gs.x (k + 1) j - gs.x k j‖ ≤ ((mur ja) ^ k) * ∑ j , (1 - ((u_j ja) j)) * ‖gs.x 1 j - gs.x 0 j‖ := by
  -- using induction
  have le1 : ∀ m, ∑ j , (1 - ((u_j ja) j)) * ‖gs.x (m + 2) j - gs.x (m + 1) j‖ ≤ (mur ja) * ∑ j , (1 - ((u_j ja) j)) * ‖gs.x (m + 1) j - gs.x m j‖ := by
    intro m
    have le_9 := lemma_le_9 A b x0 hA gs ja m i
    have le_10 := lemma_le_10 A b x0 hA gs ja hja m
    exact le_trans le_9 le_10
  induction' k with m hm
  · simp
  · have eq_1 : (mur ja) ^ (m + 1) = (mur ja) * (mur ja) ^ m := by
      rw [mul_comm]
      exact pow_succ (mur ja) m
    rw [eq_1]
    have le_1 : 0 ≤ (mur ja) := by
      exact norm_nonneg _
    rw [mul_assoc]
    apply le_trans (le1 m) _
    apply mul_le_mul_of_nonneg_left hm le_1

lemma lemma_le_12 (ja := Jacobi A hA b x0) (j : Fin n) :
    (1 - (sr ja)) ≤ (1 - ((u_j ja) j)) := by
  simp
  have le_1 : ∑ i ∈ Ioi j, ‖ja.M i j‖ ≤ ‖∑ i ∈ Ioi j, ‖ja.M i j‖‖ := by
    exact Real.le_norm_self (∑ i ∈ Ioi j, ‖ja.M i j‖)
  have le_2 := norm_le_pi_norm (f := (fun j ↦ ∑ i ∈ Ioi j, ‖ja.M i j‖)) j
  have := le_trans le_1 le_2
  linarith

lemma lemma_le_13 (ja := Jacobi A hA b x0) (j : Fin n) :
    (1 - ((u_j ja) j)) ≤ 1 := by
  have le_1 : 0 ≤ ((u_j ja) j) := by
    simp
    apply sum_nonneg
    intro i hi
    exact norm_nonneg (ja.M i j)
  linarith

lemma lemma_le_14 (ja := Jacobi A hA b x0) (j : (Fin n)) :
    (1 - (sr ja)) ≤ 1 := by
  exact le_trans (lemma_le_12 A b x0 hA ja j) (lemma_le_13 A b x0 hA ja j)

lemma lemma_le_15 (gs := GaussSeidel A hA b x0) (ja := Jacobi A hA b x0) (k : ℕ) :
    (1 - (sr ja)) * ∑ j , ‖gs.x (k + 1) j - gs.x k j‖ ≤ ∑ j , (1 - ((u_j ja) j)) * ‖gs.x (k + 1) j - gs.x k j‖ := by
  rw [mul_sum]
  have := lemma_le_12 A b x0 hA ja
  apply sum_le_sum
  intro j hj
  have le_1 := this j
  have le_2 : 0 ≤ ‖gs.x (k + 1) j - gs.x k j‖ := by
    exact norm_nonneg _
  exact mul_le_mul_of_nonneg_right le_1 le_2

lemma lemma_le_16 (gs := GaussSeidel A hA b x0) (ja := Jacobi A hA b x0) :
    ∑ j , (1 - ((u_j ja) j)) * ‖gs.x 1 j - gs.x 0 j‖ ≤ ∑ j , ‖gs.x 1 j - gs.x 0 j‖ := by
  have le_1 := lemma_le_13 A b x0 hA ja
  apply sum_le_sum
  intro j hj
  have le_2 : 0 ≤ ‖gs.x 1 j - gs.x 0 j‖ := by
    exact norm_nonneg _
  have := mul_le_mul_of_nonneg_right (le_1 j) le_2
  rw [one_mul] at this
  exact this

lemma lemma_le_17 (gs := GaussSeidel A hA b x0) (ja := Jacobi A hA b x0) (hja : ‖ja.M‖₁ < 1) (k : ℕ) (i : (Fin n)) :
    (1 - (sr ja)) * ∑ j , ‖gs.x (k + 1) j - gs.x k j‖ ≤ ((mur ja) ^ k) * ∑ j , ‖gs.x 1 j - gs.x 0 j‖ := by
  have le_1 := lemma_le_15 A b x0 hA gs ja k
  have le_2 := lemma_le_11 A b x0 hA gs ja hja k i
  have le_3 := lemma_le_16 A b x0 hA gs ja
  apply le_trans (le_trans le_1 le_2) _
  have le_4 : 0 ≤ (mur ja) ^ k := by
    apply pow_nonneg
    exact norm_nonneg _
  apply mul_le_mul_of_nonneg_left le_3 le_4

/--
This is a lemma about vector 1-norm and the sum of absolute values of entries in vector `x`.
-/
lemma lemma_eq_18_1 (x : (Fin n) → α) :
    ‖ x ‖ᵥ₁ = ∑ j , ‖x j‖ := by
  sorry

lemma lemma_le_18 (gs := GaussSeidel A hA b x0) (ja := Jacobi A hA b x0) (hja : ‖ja.M‖₁ < 1) (k : ℕ) (i : (Fin n)) :
    (1 - (sr ja)) * ‖(gs.x (k + 1)) - (gs.x k)‖ᵥ₁ ≤ ((mur ja) ^ k) * ‖gs.x 1 - gs.x 0‖ᵥ₁ := by
  have := lemma_le_17 A b x0 hA gs ja hja k i
  have eq_1 := lemma_eq_18_1 ((gs.x (k + 1)) - (gs.x k))
  have eq_2 := lemma_eq_18_1 (gs.x 1 - gs.x 0)
  rw [eq_1, eq_2]
  exact this

lemma lemma_eq_19_1 (x : ℕ → (Fin n) → α) (k : ℕ) :
    x k - x 0 = ∑ j ∈ range k , (x (j + 1) - x j) := by
  induction' k with m hm
  · simp
  have eq_1 : ∑ j ∈ range (m + 1), (x (j + 1) - x j) = x (m + 1) - x m + ∑ j ∈ range m, (x (j + 1) - x j) := by
    apply sum_range_succ_comm
  rw [eq_1 ,← hm]
  simp

lemma lemma_eq_19 (gs := GaussSeidel A hA b x0) (k : ℕ) :
    gs.x k - gs.x 0 = ∑ j ∈ range k , (gs.x (j + 1) - gs.x j) := by
  exact lemma_eq_19_1 gs.x k

/--
TODO : Here are some lemmas about convergence.
-/
lemma lemma_eq_20 (x : ℕ → (Fin n) → α) (x_star : (Fin n) → α) (hx : Tendsto x atTop (𝓝 x_star)) (k : ℕ):
    Tendsto (fun (n : ℕ) ↦ ∑ i ∈ range n \ range k, (x (i + 1) - x i)) atTop (𝓝 (x_star - x k)) := by
  have eq_1 : ∀ n, ∑ i ∈ range n \ range k, (x (i + 1) - x i) = ∑ i ∈ range n , (x (i + 1) - x i) - ∑ i ∈ range k, (x (i + 1) - x i) := by
    intro n
    sorry
  have eq_4 : ∀ n, ∑ i ∈ range n \ range k, (x (i + 1) - x i) = x n - x k := by
    intro n
    rw [eq_1 n, ← lemma_eq_19_1 x k, ← lemma_eq_19_1 x n]
    simp
  -- exact hx.sub_const (x k)
  sorry

lemma lemma_le_21 (x : ℕ → (Fin n) → α) (x_star : (Fin n) → α) (hx : Tendsto x atTop (𝓝 x_star)) (k : ℕ) :
    ∃ y, Tendsto (fun (n : ℕ) ↦ ∑ i ∈ range n \ range k, ‖x i - x (i + 1)‖ᵥ₁) atTop (𝓝 y) := by
  sorry

lemma lemma_le_22 (x : ℕ → (Fin n) → α) (x_star : (Fin n) → α) (hx : Tendsto x atTop (𝓝 x_star)) (k : ℕ) {y : ℝ} (hy : Tendsto (fun (n : ℕ) ↦ ∑ i ∈ range n \ range k, ‖x i - x (i + 1)‖ᵥ₁) atTop (𝓝 y)):
    ‖x k - x_star‖ᵥ₁ ≤ y := by
  sorry

lemma lemma_le_23 (gs := GaussSeidel A hA b x0) (ja := Jacobi A hA b x0) (hja : ‖ja.M‖₁ < 1) (k : ℕ) (i : (Fin n)) :
    ‖(gs.x (k + 1)) - (gs.x k)‖ᵥ₁ ≤ (1 / (1 - (sr ja))) * ((mur ja) ^ k) * ‖gs.x 1 - gs.x 0‖ᵥ₁ := by
  have le_1 := lemma_le_18 A b x0 hA gs ja hja k i
  have le_2 : (1 - (sr ja)) > 0 := by
    have : (sr ja) < 1 := by
      have := lemma_le_10_3 ja.M
      linarith
    linarith
  sorry

lemma lemma_le_24 (mu : ℝ) (k : ℕ):
    Tendsto (fun n ↦ ∑ i ∈ (range n \ range k), mu ^ i) atTop (𝓝 (mu ^ k / (1 - mu))) := by
  sorry

lemma lemma_le_25 (gs := GaussSeidel A hA b x0) (ja := Jacobi A hA b x0) (hja : ‖ja.M‖₁ < 1) (k : ℕ) (i : (Fin n)) (x_star : (Fin n) → α) (hx := Tendsto gs.x atTop (𝓝 x_star)) :
    ‖(gs.x k) - x_star‖ᵥ₁ ≤ (((mur ja) ^ k) / ((1 - mur ja)) * (1 - (sr ja))) * ‖gs.x 1 - gs.x 0‖ᵥ₁ := by
  sorry
