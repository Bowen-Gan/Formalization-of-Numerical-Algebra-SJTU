/-
Copyright (c) 2023 Boang Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boang Chen, Chenyi Li
-/
import Na.Defs
import Na.GaussSeidel.lemmas_4_2_5
import Mathlib.Data.Finset.Max
open Matrix Finset
open BigOperators

noncomputable section GS_4_2_5

variable {α : Type*} {n : ℕ} [NormedField α]
variable (A : Matrix (Fin n) (Fin n) α) (b : (Fin n) → α) (x0 : (Fin n) → α)
variable (hA : ∀ i, A i i ≠ 0)

#check (Jacobi A hA b x0).M
#check ‖(Jacobi A hA b x0).x 0‖
#check norm
#check Ioi
-- #check (Jacobi A hA_J b x0).M (0 : ℕ) 0

local notation "‖" x "‖ᵥ₁" => @Norm.norm _ (PiLp.instNorm 1 fun _ ↦ α) x
local notation "‖" x "‖ᵥ₂" => @Norm.norm _ (PiLp.instNorm 2 fun _ ↦ α) x
#check ‖b‖ᵥ₁
#check ‖b‖ᵥ₂

-- private def rig (ja := Jacobi A hA_J b x0) : Fin n → α :=
--   fun j ↦ ∑ i ∈ Ioi j, |ja.M i j|

-- local notation "s_func" alg => fun j ↦ (∑ i ∈ Ioi j, ‖Stationary_iterative.M alg i j‖)
-- local notation "mu_func" alg => fun j ↦ (∑ i ∈ Iio j, ‖Stationary_iterative.M alg i j‖) / (1 - (∑ i ∈ Ioi j, ‖Stationary_iterative.M alg i j‖))
-- local notation "sr" alg => ‖s_func alg‖
-- local notation "mur" alg => ‖mu_func alg‖

-- local notation "l_i" alg => fun i ↦ (∑ j ∈ Ioi i, ‖Stationary_iterative.M alg i j‖)
-- local notation "u_i" alg => fun i ↦ (∑ j ∈ Iio i, ‖Stationary_iterative.M alg i j‖)

-- local notation "D" => A.diagPart
-- local notation "L" => -A.lowerPart
-- local notation "U" => -A.upperPart

local notation "u_j" alg => fun j ↦ (∑ i ∈ Ioi j, ‖Stationary_iterative.M alg i j‖)
local notation "l_j" alg => fun j ↦ (∑ i ∈ Iio j, ‖Stationary_iterative.M alg i j‖)
local notation "sr" alg => ‖u_j alg‖
local notation "mur" alg => ‖fun j ↦ (((l_j alg) j) / (1 - ((u_j alg) j)))‖

-- variable {ja : Stationary_iterative x0}
-- #check s_func ja
-- #check mu_func ja

#synth Norm (Fin n → α)
#check Pi.normedAddCommGroup.toNorm

-- lemmas should be proven in file called lemmas_4_2_5.lean.

-- TODO : use lemmas to prove theorems

-- B = ja.M, L_1 = gs.M
theorem theorem_4_2_5_1 (ja := Jacobi A hA b x0) (gs := GaussSeidel A hA b x0) (hn : n > 0) :
    (mur ja) ≤ ‖ja.M‖₁ := by
  sorry

theorem theorem_4_2_5_2 (ja := Jacobi A hA b x0) (gs := GaussSeidel A hA b x0) (hja : ‖ja.M‖₁ < 1) (hn : n > 0) :
    (spectralRadius α gs.M).toNNReal < 1 := by
  sorry

/--
**Theorem 4.2.5.3**: Error Bound for Gauss-Seidel Method Compared to Jacobi Method.

Given a linear system `A x = b` with solution `x_star` (where the residual `A *ᵥ x_star - b = 0`),
this theorem establishes an error bound for the `k`-th Gauss-Seidel iterate `gs.x k` relative to the true solution,
in terms of the Jacobi iteration matrix `ja.M`.
-/
theorem theorem_4_2_5_3 (ja := Jacobi A hA b x0) (gs := GaussSeidel A hA b x0) (lr : {x // linearsystem.residual A b x = 0}) (hja : ‖ja.M‖₁ < 1) (k : ℕ) (hn : n > 0) :
    (‖gs.x k - lr.1‖ᵥ₁ ≤ ((mur ja) ^ k) / ((1 - (mur ja)) * (1 - (sr ja))) * ‖gs.x (1 : ℕ) - x0‖ᵥ₁) := by
  sorry
    -- we may change rig and mu_func like (fun j => ∑ i ∈ range j, |ja.M.upperPart i j|)

end GS_4_2_5

#check theorem_4_2_5_2
