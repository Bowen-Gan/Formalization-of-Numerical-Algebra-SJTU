/-
Copyright (c) 2023 Boang Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boang Chen
-/
import Na.Defs
import Na.SOR.SOR
open Matrix Filter Topology spectrum
open BigOperators

-- variable {α : Type*} {n : ℕ} [Field α] [SeminormedAddCommGroup α] [SemilatticeSup α] [Lattice α] [OrderBot α] {x0 : (Fin n) → α} (A : Matrix (Fin n) (Fin n) α) (hA : ∀ i, A i i ≠ 0) {b : (Fin n) → α} {x0 : (Fin n) → α}
variable {n : ℕ} {x0 : (Fin n) → ℝ} (A : Matrix (Fin n) (Fin n) ℝ) (hAdiag : ∀ i, A i i ≠ 0) {b : (Fin n) → ℝ} {x0 : (Fin n) → ℝ}

lemma GaussSeidel_is_SOR {gs} (hgs : gs = GaussSeidel A hAdiag b x0) : gs = SOR A b x0 1 hAdiag := by
  rw [hgs]
  unfold GaussSeidel
  unfold SOR
  simp

/--
**Theorem 4.2.7**: Convergence of Gauss-Seidel Method for Symmetric Positive Definite Matrices.

For any symmetric positive definite matrix `A`, the Gauss-Seidel iteration converges to a unique solution `x_star` for any initial guess `x0`.
-/
theorem theorem_4_2_7 {gs} (hgs : gs = GaussSeidel A hAdiag b x0) (hApos : Matrix.PosDef A) (hAt : A = Aᵀ) :
    (∀ (_ : Fin n → ℝ), ∃ x_star, Tendsto gs.x atTop (𝓝 x_star)) := by
  have ins := GaussSeidel_is_SOR A hAdiag hgs
  have : (0 : ℝ) < 1 ∧ (1 : ℝ) < 2 := by
    constructor
    · linarith
    · linarith
  have the := theorem_4_4_4_real A hApos hAt b x0 1 hAdiag this
  rw [← ins] at the
  exact the
