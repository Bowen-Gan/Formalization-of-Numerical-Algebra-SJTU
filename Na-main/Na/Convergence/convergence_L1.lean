/-
Copyright (c) 2025 Yiming Fu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yiming Fu
-/
import Na.Convergence.convergence

/-!
# L¹-version of Convergence Theorems for Stationary Iterative Methods

This file provides L¹ (infinity norm) versions of the convergence theorems for stationary
iterative methods, complementing the general norm-based results in `Na.convergence`.

## Main declarations

* `matrix_powers_L1_tendsto_zero_iff_spectral_radius_lt_one`: Matrix powers converge to zero
  in L¹ norm if and only if the spectral radius is less than 1
* `stationary_iter_L1_converges_of_matrix_powers_tend_to_zero`: A stationary iterative method
  converges in L¹ norm if the iteration matrix powers tend to zero
* `stationary_iter_L1_converges_of_spectral_radius_lt_one`: A stationary iterative method
  converges in L¹ norm if the spectral radius of the iteration matrix is less than 1

## Implementation notes

This file provides concrete L¹ norm versions of the convergence theorems as a temporary
measure, since the general norm-based results in `Na.convergence` are incomplete due to
technical difficulties with topological compatibility between different norm structures in
Mathlib.

## References

* Numerical Linear Algebra textbook

-/

section L1

open Filter Matrix

attribute [instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
theorem matrix_powers_L1_tendsto_zero_iff_spectral_radius_lt_one
    {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) :
    Tendsto (fun k : ℕ => A ^ k) atTop (nhds 0) ↔ (spectralRadius ℂ A) < 1 := by
  constructor
  · intro h
    rw [← ENNReal.tendsto_pow_atTop_nhds_zero_iff]
    suffices Tendsto (fun n : ℕ ↦ (spectralRadius ℂ (A ^ n))) atTop (nhds 0) by
      have hle : ∀ᶠ n in atTop, (spectralRadius ℂ A) ^ n ≤ spectralRadius ℂ (A ^ n) := by
        simp only [eventually_atTop]
        exact ⟨1, fun n hn ↦ spectrum.spectralRadius_pow_le' A (Nat.ne_zero_of_lt hn)⟩
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds this (by simp) hle
    suffices Tendsto (fun k : ℕ => ‖A ^ k‖) atTop (nhds 0) by
      have hle : ∀ᶠ n in atTop, (spectralRadius ℂ (A ^ n)) ≤ ENNReal.ofReal (‖A ^ n‖) := by
        apply Eventually.of_forall
        intro x
        let p : AlgebraNorm ℂ (Matrix (Fin n) (Fin n) ℂ) := {
          toFun := norm
          map_zero' := norm_zero
          add_le' := norm_add_le
          neg' := norm_neg
          mul_le' := linfty_opNorm_mul
          eq_zero_of_map_eq_zero' x := norm_eq_zero.mp
          smul' := norm_smul
          }
        show spectralRadius ℂ (A ^ x) ≤ ENNReal.ofReal (p (A ^ x))
        apply Matrix.spectralRadius_le_nnnorm'
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_ (by simp) hle
      simp_rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal this
    rw [← tendsto_zero_iff_norm_tendsto_zero]
    exact h
  · intro h
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply SeminormedRing.tendsto_norm_pow_zero_of_tendsto_rpow_norm_lt_one A (spectralRadius ℂ A) h
    exact spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius A

/-- A stationary iterative method converges up the unique fixed point in `L¹` norm if
  the spectral radius of the iteration matrix k-th power `Mᵏ` tends to zero. -/
theorem stationary_iter_L1_converges_of_matrix_powers_tend_to_zero
    {n : ℕ}  {x₀ : Fin n → ℂ}
    (iter : Stationary_iterative x₀) {x' : Fin n → ℂ}
    (h_fixed_point : x' = iter.M *ᵥ x' + iter.g) :
    Tendsto (fun k : ℕ => (iter.M) ^ k) atTop (nhds 0) → Tendsto iter.x atTop (nhds x') := by
  intro h
  let y : ℕ → Fin n → ℂ := stationary_iter_diff x' iter
  suffices Tendsto (fun k : ℕ => iter.M ^ k *ᵥ y 0) atTop (nhds 0) by
    unfold y at this
    rw [← tendsto_sub_nhds_zero_iff]
    convert this using 2
    exact stationary_iter_diff_eq x' iter _ h_fixed_point
  obtain hy | hy := ne_or_eq (y 0) 0
  · rw [NormedAddCommGroup.tendsto_nhds_zero] at h ⊢
    intro ε hεpos
    replace hy : 0 < ‖(y 0)‖ := by
      rw [norm_pos_iff]
      exact hy
    specialize h (ε / ‖(y 0)‖) (div_pos hεpos hy)
    simp only [eventually_atTop, ge_iff_le] at h ⊢
    obtain ⟨N, hN⟩ := h
    use N
    intro b hn
    calc
      _ ≤ ‖iter.M ^ b‖ * ‖y 0‖ := linfty_opNorm_mulVec (iter.M ^ b) (y 0)
      _ < (ε / ‖(y 0)‖) * ‖y 0‖  := by
        refine mul_lt_mul_of_pos_right ?_ hy
        apply hN b hn
      _ = ε := div_mul_cancel₀ ε hy.ne.symm
  · simp_rw [hy]
    simp only [mulVec_zero, tendsto_const_nhds_iff]

/-- A stationary iterative method converges to the unique fixed point in `L¹` norm
if the spectral radius of the iteration matrix is less than one. -/
theorem stationary_iter_L1_converges_of_spectral_radius_lt_one
    {n : ℕ} {x₀ : Fin n → ℂ}
    (iter : Stationary_iterative x₀) {x' : Fin n → ℂ}
    (h_fixed_point : x' = iter.M *ᵥ x' + iter.g) :
  spectralRadius ℂ iter.M < 1 → Tendsto iter.x atTop (nhds x') := by
  intro h
  apply stationary_iter_L1_converges_of_matrix_powers_tend_to_zero iter h_fixed_point
  exact (matrix_powers_L1_tendsto_zero_iff_spectral_radius_lt_one iter.M).mpr h

section L1
