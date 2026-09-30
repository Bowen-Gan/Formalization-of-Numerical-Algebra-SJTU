/-
Copyright (c) 2025 Yiming Fu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenjie Huang, Yiming Fu
-/
import Na.Defs
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Unbundled.AlgebraNorm

/-!
# Convergence Theory for Iterative Methods

This file develops the convergence theory for iterative methods, particularly focusing on
stationary iterative methods and their relationship to spectral properties of matrices.

## Main declarations

For stationary iterative methods on complex matrices:
* `Stationary_iter_converge_iff_spectralRadius_lt_one`: Convergence criterion based on spectral
  radius (Theorem 4.2.1, incomplete)

For stationary iterative methods in general:
* `stationary_iter_apriori_error_estimate`: A-priori error bounds for contracting iterations
  (Theorem 4.2.2)
* `stationary_iter_apriori_error_estimate'`: Alternative error estimate formulation (Theorem 4.2.3)

## Implementation notes

Several key theorems are marked as incomplete due to technical difficulties with compatibility
between different topological and norm structures in Mathlib. Specifically:
- The equivalence between norm-induced and standard topologies
- Proper handling of the stationary iterative method definition

## References
* Numerical Linear Algebra textbook

## TODO
Complete the proofs of the incomplete theorems once the necessary dependencies are resolved.

-/

namespace spectrum

lemma spectralRadius_pow_le {𝕜 : Type u} {A : Type v}
    [NormedField 𝕜] [Ring A] [Algebra 𝕜 A] [Nontrivial A]
    (a : A) (n : ℕ) :
    (spectralRadius 𝕜 a) ^ n ≤ spectralRadius 𝕜 (a ^ n) := by
  unfold spectralRadius
  obtain h | h := isEmpty_or_nonempty <| Subtype <| Membership.mem (spectrum 𝕜 a)
  · rw [Set.isEmpty_coe_sort] at h
    match n with
    | 0 => simp [spectrum.one_eq]
    | n + 1 => simp [h]
  · rw [iSup_subtype', ENNReal.iSup_pow, iSup_le_iff, Subtype.forall]
    intro k hk
    exact le_iSup₂_of_le (k ^ n) (pow_image_subset a n ⟨k, ⟨hk, rfl⟩⟩) (by simp)

lemma spectralRadius_pow_le' {𝕜 : Type u} {A : Type v}
    [NormedField 𝕜] [Ring A] [Algebra 𝕜 A]
    (a : A) {n : ℕ} (hn : n ≠ 0) :
    (spectralRadius 𝕜 a) ^ n ≤ spectralRadius 𝕜 (a ^ n) := by
  obtain h | h := em' <| Subsingleton A
  · rw [not_subsingleton_iff_nontrivial] at h
    exact spectralRadius_pow_le a n
  · simpa [spectralRadius] using hn

end spectrum

namespace SeminormedRing

open Filter Topology

theorem tendsto_norm_pow_zero_of_tendsto_rpow_norm_lt_one
    {A : Type*} [SeminormedRing A] (a : A) (r : ENNReal) (hr : r < 1) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (‖a ^ n‖ ^ (1 / n : ℝ))) atTop (𝓝 r) →
    Tendsto (fun n : ℕ => ‖a ^ n‖) atTop (𝓝 0) := by
  intro h
  obtain ⟨s, hrs, hs1⟩ : ∃ s : ℝ, r.toReal < s ∧ s < 1 := by
    use (r.toReal + 1) / 2
    have : r.toReal < 1 := by
      apply ENNReal.toReal_lt_of_lt_ofReal
      simpa using hr
    constructor
    · rw [lt_div_iff₀ (by simp)]
      rwa [mul_two, Real.add_lt_add_iff_left]
    · rw [div_lt_iff₀ (by simp), one_mul, ← lt_sub_iff_add_lt]
      norm_num ; exact this
  have spos : 0 < s := by
    have := @ENNReal.toReal_nonneg r
    exact lt_of_le_of_lt this hrs
  have h_eventually : ∀ᶠ n : ℕ in atTop, ‖a ^ n‖ ^ (1 / n : ℝ) < s := by
    rw [tendsto_order] at h
    rcases h with ⟨_, h⟩
    have hs'r : r < ENNReal.ofReal s := by
      rwa [ENNReal.lt_ofReal_iff_toReal_lt <| LT.lt.ne_top hr]
    have := h (ENNReal.ofReal s) hs'r
    convert this using 2
    exact (ENNReal.ofReal_lt_ofReal_iff spos).symm
  have h_bound : ∀ᶠ n in atTop, ‖a ^ n‖ ≤ s ^ n := by
    simp only [eventually_atTop] at ⊢ h_eventually
    obtain ⟨t, hlt⟩ := h_eventually
    refine ⟨max 1 t, fun n hnt ↦ ?_⟩
    have hn : 1 ≤ n := le_of_max_le_left hnt
    have ht : t ≤ n := le_of_max_le_right hnt
    have n_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_le_rpow_iff (by simp) (Real.rpow_natCast s n ▸ (pow_nonneg spos.le n))
    (show 0 < 1 / (n : ℝ) by simpa using hn)]
    have eq: (s ^ (n : ℝ)) ^ (1 / (n : ℝ)) = s := by
      rw [← Real.rpow_mul spos.le]
      rw [mul_one_div_cancel (ne_of_lt n_pos).symm]
      exact Real.rpow_one s
    rw [eq]
    exact le_of_lt (hlt n ht)
  have h_sn_zero : Tendsto (fun n : ℕ => s ^ n) atTop (𝓝 0) := by
    apply tendsto_pow_atTop_nhds_zero_of_abs_lt_one
    rw [abs_lt]
    exact ⟨neg_one_lt_zero.trans spos, hs1⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_sn_zero (by simp)
  exact h_bound

end SeminormedRing

section StationaryIterativeDiff

open Matrix

/-- The error sequence for a stationary iterative method.-/
def stationary_iter_diff  {F : Type*} [Field F] {n : ℕ}
    {x₀ : Fin n → F} (x_star : Fin n → F) (iter : Stationary_iterative x₀) :=
    fun k => iter.x k - x_star

/- Lemma: `y (k + 1) = iter.M *ᵥ y k` -/
lemma stationary_iter_diff_succ {F : Type*} [Field F] {n : ℕ}
    {x₀ : Fin n → F} (x_star : Fin n → F) (iter : Stationary_iterative x₀)
    (k : ℕ) (h_fixed_point : x_star = iter.M *ᵥ x_star + iter.g) :
    (stationary_iter_diff x_star iter (k + 1)) = iter.M *ᵥ (stationary_iter_diff x_star iter k) := by
  simp only [stationary_iter_diff]
  nth_rw 1 [Stationary_iterative.x_succ _ k, h_fixed_point]
  rw [Matrix.mulVec_sub]
  ring

/- Lemma: `y k = (iter.M) ^ k *ᵥ y 0` -/
lemma stationary_iter_diff_eq {F : Type*} [Field F]
    {x₀ : Fin n → F} (x_star : Fin n → F) (iter : Stationary_iterative x₀)
    (k : ℕ) (h_fixed_point : x_star = iter.M *ᵥ x_star + iter.g) :
    (stationary_iter_diff x_star iter k) = (iter.M) ^ k *ᵥ (stationary_iter_diff x_star iter 0) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [stationary_iter_diff_succ _ _ _ h_fixed_point, ih, Matrix.mulVec_mulVec]
    rw [pow_succ _ n, pow_mul_comm' iter.M n]


end StationaryIterativeDiff

section ComplexMatrix

open Matrix Filter Topology

/-- **Theorem 2.1.6 (1)** in textbook. -/
theorem Matrix.spectralRadius_le_nnnorm' {n : ℕ}
    (A : (Matrix (Fin n) (Fin n) ℂ))
    (p : AlgebraNorm ℂ (Matrix (Fin n) (Fin n) ℂ)) :
    (spectralRadius ℂ A) ≤ ENNReal.ofReal (p A) := by
  match n with
  | 0 => simp [spectralRadius]
  | n + 1 =>
    let _ : NormedRing ((Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) := p.toNormedRing
    let _ : NormedAlgebra ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := {
      norm_smul_le := by
        intro r A
        show p (r • A) ≤ ‖r‖ * p A
        rw [map_smul_eq_mul]}
    have : @CompleteSpace (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) PseudoMetricSpace.toUniformSpace := by
      apply @FiniteDimensional.complete ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) _ _ _
        PseudoMetricSpace.toUniformSpace
    obtain ⟨z, hz, hnorm⟩ := spectrum.exists_nnnorm_eq_spectralRadius A
    rw [spectrum.mem_iff] at hz
    rw [Algebra.algebraMap_eq_smul_one] at hz
    rw [isUnit_iff_isUnit_det] at hz
    simp only [isUnit_iff_ne_zero, ne_eq, Decidable.not_not] at hz
    rw [← exists_mulVec_eq_zero_iff] at hz
    obtain ⟨v, hne, hv⟩ := hz
    rw [sub_mulVec, sub_eq_zero] at hv
    simp only [smul_mulVec_assoc, one_mulVec] at hv
    let e1 : Fin (n + 1) → ℂ := Pi.single ⟨0, Nat.zero_lt_succ n⟩  1
    have : ‖z‖ * p (vecMulVec v e1) ≤ (p A) * p (vecMulVec v e1)  := by
      calc
        _ = p (z • vecMulVec v e1) := by rw [map_smul_eq_mul]
        _ = p (vecMulVec (z • v) e1) := by
          congr ; ext
          simp only [smul_apply, vecMulVec_apply, smul_eq_mul, Pi.smul_apply]
          rw [mul_assoc]
        _ = _ := by rw [hv]
        _ = p (A * (vecMulVec v e1)) := by
          congr ; ext
          simp only [vecMulVec_apply, mulVec, dotProduct, mul_apply, Finset.sum_mul, mul_assoc]
        _ ≤ _ := map_mul_le_mul p A _
    have pos : 0 < p (vecMulVec v e1)  := by
      show 0 < ‖(vecMulVec v e1)‖
      rw [norm_pos_iff]
      intro h
      have : v = 0 := by
        ext i
        have := congr_fun (congr_fun h i) ⟨0, Nat.zero_lt_succ n⟩
        simpa [vecMulVec_apply, Pi.single_eq_same, mul_one, zero_apply, e1] using this
      exact absurd this hne
    suffices ‖z‖ ≤ p A by
      rw [← hnorm]
      simpa only [ENNReal.ofReal, Real.toNNReal, apply_nonneg, sup_of_le_left, ENNReal.coe_le_coe] using this
    rw [← mul_le_mul_right pos]
    exact this

/-- **Theorem 2.1.7** in textbook. -/
theorem matrix_powers_tendsto_zero_iff_spectral_radius_lt_one
    {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) (p : AlgebraNorm ℂ (Matrix (Fin n) (Fin n) ℂ)):
    letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := p.toNormedRing
    letI T : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) :=
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace
    Tendsto (fun k : ℕ => A ^ k) atTop (@nhds _ T 0) ↔ (spectralRadius ℂ A) < 1 := by
  let : NormedRing (Matrix (Fin n) (Fin n) ℂ) := p.toNormedRing
  let : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := {
    norm_smul_le := by
      intro r A
      show p (r • A) ≤ ‖r‖ * p A
      rw [map_smul_eq_mul]}
  let T : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  have : @CompleteSpace (Matrix (Fin n) (Fin n) ℂ) PseudoMetricSpace.toUniformSpace := by
    apply @FiniteDimensional.complete ℂ (Matrix (Fin n) (Fin n) ℂ) _ _ _
      PseudoMetricSpace.toUniformSpace
  constructor
  · intro h
    rw [← ENNReal.tendsto_pow_atTop_nhds_zero_iff]
    suffices Tendsto (fun n : ℕ ↦ (spectralRadius ℂ (A ^ n))) atTop (𝓝 0) by
      have hle : ∀ᶠ n in atTop, (spectralRadius ℂ A) ^ n ≤ spectralRadius ℂ (A ^ n) := by
        simp only [eventually_atTop]
        exact ⟨1, fun n hn ↦ spectrum.spectralRadius_pow_le' A (Nat.ne_zero_of_lt hn)⟩
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds this (by simp) hle
    suffices Tendsto (fun k : ℕ => ‖A ^ k‖) atTop (𝓝 0) by
      have hle : ∀ᶠ n in atTop, (spectralRadius ℂ (A ^ n)) ≤ ENNReal.ofReal ‖A ^ n‖ := by
        apply Eventually.of_forall
        intro x
        exact Matrix.spectralRadius_le_nnnorm' _ p
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_ (by simp) hle
      simp_rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal this
    rwa [← tendsto_zero_iff_norm_tendsto_zero]
  · intro h
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply SeminormedRing.tendsto_norm_pow_zero_of_tendsto_rpow_norm_lt_one A _ h
    exact spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius A

/-- **Lemma 4.2.1**: This theorem is incomplete due to dependencies on
the stationary iterative method definition and
compatibility between norm-induced and standard topologies. -/
theorem stationary_iter_converge_iff_M_pow_tendsto_zero
    {n : ℕ} (p : AlgebraNorm ℂ (Matrix (Fin n) (Fin n) ℂ))
    (vp : AlgebraNorm ℂ (Fin n → ℂ))
    (compat : ∀ (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ), vp (A *ᵥ v) ≤ p A * vp v)
    {x₀ : (Fin n → ℂ)}
    (iter : Stationary_iterative x₀) {x' : Fin n → ℂ}
    (h_fixed_point : x' = iter.M *ᵥ x' + iter.g) :
    letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := p.toNormedRing
    letI T : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := PseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI : NormedRing (Fin n → ℂ) := vp.toNormedRing
    letI vT : TopologicalSpace (Fin n → ℂ) := PseudoMetricSpace.toUniformSpace.toTopologicalSpace
    Tendsto iter.x atTop (@nhds _ vT x') ↔
    (Tendsto (fun k : ℕ => (iter.M) ^ k) atTop (@nhds _ T 0) ∨ x₀ = x'):= by
  constructor
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := p.toNormedRing
  letI T : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : NormedRing (Fin n → ℂ) := vp.toNormedRing
  letI vT : TopologicalSpace (Fin n → ℂ) := PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  · rw [Classical.or_iff_not_imp_right]
    intro h hne
    let y : ℕ → Fin n → ℂ := stationary_iter_diff x' iter
    replace h : Tendsto (fun k : ℕ => iter.M ^ k *ᵥ y 0) atTop (@nhds _ vT 0) := by
      unfold y
      have : Tendsto (stationary_iter_diff x' iter) atTop (@nhds _ vT 0) := by
        unfold stationary_iter_diff
        rwa [tendsto_sub_nhds_zero_iff]
      convert this using 2
      exact (stationary_iter_diff_eq x' iter _ h_fixed_point).symm
    rw [NormedAddCommGroup.tendsto_nhds_zero] at ⊢ h
    sorry
  · intro h
    sorry


/-- **Lemma 4.2.1**: This theorem is incomplete due to dependencies on
the stationary iterative method definition and
compatibility between norm-induced and standard topologies. -/
theorem stationary_iter_converge_iff_M_pow_tendsto_zero'
    {n : ℕ} (p : AlgebraNorm ℂ (Matrix (Fin n) (Fin n) ℂ))
    (vp : AlgebraNorm ℂ (Fin n → ℂ))
    (compat : ∀ (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ), vp (A *ᵥ v) ≤ p A * vp v)
    {x₀ : (Fin n → ℂ)}
    (iter : Stationary_iterative x₀) {x' : Fin n → ℂ}
    (h_fixed_point : x' = iter.M *ᵥ x' + iter.g) :
    -- A 的幂序列收敛到 0 矩阵
    letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := p.toNormedRing
    letI T : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := PseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI : NormedRing (Fin n → ℂ) := vp.toNormedRing
    letI vT : TopologicalSpace (Fin n → ℂ) := PseudoMetricSpace.toUniformSpace.toTopologicalSpace
    Tendsto iter.x atTop (@nhds _ vT x') ↔
    (Tendsto (fun k : ℕ => (iter.M) ^ k) atTop (@nhds _ T 0) ∨ x₀ = x'):= by
  constructor
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := p.toNormedRing
  letI T : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : NormedRing (Fin n → ℂ) := vp.toNormedRing
  letI vT : TopologicalSpace (Fin n → ℂ) := PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  · rw [Classical.or_iff_not_imp_right]
    intro h hne
    let y : ℕ → Fin n → ℂ := stationary_iter_diff x' iter
    replace h : Tendsto (fun k : ℕ => iter.M ^ k *ᵥ y 0) atTop (@nhds _ vT 0) := by
      unfold y
      have : Tendsto (stationary_iter_diff x' iter) atTop (@nhds _ vT 0) := by
        unfold stationary_iter_diff
        rwa [tendsto_sub_nhds_zero_iff]
      convert this using 2
      exact (stationary_iter_diff_eq x' iter _ h_fixed_point).symm
    rw [NormedAddCommGroup.tendsto_nhds_zero] at ⊢ h
    sorry
  · intro h
    sorry

/-- **Theorem 4.2.1**: This theorem is incomplete due to dependencies on
the stationary iterative method definition and
compatibility between norm-induced and standard topologies. -/
theorem stationary_iter_converge_iff_spectralRadius_lt_one
    {n : ℕ} (p : AlgebraNorm ℂ (Matrix (Fin n) (Fin n) ℂ))
    (vp : AlgebraNorm ℂ (Fin n → ℂ)) {x₀ : (Fin n → ℂ)}
    (compat : ∀ (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ), vp (A *ᵥ v) ≤ p A * vp v)
    (iter : Stationary_iterative x₀) {x' : Fin n → ℂ}
    (h_fixed_point : x' = iter.M *ᵥ x' + iter.g)
    (hne : x₀ ≠ x') :
    letI : NormedRing (Fin n → ℂ) := vp.toNormedRing
    letI vT : TopologicalSpace (Fin n → ℂ) := PseudoMetricSpace.toUniformSpace.toTopologicalSpace
    Tendsto iter.x atTop (@nhds _ vT x') ↔ spectralRadius ℂ iter.M < 1 := by
  sorry
  -- rw [Stationary_iter_converge_iff_M_pow_tendsto_zero p vp compat iter h_fixed_point]
  -- rw [matrix_powers_tendsto_zero_iff_spectral_radius_lt_one iter.M p]
  -- refine ⟨fun h ↦ h.elim (fun h ↦ h) (fun h ↦ absurd h hne), fun h ↦ Or.inl h⟩

section ErrorEstimate

variable {F : Type*} [NormedField F] {n : ℕ}
variable (p : AlgebraNorm F (Matrix (Fin n) (Fin n) F))
variable (vp : AlgebraNorm F (Fin n → F))

/-- **Theorem 4.2.2**: A-priori error estimate for a contracting stationary iteration.
For an iteration matrix `M` with `‖M‖ < 1`, the error at step k
is bounded by `‖M‖ ^ k / (1 - ‖M‖)` times the initial step size. -/
theorem stationary_iter_apriori_error_estimate
    (h_compat : ∀ (A : Matrix (Fin n) (Fin n) F) (v : Fin n → F), vp (A *ᵥ v) ≤ p A * vp v)
    {x₀ : Fin n → F} (iter : Stationary_iterative x₀)
    (x_star : Fin n → F)
    (h_fixed_point : x_star = iter.M *ᵥ x_star + iter.g)
    (hq_lt_1 : p iter.M < 1) :
    ∀ k : ℕ, vp (iter.x k - x_star) ≤
    (p iter.M) ^ k / (1 - p iter.M) * vp (iter.x 0 - iter.x 1) := by
  intro k
  let y := stationary_iter_diff x_star iter
  -- Step 1: Take the norm of yₖ and estimate it to get the inequality vp(yₖ) ≤ qᵏ vp(y₀).
  have h_yk_le_q_pow_k_y0 : vp (y k) ≤ p iter.M ^ k * vp (y 0) := by
    match k with
    | 0 => simp
    | k + 1 =>
        simp only [y]
        rw [stationary_iter_diff_eq x_star iter (k + 1) h_fixed_point]
        show vp (iter.M ^ (k + 1) *ᵥ y 0) ≤ (p iter.M) ^ (k + 1) * vp (y 0)
        calc
          vp (iter.M ^ (k + 1) *ᵥ y 0) ≤ p (iter.M ^ (k + 1)) * vp (y 0) := by apply h_compat
          _ ≤ (p iter.M) ^ (k + 1) * vp (y 0) := by
            refine mul_le_mul_of_nonneg_right ?_ (apply_nonneg vp (y 0))
            let _ : NormedRing (Matrix (Fin n) (Fin n) F) := p.toNormedRing
            apply norm_pow_le' iter.M (by simp)
  -- Step 2: Estimate vp(y₀) and prove that vp(y₀) ≤ (1/(1-q)) * vp(x₁ - x₀).
  have h_y0_le_1 : vp (y 0) ≤ vp (iter.x 0 - iter.x 1) + (p iter.M) * vp (y 0) := by
    calc
      vp (y 0) = vp (iter.x 0 - x_star) := by simp [y, stationary_iter_diff]
      _ = vp ((iter.x 0 - iter.x 1) + (iter.x 1 - x_star)) := by ring_nf
      _ ≤ vp (iter.x 0 - iter.x 1) + vp (iter.x 1 - x_star) := by
        apply map_add_le_add
      _ = vp (iter.x 0 - iter.x 1) + vp (iter.M *ᵥ y 0) := by
        simp only [stationary_iter_diff, add_right_inj, y]
        nth_rw 1 [Stationary_iterative.x_succ, h_fixed_point]
        rw [Matrix.mulVec_sub]
        ring_nf
      _ ≤ vp (iter.x 0 - iter.x 1) + p iter.M * vp (y 0) := by
        refine add_le_add_left ?_ (vp (iter.x 0 - iter.x 1))
        apply h_compat
  have h_y0_le_2 : vp (y 0) ≤ 1 / (1 - (p iter.M)) * vp (iter.x 0 - iter.x 1) := by
    rw [div_mul_eq_mul_div]
    rw [le_div_iff₀ (sub_pos.mpr hq_lt_1)]
    rw [mul_one_sub, sub_le_iff_le_add, one_mul, mul_comm]
    exact h_y0_le_1
  calc
    _ = vp (y k) := by simp [y, stationary_iter_diff]
    _ ≤ (p iter.M) ^ k * vp (y 0) := h_yk_le_q_pow_k_y0
    _ ≤ (p iter.M) ^ k * (1 / (1 - (p iter.M)) * vp (iter.x 0 - iter.x 1)) :=
      mul_le_mul_of_nonneg_left h_y0_le_2 (pow_nonneg (apply_nonneg p iter.M) k)
    _ = (p iter.M) ^ k / (1 - (p iter.M)) * vp (iter.x 0 - iter.x 1) := by ring

/-- **Theorem 4.2.3**: A-priori error estimate for a contracting stationary iteration.
For an iteration matrix `M` with `‖M‖ < 1`, the error at step k
is bounded by `‖M‖ / (1 - ‖M‖)` times the difference between consecutive iterates. -/
theorem stationary_iter_apriori_error_estimate'
    (h_compat : ∀ (A : Matrix (Fin n) (Fin n) F) (v : Fin n → F), vp (A *ᵥ v) ≤ p A * vp v)
    {x₀ : Fin n → F} (iter : Stationary_iterative x₀)
    (x_star : Fin n → F) (h_fixed_point : x_star = iter.M *ᵥ x_star + iter.g)
    (hq_lt_1 : (p iter.M) < 1) :
    ∀ k : ℕ, vp (iter.x (k + 1) - x_star) ≤
    (p iter.M) / (1 - (p iter.M)) * vp (iter.x k - iter.x (k + 1)) := by
  intro k
  have h_main : vp (iter.x (k + 1) - x_star) ≤
    (p iter.M) * vp (iter.x k - iter.x (k + 1)) + (p iter.M) * vp (iter.x (k + 1) - x_star) := by
    calc
      vp (iter.x (k + 1) - x_star) = vp (iter.M *ᵥ (iter.x k - x_star)) := by
        rw [Stationary_iterative.x_succ iter k]
        nth_rw 1 [h_fixed_point]
        rw [Matrix.mulVec_sub]
        ring_nf
      _ ≤ p iter.M * vp (iter.x k - x_star) := by apply h_compat
      _ = (p iter.M) * vp ((iter.x k - iter.x (k + 1)) + (iter.x (k + 1) - x_star)) := by ring_nf
      _ ≤ (p iter.M) * (vp (iter.x k - iter.x (k + 1)) + vp (iter.x (k + 1) - x_star)) := by
        refine mul_le_mul_of_nonneg_left ?_ (apply_nonneg p iter.M)
        apply map_add_le_add
      _ = _ := by rw [mul_add]
  rw [div_mul_eq_mul_div, le_div_iff₀ (sub_pos.mpr hq_lt_1)]
  simp only [mul_sub, mul_one, tsub_le_iff_right]
  nth_rw 2 [mul_comm]
  exact h_main

end ErrorEstimate
