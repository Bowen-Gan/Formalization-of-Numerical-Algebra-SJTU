import Na.Defs
import Mathlib

open Matrix Filter Topology

theorem Matrix.spectralRadius_le_norm {n : ℕ}
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
      apply @FiniteDimensional.complete ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) _ _ _ PseudoMetricSpace.toUniformSpace
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
          congr
          ext i j
          simp only [smul_apply, vecMulVec_apply, smul_eq_mul, Pi.smul_apply]
          rw [mul_assoc]
        _ = _ := by rw [hv]
        _ = p (A * (vecMulVec v e1)) := by
          congr
          ext i j
          simp only [vecMulVec_apply, mulVec, dotProduct, mul_apply]
          simp only [Finset.sum_mul, mul_assoc]
        _ ≤ _ := map_mul_le_mul p A _
    have pos : 0 < p (vecMulVec v e1)  := by
      show 0 < ‖ (vecMulVec v e1)‖
      rw [norm_pos_iff]
      intro h
      have : v = 0 := by
        ext i
        have := congr_fun (congr_fun h i) ⟨0, Nat.zero_lt_succ n⟩
        simpa [vecMulVec_apply, Pi.single_eq_same, mul_one, zero_apply, e1] using this
      exact absurd this hne
    suffices ‖z‖ ≤ p A by
      rw [← hnorm]
      simpa [ENNReal.ofReal, Real.toNNReal, apply_nonneg, sup_of_le_left, ENNReal.coe_le_coe]
    rw [← mul_le_mul_right pos]
    exact this

namespace SpectralRadius

lemma pow_le {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (a : A) {n : ℕ} (hn : 0 < n) :
    (spectralRadius ℂ a) ^ n ≤ spectralRadius ℂ (a ^ n) := by
  obtain h | h := em' (Subsingleton A)
  · have : Nontrivial A := not_subsingleton_iff_nontrivial.mp h
    obtain ⟨eig, heig, eig_eq_radius⟩ := spectrum.exists_nnnorm_eq_spectralRadius a
    rw [← eig_eq_radius]
    rw [← ENNReal.coe_pow]
    rw [← nnnorm_pow]
    have eig_pow_eq_pow_spec: spectrum ℂ (a ^ n) = (fun x => x ^ n) '' spectrum ℂ a := by
      apply spectrum.map_pow_of_pos a hn
    have eig_pow_in_spec_in: eig ^ n ∈ (fun x => x ^ n) '' spectrum ℂ a := by
      exact Set.mem_image_of_mem (fun x ↦ x ^ n) heig
    have eig_pow_in_pow_spec: eig ^ n ∈ spectrum ℂ (a ^ n) := by
      rw [eig_pow_eq_pow_spec]
      exact eig_pow_in_spec_in
    apply le_biSup (fun x ↦ (‖x‖₊ : ENNReal)) eig_pow_in_pow_spec
  · simp only [spectrum.SpectralRadius.of_subsingleton, nonpos_iff_eq_zero, pow_eq_zero_iff',
    ne_eq, true_and]
    exact Nat.ne_zero_of_lt hn

end SpectralRadius

namespace NormedRing
theorem tendsto_norm_pow_zero_of_tendsto_rpow_norm_lt_one
    {A : Type*} [NormedRing A]
    (a : A) (r : ENNReal) (hr : r < 1) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (‖a ^ n‖ ^ (1 / n : ℝ))) atTop
    (𝓝 r) → Tendsto (fun n : ℕ => ‖a ^ n‖) atTop (𝓝 0) := by
  intro h
  obtain ⟨s, hrs, hs1⟩ : ∃ s : ℝ, r.toReal < s ∧ s < 1 := by
    use (r.toReal + 1) / 2
    have : r.toReal < 1 := by
      apply ENNReal.toReal_lt_of_lt_ofReal
      simpa
    constructor
    · rw [lt_div_iff₀ (by simp)]
      linarith only [@ENNReal.toReal_nonneg r, this]
    · rw [div_lt_iff₀ (by simp)]
      simp
      linarith only [this]
  have spos : 0 < s := by
    have := @ENNReal.toReal_nonneg r
    exact lt_of_le_of_lt this hrs
  -- 从收敛性得到：对于足够大的 n，‖a^n‖^(1/n) < s
  have h_eventually : ∀ᶠ n : ℕ in atTop, ‖a ^ n‖ ^ (1 / n : ℝ) < s := by
    rw [tendsto_order] at h
    rcases h with ⟨_, h⟩
    have hs'r : r < ENNReal.ofReal s := by
      rwa [ENNReal.lt_ofReal_iff_toReal_lt <| LT.lt.ne_top hr]
    have := h (ENNReal.ofReal s) hs'r
    convert this using 2
    exact (ENNReal.ofReal_lt_ofReal_iff spos).symm
  -- 这意味着对于足够大的 n，‖a^n‖ ≤ s^n
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
  -- 由于 s < 1，s^n → 0
  have h_sn_zero : Tendsto (fun n : ℕ => s ^ n) atTop (𝓝 0) := by
    apply tendsto_pow_atTop_nhds_zero_of_abs_lt_one
    rw [abs_lt]
    exact ⟨neg_one_lt_zero.trans spos, hs1⟩
  -- 使用夹逼定理
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_sn_zero (by simp)
  exact h_bound

end NormedRing

-- lemma_3 : ∀ A ∈ Cⁿˣⁿ, Aᵏ → 0 当 k → ∞ ↔ ρ(A) < 1
theorem lemma_3
    {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) (p : AlgebraNorm ℂ (Matrix (Fin n) (Fin n) ℂ)):
    letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := p.toNormedRing
    letI T : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := PseudoMetricSpace.toUniformSpace.toTopologicalSpace
    Tendsto (fun k : ℕ => A ^ k) atTop (@nhds _ T 0) ↔ (spectralRadius ℂ A) < 1 := by
  let : NormedRing (Matrix (Fin n) (Fin n) ℂ) := p.toNormedRing
  let : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := {
    norm_smul_le := by
      intro r A
      show p (r • A) ≤ ‖r‖ * p A
      rw [map_smul_eq_mul]}
  let T : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  have : @CompleteSpace (Matrix (Fin n) (Fin n) ℂ) PseudoMetricSpace.toUniformSpace := by
    apply @FiniteDimensional.complete ℂ (Matrix (Fin n) (Fin n) ℂ) _ _ _ PseudoMetricSpace.toUniformSpace
  constructor
  · intro h
    rw [← ENNReal.tendsto_pow_atTop_nhds_zero_iff]
    suffices Tendsto (fun n : ℕ ↦ (spectralRadius ℂ (A ^ n))) atTop (𝓝 0) by
      have hle : ∀ᶠ n in atTop, (spectralRadius ℂ A) ^ n ≤ spectralRadius ℂ (A ^ n) := by
        simp only [eventually_atTop]
        refine ⟨1, fun n hn ↦ ?_⟩
        exact SpectralRadius.pow_le A hn
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds this (by simp) hle
    suffices Tendsto (fun k : ℕ => ‖A ^ k‖) atTop (𝓝 0) by
      have hle : ∀ᶠ n in atTop, (spectralRadius ℂ (A ^ n)) ≤ ENNReal.ofReal ‖A ^ n‖ := by
        apply Eventually.of_forall
        intro x
        exact Matrix.spectralRadius_le_norm _ p
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_ (by simp) hle
      simp_rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal this
    rwa [← tendsto_zero_iff_norm_tendsto_zero]
  · intro h
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply NormedRing.tendsto_norm_pow_zero_of_tendsto_rpow_norm_lt_one A (spectralRadius ℂ A) h
    exact spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius A

-- useful lemma
noncomputable def Stationary_iterative_diff {F : Type*} [Field F] {n : ℕ}
    {x₀ : Fin n → F} (x_star : Fin n → F) (iter : Stationary_iterative x₀) :=
    fun k => iter.x k - x_star

-- lemma: y (k+1) = iter.M *ᵥ y k
lemma Stationary_iterative_diff_succ {F : Type*} [Field F] {n : ℕ}
    {x₀ : Fin n → F} (x_star : Fin n → F) (iter : Stationary_iterative x₀)
    (k : ℕ) (h_fixed_point : x_star = iter.M *ᵥ x_star + iter.g) :
    (Stationary_iterative_diff x_star iter (k + 1)) = iter.M *ᵥ (Stationary_iterative_diff x_star iter k) := by
  simp only [Stationary_iterative_diff]
  nth_rw 1 [Stationary_iterative.x_succ _ k, h_fixed_point]
  rw [Matrix.mulVec_sub]
  ring

-- lemma : y k = (iter.M) ^ k *ᵥ y 0
lemma Stationary_iterative_diff_eq {F : Type*} [Field F]
    {x₀ : Fin n → F} (x_star : Fin n → F) (iter : Stationary_iterative x₀)
    (k : ℕ) (h_fixed_point : x_star = iter.M *ᵥ x_star + iter.g) :
    (Stationary_iterative_diff x_star iter k) = (iter.M) ^ k *ᵥ (Stationary_iterative_diff x_star iter 0) := by
  induction k with
  | zero =>
    simp
  | succ n ih =>
    rw [Stationary_iterative_diff_succ, ih, Matrix.mulVec_mulVec]
    rw [pow_succ _ n]
    rw [pow_mul_comm' iter.M n]
    exact h_fixed_point

local notation "‖" x "‖ᵥ₁" => @Norm.norm _ (PiLp.instNorm 1 fun _ ↦ ℂ) x

theorem Stationary_iter_converge_iff_M_pow_tendsto_zero
    {n : ℕ}  {x₀ : (Fin n → ℂ)}
    (h_compat : ∀ (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ), ‖A *ᵥ v‖ᵥ₁ ≤ ‖A‖₁ * ‖v‖ᵥ₁)
    (iter : Stationary_iterative x₀) {x' : Fin n → ℂ}
    (h_fixed_point : x' = iter.M *ᵥ x' + iter.g) :
    Tendsto (fun k : ℕ => (iter.M) ^ k) atTop (nhds 0) → Tendsto iter.x atTop (nhds x') := by
  sorry

theorem Stationary_iter_converge_iff_M_pow_tendsto_zero'
    {n : ℕ} (p : AlgebraNorm ℂ (Matrix (Fin n) (Fin n) ℂ))
    (vp : AlgebraNorm ℂ (Fin n → ℂ)) {x₀ : (Fin n → ℂ)}
    (h_compat : ∀ (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ), vp (A *ᵥ v) ≤ p A * vp v)
    (iter : Stationary_iterative x₀) {x' : Fin n → ℂ}
    (h_fixed_point : x' = iter.M *ᵥ x' + iter.g) :
    letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := p.toNormedRing
    letI T : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := PseudoMetricSpace.toUniformSpace.toTopologicalSpace

    letI : NormedRing (Fin n → ℂ) := vp.toNormedRing
    letI vT : TopologicalSpace (Fin n → ℂ) := vp.toNormedRing.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    Tendsto (fun k : ℕ => (iter.M) ^ k) atTop (@nhds _ T 0)
    → Tendsto iter.x atTop (@nhds _ vT x') := by
  -- letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := p.toNormedRing
  -- letI T : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := PseudoMetricSpace.toUniformSpace.toTopologicalSpace

  -- letI : NormedRing (Fin n → ℂ) := vp.toNormedRing
  -- letI vT : TopologicalSpace (Fin n → ℂ) := vp.toNormedRing.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  sorry
  -- -- let : NormedRing (Matrix (Fin n) (Fin n) ℂ) := p.toNormedRing
  -- -- let T : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  -- -- letI : NormedRing (Fin n → ℂ) := vp.toNormedRing

  -- -- intro h
  -- let y : ℕ → Fin n → ℂ := Stationary_iterative_diff x' iter
  -- suffices Tendsto (fun k : ℕ => iter.M ^ k *ᵥ y 0) atTop (@nhds _ vT 0) by
  --   unfold y at this
  --   rw [← @tendsto_sub_nhds_zero_iff _ _ vT]
  --   convert this using 2
  --   exact Stationary_iterative_diff_eq x' iter _ h_fixed_point
  -- obtain hy | hy := ne_or_eq (y 0) 0
  -- -- ·
  -- --   rw [@NormedAddCommGroup.tendsto_nhds_zero _ _ vp.toSeminormedAddGroup _ _]
  -- --   intro ε hεpos
  -- --   replace hy : 0 < vp (y 0) := by
  -- --     show 0 < ‖(y 0)‖
  -- --     rw [@norm_pos_iff _ vp.toNormedAddGroup _]
  -- --     exact hy

  --   sorry
  --   -- specialize h (ε / vp (y 0)) (div_pos hεpos hy)

  --   -- simp only [eventually_atTop, ge_iff_le] at h ⊢
  --   -- obtain ⟨N, hN⟩ := h
  --   -- use N
  --   -- intro b hn
  --   -- calc
  --   --   _ ≤ ‖iter.M ^ b‖ * ‖y 0‖ := by

  --   --   _ < (ε / vp (y 0)) * ‖y 0‖  := by
  --   --     gcongr
  --   --     apply hN b hn

  -- · sorry
  --   -- · rw [NormedAddCommGroup.tendsto_nhds_zero]
  -- --   rw [hy]
  -- --   intro ε hεpos
  -- --   apply Eventually.of_forall
  -- --   simpa using hεpos

-- theorem_4_2_1: Convergence condition for stationary iterative methods.
theorem Stationary_iter_converge_iff_spectralRadius_lt_one'
    {n : ℕ} (p : AlgebraNorm ℂ (Matrix (Fin n) (Fin n) ℂ))
    (vp : AlgebraNorm ℂ (Fin n → ℂ)) {x₀ : (Fin n → ℂ)}
    (compat : ∀ (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ), vp (A *ᵥ v) ≤ p A * vp v)
    (iter : Stationary_iterative x₀) {x' : Fin n → ℂ}
    (h_fixed_point : x' = iter.M *ᵥ x' + iter.g) :
    letI : NormedRing (Fin n → ℂ) := vp.toNormedRing
    letI vT : TopologicalSpace (Fin n → ℂ) := vp.toNormedRing.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    spectralRadius ℂ iter.M < 1 → Tendsto iter.x atTop (@nhds _ vT x') := by
  sorry

section PrioriErrorEstimate

variable {n : ℕ}
variable (p : AlgebraNorm ℝ (Matrix (Fin n) (Fin n) ℝ))
variable (vp : AlgebraNorm ℝ (Fin n → ℝ))

-- theorem_4_2_2: A-priori error estimate for a contracting stationary iteration.
theorem theorem_4_2_2
    (h_compat : ∀ (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ), vp (A *ᵥ v) ≤ p A * vp v)
    {x₀ : Fin n → ℝ} (iter : Stationary_iterative x₀)
    (x_star : Fin n → ℝ) (q : ℝ)
    (h_fixed_point : x_star = iter.M *ᵥ x_star + iter.g)
    (hM_norm : p iter.M = q)
    (hq_lt_1 : q < 1)
    (hq_pos : 0 < q) :
    (∀ k : ℕ, vp (iter.x k - x_star) ≤ q ^ k / (1 - q) * vp (iter.x 0 - iter.x 1)) := by
  intro k
  let y := Stationary_iterative_diff x_star iter
  -- Step 1: Take the norm of yₖ and estimate it to get the inequality vp(yₖ) ≤ qᵏ vp(y₀).
  have h_yk_le_q_pow_k_y0 : vp (y k) ≤ q ^ k * vp (y 0) := by
    match k with
    | 0 => simp
    | k + 1 =>
        simp [y]
        rw [Stationary_iterative_diff_eq x_star iter (k + 1)]
        show vp (iter.M ^ (k + 1) *ᵥ y 0) ≤ q ^ (k + 1) * vp (y 0)
        calc
          vp (iter.M ^ (k + 1) *ᵥ y 0) ≤ p (iter.M ^ (k + 1)) * vp (y 0) := by apply h_compat
          _ ≤ (p iter.M) ^ (k + 1) * vp (y 0) := by
            gcongr
            let _ : NormedRing (Matrix (Fin n) (Fin n) ℝ) := p.toNormedRing
            apply norm_pow_le' iter.M (by simp)
          _ = q ^ (k + 1) * vp (y 0) := by rw [hM_norm]
        exact h_fixed_point
  -- Step 2: Estimate vp(y₀) and prove that vp(y₀) ≤ (1/(1-q)) * vp(x₁ - x₀).
  have h_y0_le_1 : vp (y 0) ≤ vp (iter.x 0 - iter.x 1) + q * vp (y 0) := by
    calc
      vp (y 0) = vp (iter.x 0 - x_star) := by simp [y, Stationary_iterative_diff]
      _ = vp ((iter.x 0 - iter.x 1) + (iter.x 1 - x_star)) := by ring_nf
      _ ≤ vp (iter.x 0 - iter.x 1) + vp (iter.x 1 - x_star) := by
        apply map_add_le_add
      _ = vp (iter.x 0 - iter.x 1) + vp (iter.M *ᵥ y 0) := by
        simp [y, Stationary_iterative_diff]
        nth_rw 1 [Stationary_iterative.x_succ, h_fixed_point]
        rw [Matrix.mulVec_sub]
        ring_nf
      _ ≤ vp (iter.x 0 - iter.x 1) + p iter.M * vp (y 0) := by
        gcongr
        apply h_compat
      _ = vp (iter.x 0 - iter.x 1) + q * vp (y 0) := by rw [hM_norm]
  have h_y0_le_2 : vp (y 0) ≤ 1 / (1 - q) * vp (iter.x 0 - iter.x 1) := by
    field_simp
    rw [le_div_iff₀ (by linarith)]
    linarith only [h_y0_le_1]
  calc
    vp (iter.x k - x_star) = vp (y k) := by simp [y, Stationary_iterative_diff]
    _ ≤ q ^ k * vp (y 0) := h_yk_le_q_pow_k_y0
    _ ≤ q ^ k * (1 / (1 - q) * vp (iter.x 0 - iter.x 1)) := by gcongr
    _ = q ^ k / (1 - q) * vp (iter.x 0 - iter.x 1) := by ring

-- theorem_4_2_3: A-posteriori error estimate for a contracting stationary iteration.
theorem theorem_4_2_3
    (h_compat : ∀ (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ), vp (A *ᵥ v) ≤ p A * vp v)
    {x₀ : Fin n → ℝ} (iter : Stationary_iterative x₀)
    (x_star : Fin n → ℝ) (q : ℝ)
    (h_fixed_point : x_star = iter.M *ᵥ x_star + iter.g)
    (hM_norm : p iter.M = q)
    (hq_lt_1 : q < 1)
    (hq_nonneg : 0 ≤ q) :
    (∀ k : ℕ, vp (iter.x (k + 1) - x_star) ≤ q / (1 - q) * vp (iter.x k - iter.x (k + 1))) := by
  intro k
  have h_main : vp (iter.x (k + 1) - x_star) ≤ q * vp (iter.x k - iter.x (k + 1)) + q * vp (iter.x (k + 1) - x_star) := by
    calc
      vp (iter.x (k + 1) - x_star) = vp (iter.M *ᵥ (iter.x k - x_star)) := by
        rw [Stationary_iterative.x_succ iter k]
        nth_rw 1 [h_fixed_point]
        rw [Matrix.mulVec_sub]
        ring_nf
      _ ≤ p iter.M * vp (iter.x k - x_star) := by apply h_compat
      _ = q * vp (iter.x k - x_star) := by rw [hM_norm]
      _ = q * vp ((iter.x k - iter.x (k + 1)) + (iter.x (k + 1) - x_star)) := by ring_nf
      _ ≤ q * (vp (iter.x k - iter.x (k + 1)) + vp (iter.x (k + 1) - x_star)) := by
        gcongr
        apply map_add_le_add
      _ = q * vp (iter.x k - iter.x (k + 1)) + q * vp (iter.x (k + 1) - x_star) := by rw [mul_add]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  simp only [mul_sub, mul_one, tsub_le_iff_right]
  linarith only [h_main]

end PrioriErrorEstimate
