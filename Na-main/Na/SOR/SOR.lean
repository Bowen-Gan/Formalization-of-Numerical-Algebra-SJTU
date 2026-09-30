import Na.Defs
import Na.SOR.fuscon
import Mathlib.Analysis.Normed.Algebra.Spectrum
open Matrix Filter Topology spectrum

lemma isLowerTriangular_of_diagPart_sub_smul_lowerPart {α : Type*} {n : ℕ} [Field α]
    (A : Matrix (Fin n) (Fin n) α) (ω : α) :
    (A.diagPart - ω • (-A.lowerPart)).BlockTriangular OrderDual.toDual := by
  apply Matrix.BlockTriangular.sub
  · unfold Matrix.BlockTriangular
    simp [OrderDual.toDual_lt_toDual,Matrix.diagPart]
    intro i j h_ij_lt
    have h_ij_ne : i ≠ j := fun h_eq => (lt_self_iff_false j).mp (h_eq ▸ h_ij_lt)
    exact diagonal_apply_ne' (fun i ↦ A i i) (id (Ne.symm h_ij_ne))
  · unfold Matrix.BlockTriangular
    simp_rw [OrderDual.toDual_lt_toDual]
    simp [Matrix.lowerPart]
    intro i j h_ij_lt h_ji_lt
    exact absurd h_ij_lt (not_lt.mpr (le_of_lt h_ji_lt))

theorem D_minus_omega_L_isUnit_of_diag_nonzero {α : Type*} {n : ℕ} [Field α]
    (A : Matrix (Fin n) (Fin n) α)
    (hA_diag_nonzero : ∀ i, A i i ≠ 0)
    (ω : α) :
    IsUnit (A.diagPart - ω • (-A.lowerPart)) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  let M := A.diagPart - ω • (-A.lowerPart)
  have h_M_lower_tri := isLowerTriangular_of_diagPart_sub_smul_lowerPart A ω
  rw [Matrix.det_of_lowerTriangular]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  simp [sub_apply, smul_apply, neg_apply]
  rw [Matrix.lowerPart]
  simp only [↓reduceIte, ge_iff_le, le_refl, mul_zero, add_zero]
  exact hA_diag_nonzero i
  exact h_M_lower_tri

noncomputable def SOR {α : Type*} {n : ℕ} [Field α]
    (A : Matrix (Fin n) (Fin n) α)
    (b : (Fin n) → α)
    (x0 : (Fin n) → α)
    (ω : α)
    (h_diag_nonzero : ∀ i, (A i i) ≠ 0)
    : Stationary_iterative x0 :=
  let D := A.diagPart
  let L := -A.lowerPart
  let U := -A.upperPart
  let M_inv := ↑(D_minus_omega_L_isUnit_of_diag_nonzero A h_diag_nonzero ω).unit.inv
  {
    M := M_inv * ((1 - ω) • D + ω • U),
    g := ω • (M_inv *ᵥ b)
  }

noncomputable section
lemma my_tendsto_sub_nhds_zero_iff {α β : Type*} [TopologicalSpace α] [AddCommGroup α] [ContinuousAdd α]
    (f : β → α) (l : α) (F : Filter β) :
    Tendsto f F (𝓝 l) ↔ Tendsto (fun x => f x - l) F (𝓝 0) := by
  sorry
lemma tendsto_matrix_mulVec_zero {n : ℕ} [TopologicalSpace (Matrix (Fin n) (Fin n) ℂ)]
    (M_seq : ℕ → Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    Tendsto M_seq atTop (𝓝 0) → Tendsto (fun k => M_seq k *ᵥ v) atTop (𝓝 0) := by
  sorry
theorem theorem_4_4_1 {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (b : (Fin n) → ℂ)
    (ω : ℂ)
    (h_diag_nonzero : ∀ i, A i i ≠ 0) :
    -- 对任意初始值，SOR 都收敛
    (∀ (x₀ : Fin n → ℂ), ∃ x_star,
      let sor_instance := SOR A b x₀ ω h_diag_nonzero
      Tendsto sor_instance.x atTop (𝓝 x_star))
    ↔
    -- 当且仅当谱半径 < 1（使用任意初始值构造的实例来获取迭代矩阵）
    (let dummy_sor := SOR A b (fun _ => 0) ω h_diag_nonzero
     spectralRadius ℂ dummy_sor.M < 1) := by

  let dummy_sor := SOR A b (fun _ => 0) ω h_diag_nonzero
  have p : AlgebraNorm ℂ (Matrix (Fin n) (Fin n) ℂ) := sorry
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := p.toNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := {
    norm_smul_le := by
      intro r M
      show p (r • M) ≤ ‖r‖ * p M
      rw [map_smul_eq_mul]
  }
  letI T : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  have : @CompleteSpace (Matrix (Fin n) (Fin n) ℂ) PseudoMetricSpace.toUniformSpace := by
    apply @FiniteDimensional.complete ℂ (Matrix (Fin n) (Fin n) ℂ) _ _ _ PseudoMetricSpace.toUniformSpace

  constructor
  · -- 充分性：如果对所有初始值都收敛，则谱半径 < 1
    intro h_convergence
    rw [← ENNReal.tendsto_pow_atTop_nhds_zero_iff]
    suffices Tendsto (fun n : ℕ ↦ (spectralRadius ℂ (dummy_sor.M ^ n))) atTop (𝓝 0) by
      have hle : ∀ᶠ n in atTop, (spectralRadius ℂ dummy_sor.M) ^ n ≤ spectralRadius ℂ (dummy_sor.M ^ n) := by
        simp only [eventually_atTop]
        refine ⟨1, fun n hn ↦ ?_⟩
        have hnz : 0<n := by linarith
        exact SpectralRadius.pow_le dummy_sor.M hnz
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds this (by simp) hle
    suffices Tendsto (fun k : ℕ => ‖dummy_sor.M ^ k‖) atTop (𝓝 0) by
      have hle : ∀ᶠ n in atTop, (spectralRadius ℂ (dummy_sor.M ^ n)) ≤ ENNReal.ofReal ‖dummy_sor.M ^ n‖ := by
        apply Eventually.of_forall
        intro x
        exact Matrix.spectralRadius_le_norm _ p
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_ (by simp) hle
      simp_rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal this
    rw [← tendsto_zero_iff_norm_tendsto_zero]
    -- 从收敛假设推导出矩阵幂趋于零
    sorry -- 需要从 h_convergence 推导出这个结论

  · -- 必要性：如果谱半径 < 1，则对所有初始值都收敛
    intro h_spectral
    intro x₀
    let sor_instance := SOR A b x₀ ω h_diag_nonzero

    -- 关键观察：SOR 的迭代矩阵 M 不依赖于初始值
    have h_M_eq : sor_instance.M = dummy_sor.M := by sorry

    have h_g_eq : sor_instance.g = dummy_sor.g := by sorry

    -- 证明存在固定点
    have h_is_unit : IsUnit (1 - sor_instance.M) := by
      rw [h_M_eq]
      -- 当谱半径 < 1 时，(1 - M) 可逆
      sorry

    let x_star := (1 - sor_instance.M)⁻¹ *ᵥ sor_instance.g
    use x_star

    -- 证明 x_star 是固定点
    have h_fixed_point : x_star = sor_instance.M *ᵥ x_star + sor_instance.g := by
      sorry

    -- 从谱半径条件推导出矩阵幂趋于零
    have h_M_pow_zero : Tendsto (fun k : ℕ => sor_instance.M ^ k) atTop (𝓝 0) := by
      rw [h_M_eq]
      -- 使用 lemma_3 (fuscon.lean 中的引理)
      sorry

    -- 使用误差公式
    rw [my_tendsto_sub_nhds_zero_iff]
    have h_error_eq : ∀ k, sor_instance.x k - x_star = sor_instance.M ^ k *ᵥ (x₀ - x_star) := by
      intro k
      exact Stationary_iterative_diff_eq x_star sor_instance k h_fixed_point
    rw [show (SOR A b x₀ ω h_diag_nonzero) = sor_instance from rfl]
    simp_rw [h_error_eq]

    exact tendsto_matrix_mulVec_zero (fun k => sor_instance.M ^ k) (x₀ - x_star) h_M_pow_zero

--定理4.4.1 SOR迭代法收敛的充分必要条件是ρ(Lw) < 1.
theorem theorem_4_4_1_real {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (b : (Fin n) → ℝ)
    (x0 : (Fin n) → ℝ)
    (ω : ℝ)
    (h_diag_nonzero : ∀ i, A i i ≠ 0) :
    let sor_instance := SOR A b x0 ω h_diag_nonzero
    (∀ (x₀ : Fin n → ℝ), ∃ x_star, Tendsto sor_instance.x atTop (𝓝 x_star))
    ↔
    spectralRadius ℝ sor_instance.M < 1 := by sorry

--定理4.4.2 SOR迭代法收敛的必要条件是0 < w < 2.
theorem theorem_4_4_2_real {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (b : (Fin n) → ℝ)
    (x0 : (Fin n) → ℝ)
    (ω : ℝ)
    (h_diag_nonzero : ∀ i, A i i ≠ 0) :
    let sor_instance := SOR A b x0 ω h_diag_nonzero
    (∀ (x₀ : Fin n → ℝ), ∃ x_star, Tendsto sor_instance.x atTop (𝓝 x_star))
    → (0 < ω ∧  ω < 2)  := by sorry

--定理4.4.4 若系数矩阵A是实对称的正定矩阵，则当0 < ω < 2时 SOR迭代法收敛.
theorem theorem_4_4_4_real {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Matrix.PosDef A)
    (ha : A = Aᵀ)
    (b : (Fin n) → ℝ)
    (x0 : (Fin n) → ℝ)
    (ω : ℝ)
    (h_diag_nonzero : ∀ i, A i i ≠ 0) :
    let sor_instance := SOR A b x0 ω h_diag_nonzero
    (0 < ω ∧ ω < 2) →
    (∀ (x₀ : Fin n → ℝ), ∃ x_star, Tendsto sor_instance.x atTop (𝓝 x_star)) := by sorry
