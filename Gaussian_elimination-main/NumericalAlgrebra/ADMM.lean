import Mathlib

open Real InnerProductSpace Filter Function Set
local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

variable {α : Type*} {n : ℕ} [NormedField α]

lemma aux1 {k} (i : Fin k) (f : Fin (k + 1) → α):
    ∑ j : Ici i.castSucc, f j = ∑ j ∈ Ici i, f j.castSucc := by
  -- @Ici (Fin (k + 1)) Fin.instPartialOrder.toPreorder (Fin.instLocallyFiniteOrderTop (k + 1)) i.castSucc : Finset (Fin (k + 1))

  sorry
#check Finset.sum_Ico_Ico_comm
lemma Finset.sum_sum_exchange (M : Matrix (Fin n) (Fin n) α) :
    ∑ j, (∑ i ∈ Ici j, M i j) = ∑ i, (∑ j ∈ Iic i, M i j) := by
  let a := 0
  let b := n
  have hui {u} (hu : u ∈ Finset.Ico a b) : u < b := by
    exact (LocallyFiniteOrderBot.finset_mem_Iio b u).mp hu
  let f : ℕ → ℕ → α := fun i j =>
    if hij : (i ∈ Finset.Ico a b) ∧ (j ∈ Finset.Ico a b) then
      M ⟨i, hui hij.1⟩ ⟨j ,hui hij.2⟩
    else 0
  have :=  Finset.sum_Ico_Ico_comm a b f
  calc _
    _ = ∑ i ∈ Ico a b, ∑ j ∈ Ico i b, f i j := by
      sorry

    _ = _ := sorry

  /--/
  induction' n with k kh
  · simp
--   rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
--   have hk : k ≤ k + 1 := sorry
  let finaux : Fin k → Fin (k + 1) := Fin.castSucc
  let M1 : Matrix (Fin k) (Fin k)  α := M.submatrix finaux finaux

-- #check Fin.sum_univ_castSucc
  obtain kh1 := kh M1
  simp [M1] at kh1
--   simp [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  calc _
    _ = (∑ j : Fin k, ∑ i ∈ Ici j, M (finaux i) (finaux j))
        + ∑ i ∈ Ici (Fin.last k), M i (Fin.last k) := by
        rw [Fin.sum_univ_castSucc]
        congr
        funext i
        simp [finaux]


        -- have (hj : j ∈ Ici i.castSucc) : j =
        -- ∑ j ∈ Ici i.castSucc, f j = ∑ j ∈ Ici i, f j.castSucc

        sorry
        -- congr

    _ = ∑ j : Fin k, ∑ i ∈ Iic j, M (finaux j) (finaux i)
        + ∑ i ∈ Ici (Fin.last k), M (Fin.last k) i  := by
        rw [kh1]
        sorry


    _ = _ :=by
        -- rw [Fin.sum_univ_
        sorry
-- namespace ADMM

-- section Basic

-- variable (E₁ E₂ F : Type*)
-- [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
-- [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]
-- [NormedAddCommGroup F ] [InnerProductSpace ℝ F ] [CompleteSpace F ]

-- /-- ADMM 问题定义 -/
-- structure Problem where
--   f₁ : E₁ → ℝ
--   f₂ : E₂ → ℝ
--   A₁ : E₁ →L[ℝ] F
--   A₂ : E₂ →L[ℝ] F
--   b  : F

-- structure Params where
--   ρ  : ℝ      -- 罚参数 (ρ > 0)
--   τ  : ℝ

-- end Basic

-- variable {E₁ E₂ F : Type*}
-- [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
-- [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]
-- [NormedAddCommGroup F ] [InnerProductSpace ℝ F ] [CompleteSpace F ]

-- noncomputable def augLag  (P : Problem E₁ E₂ F) (ρ : ℝ) (x₁ : E₁) (x₂ : E₂) (y : F) : ℝ :=
--   P.f₁ x₁ + P.f₂ x₂ + ⟪y, P.A₁ x₁ + P.A₂ x₂ - P.b⟫ + (ρ / 2) * ‖P.A₁ x₁ + P.A₂ x₂ - P.b‖ ^ 2

-- def HasUniqueMin {V α: Type*} [LE α] (φ : V → α) : Prop :=
--   ∃! x : V, ∀ y : V, φ x ≤ φ y

-- def UniqSubX (P : Problem E₁ E₂ F) (ρ : ℝ) (x₂ : E₂) (y : F) : Prop :=
--   HasUniqueMin (fun u : E₁ => augLag P ρ u x₂ y)

-- def UniqSubY (P : Problem E₁ E₂ F) (ρ : ℝ) (x₁ : E₁) (y : F) : Prop :=
--   HasUniqueMin (fun u : E₂ => augLag P ρ x₁ u y)

-- /-- 一次 ADMM 迭代 -/
-- noncomputable def admmStep {P : Problem E₁ E₂ F} {θ : Params}
--   (hX : ∀ x₂ y, UniqSubX P θ.ρ x₂ y)
--   (hY : ∀ x₁ y, UniqSubY P θ.ρ x₁ y) :
--     (E₁ × E₂ × F) → (E₁ × E₂ × F)
-- | (_, x₂, y) =>
--   -- ① x 更新：最小化 Aug‑Lag w.r.t x
--   let x₁'   := (hX x₂  y).exists.choose
--   -- ② z 更新：最小化 Aug‑Lag w.r.t z
--   let x₂'   := (hY x₁' y).exists.choose
--   -- ③ 对偶更新
--   -- 原始残差
--   let r'    := P.A₁ x₁' + P.A₂ x₂' - P.b
--   -- scaled dual ascent
--   let y'    := y + θ.τ • θ.ρ • r'
--   (x₁', x₂', y')

-- noncomputable def admmIter {P : Problem E₁ E₂ F} {θ : Params}
--   (hX : ∀ x₂ y, UniqSubX P θ.ρ x₂ y) (hY : ∀ x₁ y, UniqSubY P θ.ρ x₁ y) : Nat → (E₁ × E₂ × F) → (E₁ × E₂ × F)
--   | 0,   state => state
--   | n+1, state => admmIter hX hY n (admmStep hX hY state)

-- def HasOptimum (P : Problem E₁ E₂ F) : Prop :=
--   ∃ x z, P.A₁ x + P.A₂ z = P.b  ∧
--          ∀ x' z', P.A₁ x' + P.A₂ z' = P.b →
--                    P.f₁ x + P.f₂ z ≤ P.f₁ x' + P.f₂ z'

-- def Slater_condition {α V : Type* }[TopologicalSpace α]
--     [AddCommGroup V][Module ℝ V][AddTorsor V α]
--     (fr: Set α) : Prop := ∃ x , x ∈ intrinsicInterior ℝ fr

-- /-- Slater 条件：存在相对内点的可行向量 -/
-- def Slater (P : Problem E₁ E₂ F) : Prop := Slater_condition {(x₁, x₂) | P.A₁ x₁ + P.A₂ x₂ = P.b}

-- def HasSubgradientAt {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → ℝ) (g x : E) : Prop :=
--   ∀ y, f y ≥ f x + ⟪g, y - x⟫

-- /-- Subderiv of functions --/
-- def SubderivAt {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → ℝ) (x : E) : Set E :=
--   {g : E| HasSubgradientAt f g x}

-- class IsConvexKKT (P : Problem E₁ E₂ F) (x₁ : E₁) (x₂ : E₂)(y : F) : Prop where
--    subgrad₁ : -P.A₁.adjoint y ∈ SubderivAt P.f₁ x₁
--    subgrad₂ : -P.A₂.adjoint y ∈ SubderivAt P.f₂ x₂
--    eq       :  (P.A₁ x₁) + (P.A₂ x₂) = P.b

-- theorem admm_converges {P : Problem E₁ E₂ F} {θ : Params}
--     (hX : ∀ x₂ y, UniqSubX P θ.ρ x₂ y) (hY : ∀ x₁ y, UniqSubY P θ.ρ x₁ y)
--     (hρ : θ.ρ > 0)
--     (hτ : 0 < θ.τ ∧ θ.τ < ( 1 + √ 5 ) / 2)
--     (fullrank₁ : Injective P.A₁) (fullrank₂ : Injective P.A₂)
--     (lscf₁ : LowerSemicontinuous P.f₁) (lscf₂ : LowerSemicontinuous P.f₂)
--     (cf₁ : ConvexOn ℝ univ P.f₁) (cf₂ : ConvexOn ℝ univ P.f₂)
--     (hP : HasOptimum P) (hs : Slater P) (x₀ : E₁) (z₀ : E₂) (u₀ : F) :
--     ∃ (u : E₁) (v : E₂) (w : F),
--       IsConvexKKT P u v w ∧ Tendsto (fun n ↦ (admmIter hX hY n (x₀, z₀, u₀))) atTop (nhds (u, v, w)) := by
--   sorry

-- noncomputable section Lasso

-- open Set Real Matrix Finset

-- local notation "‖" x "‖₂" => @Norm.norm _ (PiLp.instNorm 2 fun _ ↦ ℝ) x
-- local notation "‖" x "‖₁" => @Norm.norm _ (PiLp.instNorm 1 fun _ ↦ ℝ) x

-- local notation "ℝ^"n => EuclideanSpace ℝ (Fin n)

-- variable {m n : ℕ} (μ : ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)

-- def Lasso.f₁  : (ℝ^n) → ℝ := fun x ↦ μ * ‖x‖₁

-- def Lasso.f₂  : (ℝ^n) → ℝ := fun x ↦ ((1 / 2) • ‖(A *ᵥx) - b‖₂^2)

-- instance Lasso : Problem (ℝ^n) (ℝ^n) (ℝ^n) where
--   f₁ := Lasso.f₁ μ
--   f₂ := Lasso.f₂ A b
--   A₁ := 1
--   A₂ := -1
--   b := 0

-- lemma inj_id  : Injective (1 : (ℝ^n) →L[ℝ] ℝ^n) := fun _ _ a ↦ a

-- lemma inj_neg : Injective (-1 : (ℝ^n) →L[ℝ] ℝ^n) := by
--   intro x y h; simpa using congrArg Neg.neg h

-- open Continuous
-- variable (n) in
-- lemma f₁_lsc : LowerSemicontinuous (Lasso.f₁ μ : (ℝ^n) → ℝ) :=
--   -- L¹范数连续 ⇒ l.s.c.
--   lowerSemicontinuous (mul continuous_const (norm continuous_id'))
-- #check DivisionRing
-- variable (n) in
-- lemma f₁_conv : ConvexOn ℝ univ (Lasso.f₁ μ : (ℝ^n) → ℝ) := by
--   sorry

-- variable (n) in
-- lemma f₂_lsc : LowerSemicontinuous (Lasso.f₂ A b : (ℝ^n) → ℝ) := by
--   unfold Lasso.f₂
--   apply lowerSemicontinuous
--   exact continuous_const--?????

-- variable (n) in
-- lemma f₂_conv  : ConvexOn ℝ univ (Lasso.f₂ A b : (ℝ^n) → ℝ) := by
--   -- 二次函数凸
--   -- admit

--   sorry

-- variable (θ : Params)
-- lemma uniq_subX (x₂ : ℝ^n) (y : ℝ^n) :
--     UniqSubX (Lasso μ A b) θ.ρ x₂ y := by
--   -- 目标 x ↦ μ‖x‖₁ + (ρ/2)‖x - (x₂ - y/ρ)‖²  强凸 ⇒ 唯一
--   -- 用 `quadratic_strong_convex` + Weierstrass；略
--   admit

-- lemma uniq_subY (x₁ : ℝ^n) (y : ℝ^n) :
--     UniqSubY (Lasso μ A b) θ.ρ x₁ y := by
--   sorry

-- lemma feasible : HasOptimum (Lasso μ A b) := by
--   simp [HasOptimum]
--   sorry

-- lemma slater : Slater (Lasso μ A b) := by
--   simp [Slater, Lasso]
--   simp only [Slater_condition]
--   use (0, 0)
--   sorry

-- theorem lasso_ADMM_converges (hρ : θ.ρ > 0) (hτ : 0 < θ.τ ∧ θ.τ < (1 + √5) / 2)
--     (x₀ z₀ y₀ : ℝ^n) : ∃ (x z y : ℝ^n), IsConvexKKT (Lasso μ A b) x z y
--     ∧ Tendsto (fun k ↦ admmIter (uniq_subX μ A b θ) (uniq_subY μ A b θ) k (x₀,z₀,y₀)) atTop (nhds (x, z, y)) :=
--   admm_converges (uniq_subX μ A b θ) (uniq_subY μ A b θ)
--   hρ hτ inj_id inj_neg (f₁_lsc n μ) (f₂_lsc n A b) (f₁_conv n μ) (f₂_conv n A b)
--   (feasible μ A b) (slater μ A b) x₀ z₀ y₀


-- end Lasso
