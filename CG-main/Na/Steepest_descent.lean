import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Polynomial.Basic
import «Na».Defs


open Matrix Set


noncomputable section steepest_descent

variable {n : ℕ}

def steepest_descent.stepsize (A : Matrix (Fin n) (Fin n) ℝ) :
  ((Fin n) → ℝ) → ℝ :=
  fun r ↦ if r = 0 then 0 else (r ⬝ᵥ r) / (r ⬝ᵥ (A *ᵥ r))

def steepest_descent.info (A : Matrix (Fin n) (Fin n) ℝ) (x0 b : (Fin n) → ℝ)  :
    ℕ → (((Fin n) → ℝ) × ((Fin n) → ℝ) × ℝ)
  | 0 => (x0, b - A *ᵥ x0, steepest_descent.stepsize A (b - A *ᵥ x0))
  | p + 1 =>
    let (x, r, s) := steepest_descent.info A x0 b p
    (x + s • r, linearsystem.residual A b (x + s • r),
      steepest_descent.stepsize A (linearsystem.residual A b (x + s • r)))

def steepest_descent.x (A : Matrix (Fin n) (Fin n) ℝ) (x0 b : (Fin n) → ℝ)  :
    ℕ → ((Fin n) → ℝ) := fun k ↦ (steepest_descent.info A x0 b k).1

def steepest_descent.r (A : Matrix (Fin n) (Fin n) ℝ) (x0 b : (Fin n) → ℝ)  :
    ℕ → ((Fin n) → ℝ) := fun k ↦ (steepest_descent.info A x0 b k).2.1

def steepest_descent.α (A : Matrix (Fin n) (Fin n) ℝ) (x0 b : (Fin n) → ℝ)  :
    ℕ → ℝ := fun k ↦ (steepest_descent.info A x0 b k).2.2


variable (A : Matrix (Fin n) (Fin n) ℝ) (x0 b : (Fin n) → ℝ)
local notation "xk" => steepest_descent.x A x0 b
local notation "r" => steepest_descent.r A x0 b
local notation "α" => steepest_descent.α A x0 b
local notation "φ" => quad_func A b

lemma xk_eq_def : ∀ k,  xk (k+1) = xk k + (α k) • (r k) := fun _ => rfl
lemma rk_def : ∀ k,  r k = b - A *ᵥ xk k
  | 0 => rfl
  | _ + 1 => rfl
lemma αk_eq : ∀ k, α k = if r k = 0 then 0 else (r k) ⬝ᵥ (r k) / (r k) ⬝ᵥ (A *ᵥ (r k))
  | 0 => rfl
  | _ + 1 => rfl

lemma unfold_quad_x_plus_y (hA : A.IsSymm) (x y: (Fin n) → ℝ) :
  (x + y) ⬝ᵥ A *ᵥ (x + y) = x ⬝ᵥ A *ᵥ x + y ⬝ᵥ A *ᵥ x + x ⬝ᵥ A *ᵥ y + y ⬝ᵥ A *ᵥ y := by
    rw [← add_dotProduct x y (A *ᵥ x), add_assoc, ← add_dotProduct x y (A *ᵥ y)]
    rw [inner_x_Ay_eq_inner_y_Ax A hA (x + y) x, inner_x_Ay_eq_inner_y_Ax A hA (x + y) y, ← add_dotProduct]

-- 二次函数在对称轴处取最大值(a > 0)
theorem quadratic_min {a b c : ℝ} (ha : a > 0) :
    IsMinOn (fun x => a * x ^ 2 + b * x + c) univ (-b / (2 * a)) := by
  intro x hx; dsimp [IsMinOn]
  have h : a * x ^ 2 + b * x + c = a * (x + b / (2 * a)) ^ 2 + (4 * a * c - b ^ 2) / (4 * a) := by
    field_simp [(show a ≠ 0 from by linarith)]; ring
  have h0 : a * (-b / (2 * a)) ^ 2 + b * (-b / (2 * a)) + c = (4 * a * c - b ^ 2) / (4 * a) := by
    field_simp [(show a ≠ 0 from by linarith)]; ring
  rw [h, h0]
  have h1 : a * (x + b / (2 * a)) ^ 2 ≥ 0 :=
    mul_nonneg (le_of_lt ha) (sq_nonneg _)
  linarith

lemma inner_x_Ay_eq_inner_Ax_y (hA : A.IsSymm) (x y: Fin n → ℝ): x ⬝ᵥ A *ᵥ y = A *ᵥ x ⬝ᵥ y := by
  rw [inner_x_Ay_eq_inner_y_Ax]
  exact dotProduct_comm y (A *ᵥ x)
  exact hA

-- 140页最上面
theorem stepsize_min (k : ℕ) (hA : A.PosDef):
  ∀ a : ℝ, φ (xk k + (α k) • (r k)) ≤ φ (xk k + a • (r k)) := by
  by_cases hr : r k = 0
  · rw [hr]; simp
  have h3key1: ∀ a,  φ (xk k + a • (r k))= ((r k) ⬝ᵥ (A *ᵥ (r k))) * (a^2)
    + (- 2 * ((r k)⬝ᵥ(r k)) ) * a + φ  (xk k) := by
    intro a; unfold quad_func
    rw [unfold_quad_x_plus_y, inner_x_Ay_eq_inner_y_Ax A hA.1 (a • (r k)) (xk k), add_assoc (xk k ⬝ᵥ A *ᵥ xk k)]
    have : xk k ⬝ᵥ A *ᵥ a • r k + xk k ⬝ᵥ A *ᵥ a • r k = 2 *(xk k ⬝ᵥ A *ᵥ a • r k) := by
      rw [Eq.symm (two_nsmul (xk k ⬝ᵥ A *ᵥ a • r k))]
      exact Mathlib.Tactic.Ring.smul_eq_cast rfl rfl
    rw [this]; simp [mul_add]
    rw [← sub_sub, ← add_comm, ← add_assoc]
    have h1: a * r k ⬝ᵥ A *ᵥ a • r k + xk k ⬝ᵥ A *ᵥ xk k + 2 * xk k ⬝ᵥ A *ᵥ a • r k - 2 * b ⬝ᵥ xk k - 2 * (a * b ⬝ᵥ r k)
    = a * r k ⬝ᵥ A *ᵥ a • r k + 2 * xk k ⬝ᵥ A *ᵥ a • r k - 2 * (a * b ⬝ᵥ r k) + (xk k ⬝ᵥ A *ᵥ xk k - 2 * b ⬝ᵥ xk k)
     := by ring
    rw [h1]; congr 1
    have h2: a * r k ⬝ᵥ A *ᵥ a • r k =a ^ 2 * r k ⬝ᵥ A *ᵥ r k := by
      rw [Matrix.mulVec_smul]; simp; rw [← mul_assoc]; ring
    rw [h2]; apply eq_of_sub_eq_zero; ring_nf
    have h3: - (b ⬝ᵥ r k) + r k ⬝ᵥ r k + (A *ᵥ xk k)⬝ᵥr k = 0 := by
      rw [rk_def]; simp; ring
    calc
      _ = 2 * a * - (b ⬝ᵥ r k) + a * r k ⬝ᵥ r k * 2 + xk k ⬝ᵥ A *ᵥ a • r k * 2 := by
        simp; exact Eq.symm (mul_rotate 2 a (b ⬝ᵥ r k))
      _ = 2 * a * - (b ⬝ᵥ r k) + 2 * a * r k ⬝ᵥ r k + xk k ⬝ᵥ A *ᵥ a • r k * 2 := by
        simp; exact Eq.symm (mul_rotate 2 a (r k ⬝ᵥ r k))
      _ = 2 * a * - (b ⬝ᵥ r k) + 2 * a * r k ⬝ᵥ r k + 2 * a * xk k ⬝ᵥ A *ᵥ r k := by
        simp; ring_nf; rw [Matrix.mulVec_smul]; simp
      _ = 2 * a * (- (b ⬝ᵥ r k) + r k ⬝ᵥ r k + xk k ⬝ᵥ A *ᵥ r k) := by
        repeat rw [← mul_add]
      _ = 2 * a * (- (b ⬝ᵥ r k) + r k ⬝ᵥ r k + (A *ᵥ xk k) ⬝ᵥ r k ) := by
        simp; left; refine inner_x_Ay_eq_inner_Ax_y A ?_ (xk k) (r k); exact hA.1
      _ = 0 := by rw [mul_eq_zero, h3]; right; rfl
    exact hA.1
  let g : ℝ → ℝ := fun a : ℝ ↦ ((r k) ⬝ᵥ (A *ᵥ (r k))) * (a ^ 2)
    + (- 2 * ((r k)⬝ᵥ(r k)) ) * a + φ  (xk k)
  obtain hh := hA.2 (r k) hr; simp at hh
  have : IsMinOn g univ (- (- 2 * (r k)⬝ᵥ(r k)) / (2 * ((r k) ⬝ᵥ (A *ᵥ (r k))))) := by
    unfold g; apply quadratic_min; simpa
  field_simp at this
  have hgmin : IsMinOn g univ (α k) := by
    convert this; rw [αk_eq]; split_ifs; field_simp [hh]; ring_nf
  let h : ℝ → ℝ := fun a ↦ φ (xk k + a • (r k))
  have : g = h := by simp [g, h]; ext a; rw [h3key1]; ring
  rw [this] at hgmin; exact fun a ↦ hgmin trivial

theorem φ_is_mono (k : ℕ) (hA : A.PosDef): φ (xk (k+1)) ≤ φ (xk k) := by
  rw [xk_eq_def]; simpa using stepsize_min A x0 b k hA 0

instance A_is_invertible (hA : A.PosDef) : Invertible A := by
  exact (Matrix.PosDef.isUnit hA).invertible

theorem steepest_descent_convergence (x_star : Fin n → ℝ) (hA : A.PosDef)
  (hxs : A *ᵥ x_star = b) :
  let wrapped_A : {X // Matrix.PosDef X} := ⟨A, hA⟩
  let κ := @Matrix.conditionNumber _ _ _ A (A_is_invertible A hA)
  ∀ k, Norm_ofPosDef wrapped_A (xk k - x_star) ≤
    ((κ - 1)/(κ + 1))^k * Norm_ofPosDef wrapped_A (xk 0 - x_star) := by
    sorry

-- theorem steepest_descent_convergence' (x_star : Fin n → ℝ) (hA : A.PosDef)
--   (hxs : A *ᵥ x_star = b) :
--   let wrapped_A : {X // Matrix.PosDef X} := ⟨A, hA⟩
--   let κ := Matrix.conditionNumber' ⟨A, _ , _, _⟩
--   ∀ k, Norm_ofPosDef wrapped_A (xk k - x_star) ≤
--     ((κ - 1)/(κ + 1))^k * Norm_ofPosDef wrapped_A (xk 0 - x_star) := by
--     sorry

end steepest_descent
