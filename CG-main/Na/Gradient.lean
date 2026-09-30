import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix

#check InnerProductSpace

noncomputable section Gradient

open Matrix

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup Matrix.frobeniusNormedAddCommGroup

noncomputable instance Matrix.Innerproductspace
    {m : Type u_3} {n : Type u_4} [Fintype m] [Fintype n]  :
    InnerProductSpace ℝ (Matrix m n ℝ) where
  norm_smul_le := by sorry
  inner := fun A B => trace (A * Bᵀ)
  conj_inner_symm := by sorry
  norm_sq_eq_re_inner := by sorry
  add_left := by sorry
  smul_left := by sorry

noncomputable instance Matrix.CompleteSpace
    {m : Type u_3} {n : Type u_4} [Fintype m] [Fintype n]  :
    CompleteSpace (Matrix m n ℝ) where
  complete := by sorry

variable {m : Type u_3} {n : Type u_4} [Fintype m] [Fintype n]

end Gradient
