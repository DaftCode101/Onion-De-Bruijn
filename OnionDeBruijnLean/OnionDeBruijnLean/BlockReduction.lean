import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Block

set_option linter.style.longLine false

open Matrix

variable {n m α : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] [CommRing α]

--------------------------------------------------------------------------------
-- 1. Schur Complement Reductions for Block Matrices
--------------------------------------------------------------------------------

lemma det_scalar_block_matrix (X : α) (B : Matrix m n α) (C : Matrix n m α) (D : Matrix n n α) :
    X ^ Fintype.card n * (fromBlocks (diagonal (fun _ => X)) B C D).det = 
    X ^ Fintype.card m * (X • D - C * B).det := by
  let P : Matrix (m ⊕ n) (m ⊕ n) α := fromBlocks 1 0 (-C) (diagonal (fun _ => X))
  let M : Matrix (m ⊕ n) (m ⊕ n) α := fromBlocks (diagonal (fun _ => X)) B C D
  
  have h_PM : P * M = fromBlocks (diagonal (fun _ => X)) B 0 (X • D - C * B) := by
    rw [fromBlocks_multiply]
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [Matrix.diagonal]
    · simp [Matrix.diagonal]
    · simp [Matrix.mul_apply, Matrix.diagonal, Finset.sum_ite_eq]
      ring
    · simp [Matrix.mul_apply, Matrix.diagonal, Matrix.sub_apply, Matrix.smul_apply, Finset.sum_ite_eq]
      ring
  have h_det_P : P.det = X ^ Fintype.card n := by
    rw [det_fromBlocks_zero₁₂, det_one, one_mul, det_diagonal]
    rw [Finset.prod_const, Finset.card_univ]
  have h_det_PM : (P * M).det = X ^ Fintype.card m * (X • D - C * B).det := by
    rw [h_PM, det_fromBlocks_zero₂₁, det_diagonal, Finset.prod_const, Finset.card_univ]
  have h_mult : P.det * M.det = (P * M).det := (det_mul P M).symm
  rw [← h_mult] at h_det_PM
  rw [h_det_P] at h_det_PM
  exact h_det_PM
