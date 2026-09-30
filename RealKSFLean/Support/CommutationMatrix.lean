import Mathlib.LinearAlgebra.Matrix.Vec
import RealKSFLean.Definitions

/-!
# The commutation matrix, as an actual permutation of vectors

A property of `commutationMatrix` (`RealKSFLean.Definitions`) confirming it deserves its name: it
really does implement the commutation/transpose operation on stacked vectors,
`K.mulVec A.vec = A.transpose.vec`. Not used elsewhere in the development (which only needs
`commutationMatrix_mul_repeatFst`, `RealKSFLean.Paper.Lemma1`), but recorded since it is the
textbook justification for calling `commutationMatrix` a *commutation* matrix.
-/

variable (m n : Type*) [DecidableEq m] [DecidableEq n]

theorem commutationMatrix_mulVec_vec [Fintype m] [Fintype n]
    {R' : Type*} [NonAssocSemiring R'] (A : Matrix m n R') :
    (commutationMatrix m n R').mulVec A.vec = A.transpose.vec := by
  funext i
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i.swap]
  · -- terme central : j = i.swap
    simp [commutationMatrix, Matrix.vec, Matrix.transpose, Prod.swap_swap]
  · -- tous les autres j ne contribuent pas
    intro j _ hj
    have hij : i ≠ j.swap := by
      intro h
      exact hj (by rw [h, Prod.swap_swap])
    simp [commutationMatrix, hij]
  · -- i.swap ∈ univ (trivial, Fintype)
    intro h
    exact absurd (Finset.mem_univ _) h
