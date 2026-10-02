import Mathlib.LinearAlgebra.Matrix.Vec
import RealKSFLean.Definitions

/-!
# Definition 2: the commutation matrix

**Definition 2** of the letter (following [21]) defines the commutation matrix `C_{m,n}` as the
permutation matrix such that, for every `M ∈ ℝ^{m×n}`, `C_{m,n} vec(M) = vec(Mᵀ)`, where `vec`
stacks the columns of `M`; equivalently, it is the permutation
`σ(i + m(j-1)) = j + n(i-1)` of `⟦1, mn⟧`.

In Lean, `commutationMatrix m n R` (`RealKSFLean.Definitions`) is defined directly as the
permutation matrix of `Prod.swap : m × n → n × m` (this is `σ`, with the flat index
`i + m(j-1)` of `vec(M)` represented by the pair `(j, i)` as in Mathlib's `Matrix.vec`).
`commutationMatrix_mulVec_vec` below checks that it satisfies the defining property of
Definition 2.
-/

variable (m n : Type*) [DecidableEq m] [DecidableEq n]

/-- **Definition 2.** `C_{m,n} vec(M) = vec(Mᵀ)` for every `M : Matrix m n R'`. -/
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
