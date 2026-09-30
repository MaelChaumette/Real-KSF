import Test.Definitions

/-!
# Lemma 1: the commutation matrix turns a "row-repeat" into another "row-repeat"

**Lemma 1** of the letter states, for `A ∈ ℂ^{m×n}`,
`C_{2,m} · (1_{2×1} ⊗ A) = A ⊗ 1_{2×1}`.

Both sides are matrices built from `A` by stacking two identical copies of `A` as row-blocks:
the left-hand side stacks them in the order `(copy, row)` (i.e. `A` is *repeated* along the
`Fin 2` factor placed *first*), the right-hand side stacks them in the order `(row, copy)`
(the `Fin 2` factor placed *last*). Multiplying by the commutation matrix on the left is
exactly what swaps between these two stacking orders. We state this directly (with a general
index type `p` in place of the specific doubling `Fin 2`, since the argument does not use
`p = Fin 2` at all) instead of going through `Matrix.kroneckerMap`: the trivial `1×1`
Kronecker factor used to write `1_{2×1}` in the paper carries no information, and inlining it
away turns the identity into a one-line computation with `Matrix.mul_apply`.

This is exactly the fact used (packaged with the mixed-product property of the Kronecker
product) to justify the permutation `P_π` of equation (9), and hence Lemma 2
(`Test.Paper.Lemma2.Pperm_mul_repeatFst`, which builds `P_π` directly from
`commutationMatrix_mul_repeatFst` below).
-/

open Matrix

variable {m p q : Type*} [DecidableEq m] [DecidableEq p] [Fintype m] [Fintype p]
variable {R : Type*} [NonAssocSemiring R]

/-- **Lemma 1.** Left-multiplying `repeatFst A` (the `A` repeated with the "copy index" `p`
placed *first*) by the commutation matrix `commutationMatrix m p R` yields `repeatSnd A` (the
same repeated matrix, with the copy index placed *last*): `C_{p,m} · (1_{p×1} ⊗ A) = A ⊗
1_{p×1}`. -/
theorem commutationMatrix_mul_repeatFst (A : Matrix m q R) :
    commutationMatrix m p R * repeatFst A = repeatSnd A := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single i.swap]
  · simp [commutationMatrix, repeatFst, repeatSnd]
  · intro k _ hk
    have hik : i ≠ k.swap := fun h => hk (by rw [h, Prod.swap_swap])
    simp [commutationMatrix, hik]
  · exact fun h => absurd (Finset.mem_univ _) h
