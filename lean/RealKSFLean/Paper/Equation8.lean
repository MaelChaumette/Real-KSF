import RealKSFLean.Definitions

/-!
# Equation (8): the commutation matrix turns a "row-repeat" into another "row-repeat"

Equation (8) of the letter (inside the proof of Lemma 1) states, for `A ∈ ℂ^{a×p}`,
`A ⊗ 1_{2×1} = C_{a,2} · (1_{2×1} ⊗ A)`. The paper derives it from the identity
`A ⊗ B = C_{m,n} (B ⊗ A) C_{p,q}ᵀ` of [21, Theorem 3.1], specialized to `n = 2`, `q = 1`
(using `C_{p,1} = I_p`).

Both sides are matrices built from `A` by stacking two identical copies of `A` as row-blocks:
the right-hand side stacks them in the order `(copy, row)` (i.e. `A` is *repeated* along the
`Fin 2` factor placed *first*), the left-hand side stacks them in the order `(row, copy)`
(the `Fin 2` factor placed *last*). Multiplying by the commutation matrix on the left is
exactly what swaps between these two stacking orders. We state this directly (with a general
index type `p` in place of the specific doubling `Fin 2`, since the argument does not use
`p = Fin 2` at all) instead of going through `Matrix.kroneckerMap`: the trivial `1×1`
Kronecker factor used to write `1_{2×1}` in the paper carries no information, and inlining it
away turns the identity into a one-line computation with `Matrix.mul_apply`.

This is exactly the fact used (packaged with the mixed-product property of the Kronecker
product) to prove Lemma 1 (`RealKSFLean.Paper.Lemma1.Pperm_mul_repeatFst`, which builds
`P_π := C_{a,2} ⊗ I_{bd}` directly from `commutationMatrix_mul_repeatFst` below).
-/

open Matrix

variable {m p q : Type*} [DecidableEq m] [DecidableEq p] [Fintype m] [Fintype p]
variable {R : Type*} [NonAssocSemiring R]

/-- **Equation (8).** Left-multiplying `repeatFst A` (the `A` repeated with the "copy index" `p`
placed *first*) by the commutation matrix `commutationMatrix m p R` (i.e. `C_{m,p}`) yields
`repeatSnd A` (the same repeated matrix, with the copy index placed *last*):
`C_{m,p} · (1_{p×1} ⊗ A) = A ⊗ 1_{p×1}`. -/
theorem commutationMatrix_mul_repeatFst (A : Matrix m q R) :
    commutationMatrix m p R * repeatFst A = repeatSnd A := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single i.swap]
  · simp [commutationMatrix, repeatFst, repeatSnd]
  · intro k _ hk
    have hik : i ≠ k.swap := fun h => hk (by rw [h, Prod.swap_swap])
    simp [commutationMatrix, hik]
  · exact fun h => absurd (Finset.mem_univ _) h
