import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Complex.BigOperators

/-!
# Real and imaginary parts of a product of complex matrices

This file formalizes the "simple linear algebra" behind Section III-A of the paper
*"On the Real Part of Butterfly Factorizations, with Application to Fast Transforms"*:
the real and imaginary parts of a product of two complex matrices, written as products
of real block matrices. Iterating these two identities gives the pre-factorization (1)
of the real part of a product of `L` factors (`RealKSFLean.Paper.RealPartChain`).

The Kronecker-sparse structure itself (Section II) is treated in
`RealKSFLean.Definitions`/`RealKSFLean.Paper.Definition1`; this file only contains the
underlying linear-algebra fact, which holds for arbitrary complex matrices.
-/

open Matrix

variable {m n p : Type*} [Fintype n]

/-- `Re(K₁ K₂) = [Re K₁ | Im K₁] * [Re K₂ ; -Im K₂]` (equation (1) for `L = 2`). -/
theorem re_mul (K₁ : Matrix m n ℂ) (K₂ : Matrix n p ℂ) :
    (K₁ * K₂).map Complex.re =
      fromCols (K₁.map Complex.re) (K₁.map Complex.im) *
        fromRows (K₂.map Complex.re) (-(K₂.map Complex.im)) := by
  rw [fromCols_mul_fromRows]
  ext i k
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, Matrix.neg_apply,
    Complex.re_sum, Complex.mul_re, Finset.sum_sub_distrib, mul_neg, Finset.sum_neg_distrib]
  ring

/-- `Im(K₁ K₂) = [Re K₁ | Im K₁] * [Im K₂ ; Re K₂]`. -/
theorem im_mul (K₁ : Matrix m n ℂ) (K₂ : Matrix n p ℂ) :
    (K₁ * K₂).map Complex.im =
      fromCols (K₁.map Complex.re) (K₁.map Complex.im) *
        fromRows (K₂.map Complex.im) (K₂.map Complex.re) := by
  rw [fromCols_mul_fromRows]
  ext i k
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply,
    Complex.im_sum, Complex.mul_im, Finset.sum_add_distrib]
