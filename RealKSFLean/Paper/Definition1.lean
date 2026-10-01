import RealKSFLean.Definitions

/-!
# Definition 1: Kronecker-sparse factors, and their real/imaginary parts

For `a b c d : ℕ`, a matrix in `ℝ^{abd × acd}` (or `ℂ^{abd × acd}`) is a *Kronecker-sparse
factor of (sparsity) pattern `π = (a, b, c, d)`* if its support is included in the support of
`S_π := I_a ⊗ 1_{b×c} ⊗ I_d` (`IsKSparse`, `RealKSFLean.Definitions`).

This file records the first observation of Section III-A (case `L = 1`): being Kronecker-sparse
only depends on the support, so a single factor's real and imaginary parts are Kronecker-sparse
with the *same* pattern as the original factor. It also records the observation of Section III-D
used for the imaginary part: `z K` (e.g. `-𝚥 K`) is Kronecker-sparse with the same pattern as `K`.
-/

variable {a b c d : ℕ} {R : Type*}

/-- Being a Kronecker-sparse factor only depends on the support, so applying any function
fixing `0` entrywise (in particular `Re` or `Im`) to a Kronecker-sparse factor of pattern
`(a, b, c, d)` yields another Kronecker-sparse factor of the *same* pattern. -/
theorem IsKSparse.map [Zero R] {R' : Type*} [Zero R'] {K : Matrix (Fin a × Fin b × Fin d)
    (Fin a × Fin c × Fin d) R} (h : IsKSparse a b c d K) {f : R → R'} (hf : f 0 = 0) :
    IsKSparse a b c d (K.map f) := by
  intro i j hij
  simp [Matrix.map_apply, h i j hij, hf]

/-- Real part of a single Kronecker-sparse factor: same pattern. -/
theorem IsKSparse.re {K : Matrix (Fin a × Fin b × Fin d) (Fin a × Fin c × Fin d) ℂ}
    (h : IsKSparse a b c d K) : IsKSparse a b c d (K.map Complex.re) :=
  h.map Complex.zero_re

/-- Imaginary part of a single Kronecker-sparse factor: same pattern. -/
theorem IsKSparse.im {K : Matrix (Fin a × Fin b × Fin d) (Fin a × Fin c × Fin d) ℂ}
    (h : IsKSparse a b c d K) : IsKSparse a b c d (K.map Complex.im) :=
  h.map Complex.zero_im

/-- A scalar multiple `z • K` (e.g. `-𝚥 K`, Section III-D) of a Kronecker-sparse factor is
Kronecker-sparse with the *same* pattern. -/
theorem IsKSparse.smul {K : Matrix (Fin a × Fin b × Fin d) (Fin a × Fin c × Fin d) ℂ}
    (h : IsKSparse a b c d K) (z : ℂ) : IsKSparse a b c d (z • K) := by
  intro i j hij
  simp [h i j hij]
