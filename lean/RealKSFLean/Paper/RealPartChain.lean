import RealKSFLean.Definitions
import RealKSFLean.Paper.RealPart

/-!
# The pre-factorization of the real part (equation (1))

Given a sequence of complex matrices `K 0, K 1, ..., K (L-1)` with
`K k : Matrix (J k) (J (k+1)) ℂ`, this file shows (Section III-A) that the real part of the
product `K 0 * K 1 * ... * K (L-1)` can be written as a product of `L` *real* matrices
`Kbar 0, ..., Kbar (L-1)` (`RealKSFLean.Definitions`), obtained by doubling the row/column spaces
of all factors except the very first row space `J 0`:

* `Kbar 0 := [Re (K 0) | Im (K 0)]` (a `fromCols` block)
* `Kbar k := [Re (K k)  Im (K k) ; -Im (K k)  Re (K k)]` (a `fromBlocks` block), for `0 < k`

so that
`Re (K 0 * ... * K (L-1))
  = Kbar 0 * Kbar 1 * ... * Kbar (L-2) * fromRows (Re (K (L-1))) (-(Im (K (L-1))))`.

We package this as: `Re (Kprod K L) = the "columns" of Kbarprod K L`, i.e. the doubled product
`Kbarprod K L : Matrix (J 0) (J2 J L) ℝ` (where `J2 J L = J L ⊕ J L` for `L ≥ 1`) is exactly
`fromCols (Re (Kprod K L)) (Im (Kprod K L))`. This is `chain_re_im` below; the paper's formula
(1) for `Re` alone is `chain_re` (and the analogous formula for `Im` is `chain_im`), obtained by
peeling off the last factor as a `fromRows` block instead of a `fromBlocks` block.

Section III-D notes that the imaginary part reduces to the real part, since
`Im(K_1 ⋯ K_L) = Re((-𝚥 K_1) ⋯ K_L)` and `-𝚥 K_1` is Kronecker-sparse with the same pattern as
`K_1`; more generally the same holds for `Re(z K_1 ⋯ K_L)`, `z ∈ ℂ`. This is
`Kprod_scaleFirst`/`im_Kprod_eq_re_scaleFirst` below (and `IsKSparse.smul`,
`RealKSFLean.Paper.Definition1`, for the sparsity of `z K_1`).
-/

open Matrix

variable {J : ℕ → Type*} [∀ k, Fintype (J k)] [∀ k, DecidableEq (J k)]

/-- The key recursive identity: the doubled product `Kbarprod K L` is exactly
`[Re (Kprod K L) | Im (Kprod K L)]`, for every `L ≥ 1`. -/
theorem chain_re_im (K : (k : ℕ) → Matrix (J k) (J (k + 1)) ℂ) (L : ℕ) :
    Kbarprod K (L + 1) =
      fromCols ((Kprod K (L + 1)).map Complex.re) ((Kprod K (L + 1)).map Complex.im) := by
  induction L with
  | zero =>
    change Kbarprod K 0 * Kbar K 0 = _
    simp [Kbarprod, Kbar, Kprod]
  | succ L ih =>
    change Kbarprod K (L + 1) * Kbar K (L + 1) = _
    rw [ih, Kbar, fromCols_mul_fromBlocks]
    change _ = fromCols ((Kprod K (L + 1) * K (L + 1)).map Complex.re)
      ((Kprod K (L + 1) * K (L + 1)).map Complex.im)
    rw [re_mul, im_mul, fromCols_mul_fromRows, fromCols_mul_fromRows]

/-- Equation (1): `Re (K 0 * ... * K (L+1))` is the product of the `L + 1` real factors
`Kbar 0, ..., Kbar L` (doubling everything but the input space) followed by the final
factor `[Re (K (L+1)) ; -Im (K (L+1))]` acting only on the output. -/
theorem chain_re (K : (k : ℕ) → Matrix (J k) (J (k + 1)) ℂ) (L : ℕ) :
    (Kprod K (L + 2)).map Complex.re =
      Kbarprod K (L + 1) *
        fromRows ((K (L + 1)).map Complex.re) (-((K (L + 1)).map Complex.im)) := by
  change (Kprod K (L + 1) * K (L + 1)).map Complex.re = _
  rw [re_mul, ← chain_re_im]

/-- Equation (1), imaginary-part version: `Im (K 0 * ... * K (L+1))` uses the same factors
`Kbar 0, ..., Kbar L`, followed by `[Im (K (L+1)) ; Re (K (L+1))]`. -/
theorem chain_im (K : (k : ℕ) → Matrix (J k) (J (k + 1)) ℂ) (L : ℕ) :
    (Kprod K (L + 2)).map Complex.im =
      Kbarprod K (L + 1) *
        fromRows ((K (L + 1)).map Complex.im) ((K (L + 1)).map Complex.re) := by
  change (Kprod K (L + 1) * K (L + 1)).map Complex.im = _
  rw [im_mul, ← chain_re_im]

/-- Multiplying the first factor by `z` multiplies the product by `z`: the factors
`scaleFirst z K` are a factorization of `z K_1 ⋯ K_L`. -/
theorem Kprod_scaleFirst (z : ℂ) (K : (k : ℕ) → Matrix (J k) (J (k + 1)) ℂ) (L : ℕ) :
    Kprod (scaleFirst z K) (L + 1) = z • Kprod K (L + 1) := by
  induction L with
  | zero => simp [Kprod, scaleFirst]
  | succ L ih =>
    change Kprod (scaleFirst z K) (L + 1) * scaleFirst z K (L + 1) =
      z • (Kprod K (L + 1) * K (L + 1))
    rw [ih]
    simp [scaleFirst, Matrix.smul_mul]

/-- **Section III-D.** `Im(K_1 ⋯ K_L) = Re((-𝚥 K_1) ⋯ K_L)`: the imaginary part of a product is
the real part of the product with the first factor multiplied by `-𝚥`, so every result on the
real part (equation (1), Proposition 1, Corollary 1) applies to the imaginary part. -/
theorem im_Kprod_eq_re_scaleFirst (K : (k : ℕ) → Matrix (J k) (J (k + 1)) ℂ) (L : ℕ) :
    (Kprod K (L + 1)).map Complex.im =
      (Kprod (scaleFirst (-Complex.I) K) (L + 1)).map Complex.re := by
  rw [Kprod_scaleFirst]
  ext i j
  simp
