import Test.Definitions
import Test.Paper.RealPart

/-!
# The general recursive identity (equation (3))

Given a chain of complex matrices `K 0, K 1, ..., K (L-1)` with `K k : Matrix (J k) (J (k+1)) ℂ`,
this file shows that the real part of the product `K 0 * K 1 * ... * K (L-1)` can be written as
a product of `L` *real* matrices `Kbar 0, ..., Kbar (L-1)` (`Test.Definitions`), obtained by
doubling the row/column spaces of all factors except the very first row space `J 0`:

* `Kbar 0 := [Re (K 0) | Im (K 0)]` (a `fromCols` block)
* `Kbar k := [Re (K k)  Im (K k) ; -Im (K k)  Re (K k)]` (a `fromBlocks` block), for `0 < k`

so that
`Re (K 0 * ... * K (L-1))
  = Kbar 0 * Kbar 1 * ... * Kbar (L-2) * fromRows (Re (K (L-1))) (-(Im (K (L-1))))`.

We package this as: `Re (Kprod K L) = the "columns" of Kbarprod K L`, i.e. the doubled product
`Kbarprod K L : Matrix (J 0) (J2 J L) ℝ` (where `J2 J L = J L ⊕ J L` for `L ≥ 1`) is exactly
`fromCols (Re (Kprod K L)) (Im (Kprod K L))`. This is `chain_re_im` below; the paper's formula
(3) for `Re` alone is `chain_re` (and for `Im`, `chain_im`, used in Remark 2), obtained by
peeling off the last factor as a `fromRows` block instead of a `fromBlocks` block.
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

/-- Equation (3): `Re (K 0 * ... * K (L+1))` is the product of the `L + 1` real factors
`Kbar 0, ..., Kbar L` (doubling everything but the input space) followed by the final
factor `[Re (K (L+1)) ; -Im (K (L+1))]` acting only on the output. -/
theorem chain_re (K : (k : ℕ) → Matrix (J k) (J (k + 1)) ℂ) (L : ℕ) :
    (Kprod K (L + 2)).map Complex.re =
      Kbarprod K (L + 1) *
        fromRows ((K (L + 1)).map Complex.re) (-((K (L + 1)).map Complex.im)) := by
  change (Kprod K (L + 1) * K (L + 1)).map Complex.re = _
  rw [re_mul, ← chain_re_im]

/-- Equation (3), imaginary-part version (used in Remark 2 for the DHT). -/
theorem chain_im (K : (k : ℕ) → Matrix (J k) (J (k + 1)) ℂ) (L : ℕ) :
    (Kprod K (L + 2)).map Complex.im =
      Kbarprod K (L + 1) *
        fromRows ((K (L + 1)).map Complex.im) ((K (L + 1)).map Complex.re) := by
  change (Kprod K (L + 1) * K (L + 1)).map Complex.im = _
  rw [im_mul, ← chain_re_im]
