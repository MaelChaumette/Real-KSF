import RealKSFLean.Support.Assembly
import RealKSFLean.Support.FlatChain

/-!
# The telescoping assembly

Given an infinite chainable sequence of chains `π_0, π_1, π_2, ...` (`Chainable2` holding at
every junction) and, for each `k`, a genuine Kronecker-sparse factor `K_orig k` of chain `π_k`,
`RealKSFLean.Definitions` builds the flat reindexing `Kflat`, the permuted factors `Ktilde`, and
their partial products `KtildeProd`. This file establishes the **telescoping identity**
`KtildeProd (L+1) = Kbarprod (Kflat) (L+1) * (Pfor (L+1))ᵀ`, proved by induction using
`Pfor_orthogonal` (`Pᵀ P = 1`) to cancel the inserted permutations, mirroring exactly
`RealKSFLean.Paper.RealPartChain.chain_re_im`'s own induction. None of `Jfam`, `Kflat`, `Pfor`,
`Ktilde`, `KtildeProd` or this telescoping lemma appears as such in the paper — they are the
Lean-specific scaffolding needed to build the factorization promised by Corollary 1
(`RealKSFLean.Paper.Corollary1`).
-/

open Matrix Prop1

variable (a b c d : ℕ → ℕ)
variable (hchain : ∀ k, Chainable2 (a k) (c k) (d k) (a (k + 1)) (b (k + 1)) (d (k + 1)))

@[simp] theorem colCastEquiv_apply_val (k : ℕ) (i : Fin (a k * (c k * d k))) :
    (colCastEquiv a b c d hchain k i).val = i.val :=
  natCastEquiv_apply_val _ i

@[simp] theorem colCastEquiv_symm_apply_val (k : ℕ) (j : Jfam a b d (k + 1)) :
    ((colCastEquiv a b c d hchain k).symm j).val = j.val :=
  natCastEquiv_symm_apply_val _ j

/-- **`Pfor` is orthogonal**: it is `PpermF`, which is already the permutation matrix of an
equivalence (`PpermF_eq_submatrix_one`), reindexed by the further equivalence `sumToFinEquiv` —
so it is *also* the permutation matrix of an equivalence, hence orthogonal
(`PpermF_orthogonal`, transported along `sumToFinEquiv`). This is the fact that lets the
telescoping induction below cancel each inserted `Pfor k` against its own transpose. -/
theorem Pfor_orthogonal (k : ℕ) : (Pfor a b d k)ᵀ * Pfor a b d k = 1 := by
  unfold Pfor
  rw [Matrix.transpose_submatrix,
    Matrix.submatrix_mul_equiv (PpermF (a k) (b k) (d k)).transpose (PpermF (a k) (b k) (d k))
      (sumToFinEquiv (a k * (b k * d k))) (Equiv.refl (Fin (a k * (2 * b k * d k))))
      (sumToFinEquiv (a k * (b k * d k))),
    PpermF_orthogonal]
  ext x x'
  simp [Matrix.submatrix_apply, Matrix.one_apply,
    (sumToFinEquiv (a k * (b k * d k))).injective.eq_iff]

variable (K_orig : (k : ℕ) → Matrix (Fin (a k) × Fin (b k) × Fin (d k))
  (Fin (a k) × Fin (c k) × Fin (d k)) ℂ)

set_option maxHeartbeats 800000 in
-- the chained `Matrix.mul_assoc`/`Pfor_orthogonal` rewriting below is elaboration-heavy
/-- **The telescoping invariant**: the permuted partial product `KtildeProd (L+1)` equals the
*original* doubled partial product `Kbarprod (Kflat) (L+1)`, right-multiplied by `(Pfor
(L+1))ᵀ` — i.e. inserting the permutations `Pfor k` between consecutive `Kbar k`'s and
cancelling adjacent `Pfor kᵀ · Pfor k = 1` pairs (`Pfor_orthogonal`) telescopes down to just a
trailing `Pfor (L+1)ᵀ`. This mirrors `chain_re_im`'s own induction exactly. -/
theorem KtildeProd_eq (L : ℕ) :
    KtildeProd a b c d hchain K_orig (L + 1) =
      Kbarprod (Kflat a b c d hchain K_orig) (L + 1) * (Pfor a b d (L + 1))ᵀ := by
  induction L with
  | zero =>
    have h0 : KtildeProd a b c d hchain K_orig 0 = 1 := rfl
    have h1 : Ktilde a b c d hchain K_orig 0 =
        Kbarprod (Kflat a b c d hchain K_orig) 1 * (Pfor a b d 1)ᵀ := by
      change Kbar (Kflat a b c d hchain K_orig) 0 * (Pfor a b d 1)ᵀ = _
      congr 1
      simp [Kbarprod]
    change KtildeProd a b c d hchain K_orig 0 * Ktilde a b c d hchain K_orig 0 = _
    rw [h0, Matrix.one_mul, h1]
  | succ L ih =>
    have hK : Ktilde a b c d hchain K_orig (L + 1) =
        Pfor a b d (L + 1) * Kbar (Kflat a b c d hchain K_orig) (L + 1) *
          (Pfor a b d (L + 1 + 1))ᵀ := rfl
    change KtildeProd a b c d hchain K_orig (L + 1) * Ktilde a b c d hchain K_orig (L + 1) = _
    rw [ih, hK, ← Matrix.mul_assoc,
      Matrix.mul_assoc (Kbarprod (Kflat a b c d hchain K_orig) (L + 1)),
      ← Matrix.mul_assoc (Pfor a b d (L + 1))ᵀ (Pfor a b d (L + 1))
        (Kbar (Kflat a b c d hchain K_orig) (L + 1)),
      Pfor_orthogonal, Matrix.one_mul]
    change Kbarprod (Kflat a b c d hchain K_orig) (L + 1) *
        Kbar (Kflat a b c d hchain K_orig) (L + 1) * (Pfor a b d (L + 1 + 1))ᵀ = _
    rfl
