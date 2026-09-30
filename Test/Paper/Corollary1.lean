import Test.Support.ChainAssembly
import Test.Support.ChainSparse
import Test.Paper.RealPartChain

/-!
# Corollary 1: chainable architectures give Kronecker-sparse factorizations of `Re(K)`

Following [3, Definition 4.12] (as communicated for this development): two consecutive chains
`π = (a, b, c, d)` and `π' = (a', b', c', d')` are **chainable** when `C2` and `C3` hold (and,
additionally, `d' ∣ d`, not needed here — see `Prop1.Chainable2`, `Test.Definitions`). An
architecture (a chain `π_1, ..., π_L`) is chainable when every consecutive pair is. The
*pairwise* arithmetic statement — a chainable pair satisfies C1, C2, C3, hence
`Prop1.Condition10` — is `Prop1.chainable_condition10` (`Test.Paper.Proposition1`); this file
assembles the actual consequence for a whole chainable architecture: `Re(K)` admits a
Kronecker-sparse factorization with the new chain `(π̃_1, ..., π̃_L)`.

* `re_Kprod_eq_KtildeProd` is the factorization itself: `Re(K)`, restricted to the first
  `L + 2` factors of the chain, equals the permuted partial product `KtildeProd (L + 1)`
  followed by a last factor acting only on the final output space.
* `ktilde_zero_isKSparse`/`ktilde_succ_isKSparse` show that every factor `K̃_ℓ` of this new
  chain is *genuinely* Kronecker-sparse, in the literal sense of Definition 1.

Together, these are exactly Corollary 1: a chainable architecture on `K` implies `Re(K)` admits
a Kronecker-sparse factorization.
-/

open Matrix Prop1

variable (a b c d : ℕ → ℕ)
variable (hchain : ∀ k, Chainable2 (a k) (c k) (d k) (a (k + 1)) (b (k + 1)) (d (k + 1)))
variable (K_orig : (k : ℕ) → Matrix (Fin (a k) × Fin (b k) × Fin (d k))
  (Fin (a k) × Fin (c k) × Fin (d k)) ℂ)

/-- **Corollary 1's factorization**: `Re K`, restricted to the first `L + 2` factors of the
chain, equals the permuted partial product `KtildeProd (L + 1)` followed by a last factor
acting only on `K_{L+1}`'s own output space (the one factor that is *not* doubled by any
`Pfor`, exactly as in `chain_re`/equation (3)). Combines `chain_re` (equation (3), applied to
the flat chain `Kflat`) with the telescoping invariant `KtildeProd_eq`
(`Test.Support.ChainAssembly`), cancelling the inserted `Pfor (L+1)ᵀ · Pfor (L+1)` pair. -/
theorem re_Kprod_eq_KtildeProd (L : ℕ) :
    (Kprod (Kflat a b c d hchain K_orig) (L + 2)).map Complex.re =
      KtildeProd a b c d hchain K_orig (L + 1) *
        (Pfor a b d (L + 1) *
          fromRows ((Kflat a b c d hchain K_orig (L + 1)).map Complex.re)
            (-((Kflat a b c d hchain K_orig (L + 1)).map Complex.im))) := by
  rw [chain_re, KtildeProd_eq, Matrix.mul_assoc, ← Matrix.mul_assoc (Pfor a b d (L + 1))ᵀ,
    Pfor_orthogonal, Matrix.one_mul]

/-- **`K̃_0` is a genuine Kronecker-sparse factor of chain `(a_0, b_0, 2 c_0, d_0)`**, in the
literal `Fin a × Fin b × Fin d`-typed sense of Definition 1 (`IsKSparse`), not just flatly. -/
theorem ktilde_zero_isKSparse (ha0 : 0 < a 0) (ha1 : 0 < a 1) (hb0 : 0 < b 0) (hc0 : 0 < c 0)
    (hd00 : 0 < d 0) (hb1 : 0 < b 1) (hd1 : 0 < d 1)
    (hKorig : IsKSparse (a 0) (b 0) (c 0) (d 0) (K_orig 0)) :
    IsKSparse (a 0) (b 0) (2 * c 0) (d 0)
      (Matrix.submatrix
        (Matrix.submatrix (Ktilde a b c d hchain K_orig 0) (Equiv.refl _)
          (aDouble (chain_c1_at a b c d hchain 0)))
        (finChainEquiv (a 0) (b 0) (d 0)) (finChainEquiv (a 0) (2 * c 0) (d 0))) := by
  rw [isKSparse_submatrix_finChainEquiv_iff (a 0) (b 0) (2 * c 0) (d 0) hb0 (by positivity) hd00]
  exact ktilde_zero_ksparse a b c d hchain K_orig ha0 ha1 hb0 hc0 hd00 hb1 hd1 hKorig

/-- **`K̃_{k+1}` is a genuine Kronecker-sparse factor of chain
`(a_{k+1}, 2 b_{k+1}, 2 c_{k+1}, d_{k+1})`**, in the literal `Fin a × Fin b × Fin d`-typed sense
of Definition 1 (`IsKSparse`), not just flatly. Together with `ktilde_zero_isKSparse`, this
completes Corollary 1: every factor `K̃_ℓ` of the new chain assembled from a chainable
architecture is genuinely Kronecker-sparse. -/
theorem ktilde_succ_isKSparse (k : ℕ) (ha1 : 0 < a (k + 1)) (ha2 : 0 < a (k + 2))
    (hb1 : 0 < b (k + 1)) (hc1 : 0 < c (k + 1)) (hd1 : 0 < d (k + 1)) (hb2 : 0 < b (k + 2))
    (hd2 : 0 < d (k + 2))
    (hKorig : IsKSparse (a (k + 1)) (b (k + 1)) (c (k + 1)) (d (k + 1)) (K_orig (k + 1))) :
    IsKSparse (a (k + 1)) (2 * b (k + 1)) (2 * c (k + 1)) (d (k + 1))
      (Matrix.submatrix
        (Matrix.submatrix (Ktilde a b c d hchain K_orig (k + 1)) (Equiv.refl _)
          (aDouble (chain_c1_at a b c d hchain (k + 1))))
        (finChainEquiv (a (k + 1)) (2 * b (k + 1)) (d (k + 1)))
        (finChainEquiv (a (k + 1)) (2 * c (k + 1)) (d (k + 1)))) := by
  rw [isKSparse_submatrix_finChainEquiv_iff (a (k + 1)) (2 * b (k + 1)) (2 * c (k + 1))
    (d (k + 1)) (by positivity) (by positivity) hd1]
  exact ktilde_succ_ksparse a b c d hchain K_orig k ha1 ha2 hb1 hc1 hd1 hb2 hd2 hKorig
