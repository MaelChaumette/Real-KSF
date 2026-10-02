import RealKSFLean.Paper.Proposition1Architecture

/-!
# Corollary 1: chainable architectures give Kronecker-sparse factorizations of `Re(A)`

Following [13, Definition 4.12] (and the letter's footnote), two consecutive patterns
`π = (a, b, c, d)` and `π' = (a', b', c', d')` are **chainable** when C1 ∧ C2 ∧ C3 ∧ (`d' ∣ d`)
holds (`Prop1.Chainable2`, `RealKSFLean.Definitions`); an architecture is chainable when every
consecutive pair is. A chainable architecture therefore satisfies the three conditions of
Proposition 1 at every junction (`chainable_conditions`), and Proposition 1
(`RealKSFLean.Paper.Proposition1Architecture`) gives Corollary 1 (`corollary1`): `Re(A)` admits a
Kronecker-sparse factorization with the new architecture `(π'_1, ..., π'_L)` of (3).
-/

open Matrix Prop1

variable (a b c d : ℕ → ℕ)

/-- A chainable architecture satisfies the conditions C1, C2, C3 of Proposition 1 at every
junction. -/
theorem chainable_conditions
    (hchain : ∀ k, Chainable2 (a k) (c k) (d k) (a (k + 1)) (b (k + 1)) (d (k + 1))) (k : ℕ) :
    Conditions (a k) (c k) (d k) (a (k + 1)) (b (k + 1)) (d (k + 1)) :=
  (hchain k).toConditions

variable (hchain : ∀ k, Chainable2 (a k) (c k) (d k) (a (k + 1)) (b (k + 1)) (d (k + 1)))
variable (K_orig : (k : ℕ) → Matrix (Fin (a k) × Fin (b k) × Fin (d k))
  (Fin (a k) × Fin (c k) × Fin (d k)) ℂ)

/-- **Corollary 1.** If `A = K_1 ⋯ K_L` (here `K_orig 0 ⋯ K_orig (L+1)`) is a Kronecker-sparse
factorization with a chainable architecture, then `Re(A) = K̃_1 ⋯ K̃_L` where every `K̃_ℓ` is a
Kronecker-sparse factor with the pattern `π'_ℓ` of (3): `(a_1, b_1, 2c_1, d_1)` for the first
factor, `(a_ℓ, 2b_ℓ, 2c_ℓ, d_ℓ)` for the interior ones and `(a_L, 2b_L, c_L, d_L)` for the last
one. -/
theorem corollary1 (L : ℕ) (ha : ∀ k, 0 < a k) (hb : ∀ k, 0 < b k) (hc : ∀ k, 0 < c k)
    (hd : ∀ k, 0 < d k) (hK : ∀ k, IsKSparse (a k) (b k) (c k) (d k) (K_orig k)) :
    let hC1 := fun k => (hchain k).c1
    (Kprod (Kflat a b c d hC1 K_orig) (L + 2)).map Complex.re =
        KtildeProd a b c d hC1 K_orig (L + 1) *
          (Pfor a b d (L + 1) *
            fromRows ((Kflat a b c d hC1 K_orig (L + 1)).map Complex.re)
              (-((Kflat a b c d hC1 K_orig (L + 1)).map Complex.im))) ∧
      IsKSparse (a 0) (b 0) (2 * c 0) (d 0)
        (Matrix.submatrix
          (Matrix.submatrix (Ktilde a b c d hC1 K_orig 0) (Equiv.refl _)
            (aDouble (chain_c1_at a b c d hC1 0)))
          (finChainEquiv (a 0) (b 0) (d 0)) (finChainEquiv (a 0) (2 * c 0) (d 0))) ∧
      (∀ k, IsKSparse (a (k + 1)) (2 * b (k + 1)) (2 * c (k + 1)) (d (k + 1))
        (Matrix.submatrix
          (Matrix.submatrix (Ktilde a b c d hC1 K_orig (k + 1)) (Equiv.refl _)
            (aDouble (chain_c1_at a b c d hC1 (k + 1))))
          (finChainEquiv (a (k + 1)) (2 * b (k + 1)) (d (k + 1)))
          (finChainEquiv (a (k + 1)) (2 * c (k + 1)) (d (k + 1))))) ∧
      IsKSparse (a (L + 1)) (2 * b (L + 1)) (c (L + 1)) (d (L + 1))
        (Matrix.submatrix
          (Matrix.submatrix
            (Pfor a b d (L + 1) *
              fromRows ((Kflat a b c d hC1 K_orig (L + 1)).map Complex.re)
                (-((Kflat a b c d hC1 K_orig (L + 1)).map Complex.im)))
            (Equiv.refl _) (colCastEquiv a b c d hC1 (L + 1)))
          (finChainEquiv (a (L + 1)) (2 * b (L + 1)) (d (L + 1)))
          (finChainEquiv (a (L + 1)) (c (L + 1)) (d (L + 1)))) := by
  intro hC1
  exact ⟨re_Kprod_eq_KtildeProd a b c d hC1 K_orig L,
    ktilde_zero_isKSparse a b c d hC1 K_orig (hchain 0).c2 (hchain 0).c3 (ha 0) (ha 1) (hb 0)
      (hc 0) (hd 0) (hb 1) (hd 1) (hK 0),
    fun k => ktilde_succ_isKSparse a b c d hC1 K_orig k (hchain _).c2 (hchain _).c3 (ha _) (ha _)
      (hb _) (hc _) (hd _) (hb _) (hd _) (hK _),
    ktilde_last_isKSparse a b c d hC1 K_orig L (hb _) (hc _) (hd _) (hK _)⟩
