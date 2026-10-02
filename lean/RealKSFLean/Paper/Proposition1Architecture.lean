import RealKSFLean.Support.ChainAssembly
import RealKSFLean.Support.ChainSparse
import RealKSFLean.Support.Necessity
import RealKSFLean.Paper.RealPartChain

/-!
# Proposition 1, architecture level

`RealKSFLean.Paper.Proposition1` proves, for a *single* junction between two consecutive patterns
`π_ℓ = (a_ℓ, b_ℓ, c_ℓ, d_ℓ)` and `π_{ℓ+1}`, that equation (9) holds if and only if C2 and C3 hold
(given C1). This file assembles the statement of Proposition 1 for a whole architecture
`(π_1, ..., π_L)` satisfying C1 (compatible dimensions, needed to even form the products): with
`K̃_ℓ` defined as in (2) with `P_ℓ := P_{π_ℓ}` as in (7) and `K_ℓ ∈ 𝒦_{π_ℓ}`, the following are
equivalent (`proposition1`):

* C2 and C3 hold at every junction;
* `K̃_ℓ ∈ 𝒦_{π'_ℓ}` for every `ℓ`, with `π'_ℓ` as in (3).

Lean indexes the factors from `0`: `K_orig 0, K_orig 1, ...` stand for the paper's
`K_1, K_2, ...`, and the architecture has `L + 2` factors (the paper's `L ≥ 2`).

* `re_Kprod_eq_KtildeProd` is the factorization itself: `Re(K)`, restricted to the first
  `L + 2` factors, equals the permuted partial product `KtildeProd (L + 1)` followed by the last
  factor `K̃_L := P_L · K̄_L`.
* **Sufficiency.** `ktilde_zero_isKSparse` (`π'_1 = (a_1, b_1, 2c_1, d_1)`),
  `ktilde_succ_isKSparse` (`π'_ℓ = (a_ℓ, 2b_ℓ, 2c_ℓ, d_ℓ)`) and `ktilde_last_isKSparse`
  (`π'_L = (a_L, 2b_L, c_L, d_L)`, no condition needed) show that every factor `K̃_ℓ` of the new
  architecture is *genuinely* Kronecker-sparse, in the literal sense of Definition 1.
* **Necessity.** `conditions_of_ktilde_zero`/`conditions_of_ktilde_succ`: if the factor `K̃_ℓ`
  built from the Kronecker-sparse factors `K_k := (1 + 𝚥) S_{π_k}` (`ksWitness`) lies in
  `𝒦_{π'_ℓ}`, then C2 and C3 hold at the junction between `π_ℓ` and `π_{ℓ+1}`.
-/

open Matrix Prop1

variable (a b c d : ℕ → ℕ)
variable (hC1 : ∀ k, C1 (a k) (c k) (d k) (a (k + 1)) (b (k + 1)) (d (k + 1)))
variable (K_orig : (k : ℕ) → Matrix (Fin (a k) × Fin (b k) × Fin (d k))
  (Fin (a k) × Fin (c k) × Fin (d k)) ℂ)

/-- **The factorization of Proposition 1**: `Re K`, restricted to the first `L + 2` factors,
equals the permuted partial product `KtildeProd (L + 1)` followed by the last factor
`K̃_L = P_L · K̄_L` (`K̄_L` being the one factor whose output space is *not* doubled, exactly as
in `chain_re`/equation (1)). Combines `chain_re` (equation (1), applied to the flat sequence
`Kflat`) with the telescoping invariant `KtildeProd_eq`
(`RealKSFLean.Support.ChainAssembly`), cancelling the inserted `Pfor (L+1)ᵀ · Pfor (L+1)` pair. -/
theorem re_Kprod_eq_KtildeProd (L : ℕ) :
    (Kprod (Kflat a b c d hC1 K_orig) (L + 2)).map Complex.re =
      KtildeProd a b c d hC1 K_orig (L + 1) *
        (Pfor a b d (L + 1) *
          fromRows ((Kflat a b c d hC1 K_orig (L + 1)).map Complex.re)
            (-((Kflat a b c d hC1 K_orig (L + 1)).map Complex.im))) := by
  rw [chain_re, KtildeProd_eq, Matrix.mul_assoc, ← Matrix.mul_assoc (Pfor a b d (L + 1))ᵀ,
    Pfor_orthogonal, Matrix.one_mul]

/-- **`K̃_0` is a genuine Kronecker-sparse factor of pattern `π'_1 = (a_0, b_0, 2 c_0, d_0)`**,
in the literal `Fin a × Fin b × Fin d`-typed sense of Definition 1 (`IsKSparse`), not just
flatly. -/
theorem ktilde_zero_isKSparse (hC2 : C2 (d 0) (b 1) (d 1)) (hC3 : C3 (a 0) (a 1))
    (ha0 : 0 < a 0) (ha1 : 0 < a 1) (hb0 : 0 < b 0) (hc0 : 0 < c 0)
    (hd00 : 0 < d 0) (hb1 : 0 < b 1) (hd1 : 0 < d 1)
    (hKorig : IsKSparse (a 0) (b 0) (c 0) (d 0) (K_orig 0)) :
    IsKSparse (a 0) (b 0) (2 * c 0) (d 0)
      (Matrix.submatrix
        (Matrix.submatrix (Ktilde a b c d hC1 K_orig 0) (Equiv.refl _)
          (aDouble (chain_c1_at a b c d hC1 0)))
        (finChainEquiv (a 0) (b 0) (d 0)) (finChainEquiv (a 0) (2 * c 0) (d 0))) := by
  rw [isKSparse_submatrix_finChainEquiv_iff (a 0) (b 0) (2 * c 0) (d 0) hb0 (by positivity) hd00]
  exact ktilde_zero_ksparse a b c d hC1 K_orig hC2 hC3 ha0 ha1 hb0 hc0 hd00 hb1 hd1 hKorig

/-- **`K̃_{k+1}` is a genuine Kronecker-sparse factor of pattern
`π'_{k+1} = (a_{k+1}, 2 b_{k+1}, 2 c_{k+1}, d_{k+1})`** (interior factors), in the literal
`Fin a × Fin b × Fin d`-typed sense of Definition 1 (`IsKSparse`), not just flatly. -/
theorem ktilde_succ_isKSparse (k : ℕ) (hC2 : C2 (d (k + 1)) (b (k + 2)) (d (k + 2)))
    (hC3 : C3 (a (k + 1)) (a (k + 2))) (ha1 : 0 < a (k + 1)) (ha2 : 0 < a (k + 2))
    (hb1 : 0 < b (k + 1)) (hc1 : 0 < c (k + 1)) (hd1 : 0 < d (k + 1)) (hb2 : 0 < b (k + 2))
    (hd2 : 0 < d (k + 2))
    (hKorig : IsKSparse (a (k + 1)) (b (k + 1)) (c (k + 1)) (d (k + 1)) (K_orig (k + 1))) :
    IsKSparse (a (k + 1)) (2 * b (k + 1)) (2 * c (k + 1)) (d (k + 1))
      (Matrix.submatrix
        (Matrix.submatrix (Ktilde a b c d hC1 K_orig (k + 1)) (Equiv.refl _)
          (aDouble (chain_c1_at a b c d hC1 (k + 1))))
        (finChainEquiv (a (k + 1)) (2 * b (k + 1)) (d (k + 1)))
        (finChainEquiv (a (k + 1)) (2 * c (k + 1)) (d (k + 1)))) := by
  rw [isKSparse_submatrix_finChainEquiv_iff (a (k + 1)) (2 * b (k + 1)) (2 * c (k + 1))
    (d (k + 1)) (by positivity) (by positivity) hd1]
  exact ktilde_succ_ksparse a b c d hC1 K_orig k hC2 hC3 ha1 ha2 hb1 hc1 hd1 hb2 hd2 hKorig

/-- **The last factor `K̃_L = P_L · K̄_L` is a genuine Kronecker-sparse factor of pattern
`π'_L = (a_L, 2 b_L, c_L, d_L)`**, in the literal `Fin a × Fin b × Fin d`-typed sense of
Definition 1 (`IsKSparse`). Together with `ktilde_zero_isKSparse` and `ktilde_succ_isKSparse`,
this completes the "if" direction of Proposition 1: every factor `K̃_ℓ` of the new architecture
is genuinely Kronecker-sparse. -/
theorem ktilde_last_isKSparse (k : ℕ) (hb1 : 0 < b (k + 1)) (hc1 : 0 < c (k + 1))
    (hd1 : 0 < d (k + 1))
    (hKorig : IsKSparse (a (k + 1)) (b (k + 1)) (c (k + 1)) (d (k + 1)) (K_orig (k + 1))) :
    IsKSparse (a (k + 1)) (2 * b (k + 1)) (c (k + 1)) (d (k + 1))
      (Matrix.submatrix
        (Matrix.submatrix
          (Pfor a b d (k + 1) *
            fromRows ((Kflat a b c d hC1 K_orig (k + 1)).map Complex.re)
              (-((Kflat a b c d hC1 K_orig (k + 1)).map Complex.im)))
          (Equiv.refl _) (colCastEquiv a b c d hC1 (k + 1)))
        (finChainEquiv (a (k + 1)) (2 * b (k + 1)) (d (k + 1)))
        (finChainEquiv (a (k + 1)) (c (k + 1)) (d (k + 1)))) := by
  rw [isKSparse_submatrix_finChainEquiv_iff (a (k + 1)) (2 * b (k + 1)) (c (k + 1))
    (d (k + 1)) (by positivity) hc1 hd1]
  exact ktilde_last_ksparse a b c d hC1 K_orig k hb1 hc1 hd1 hKorig

/-- **Necessity of C2 & C3, first junction.** If `K̃_0`, built from the Kronecker-sparse factors
`K_k := (1 + 𝚥) S_{π_k}`, lies in `𝒦_{π'_1}`, then C2 and C3 hold between `π_0` and `π_1`. -/
theorem conditions_of_ktilde_zero (ha0 : 0 < a 0) (ha1 : 0 < a 1) (hb0 : 0 < b 0)
    (hc0 : 0 < c 0) (hd0 : 0 < d 0) (hb1 : 0 < b 1) (hd1 : 0 < d 1)
    (hKS : IsKSparse (a 0) (b 0) (2 * c 0) (d 0)
      (Matrix.submatrix
        (Matrix.submatrix (Ktilde a b c d hC1 (ksWitness a b c d) 0) (Equiv.refl _)
          (aDouble (chain_c1_at a b c d hC1 0)))
        (finChainEquiv (a 0) (b 0) (d 0)) (finChainEquiv (a 0) (2 * c 0) (d 0)))) :
    C2 (d 0) (b 1) (d 1) ∧ C3 (a 0) (a 1) := by
  rw [isKSparse_submatrix_finChainEquiv_iff (a 0) (b 0) (2 * c 0) (d 0) hb0 (by positivity) hd0]
    at hKS
  have h := condition10_of_ktilde_zero a b c d hC1 hb0 hc0 hd0 hb1 hd1 hKS
  exact necessity (a 0) (c 0) (d 0) (a 1) (b 1) (d 1) ha0 ha1 hc0 hd0 hb1 hd1 (hC1 0)
    (by rw [mul_assoc]; exact h)

/-- **Necessity of C2 & C3, interior junctions.** If `K̃_{k+1}`, built from the
Kronecker-sparse factors `K_k := (1 + 𝚥) S_{π_k}`, lies in `𝒦_{π'_{k+1}}`, then C2 and C3 hold
between `π_{k+1}` and `π_{k+2}`. -/
theorem conditions_of_ktilde_succ (k : ℕ) (ha1 : 0 < a (k + 1)) (ha2 : 0 < a (k + 2))
    (hb1 : 0 < b (k + 1)) (hc1 : 0 < c (k + 1)) (hd1 : 0 < d (k + 1)) (hb2 : 0 < b (k + 2))
    (hd2 : 0 < d (k + 2))
    (hKS : IsKSparse (a (k + 1)) (2 * b (k + 1)) (2 * c (k + 1)) (d (k + 1))
      (Matrix.submatrix
        (Matrix.submatrix (Ktilde a b c d hC1 (ksWitness a b c d) (k + 1)) (Equiv.refl _)
          (aDouble (chain_c1_at a b c d hC1 (k + 1))))
        (finChainEquiv (a (k + 1)) (2 * b (k + 1)) (d (k + 1)))
        (finChainEquiv (a (k + 1)) (2 * c (k + 1)) (d (k + 1))))) :
    C2 (d (k + 1)) (b (k + 2)) (d (k + 2)) ∧ C3 (a (k + 1)) (a (k + 2)) := by
  rw [isKSparse_submatrix_finChainEquiv_iff (a (k + 1)) (2 * b (k + 1)) (2 * c (k + 1))
    (d (k + 1)) (by positivity) (by positivity) hd1] at hKS
  have h := condition10_of_ktilde_succ a b c d hC1 k hb1 hc1 hd1 hb2 hd2 hKS
  exact necessity (a (k + 1)) (c (k + 1)) (d (k + 1)) (a (k + 2)) (b (k + 2)) (d (k + 2))
    ha1 ha2 hc1 hd1 hb2 hd2 (hC1 (k + 1)) (by rw [mul_assoc]; exact h)

/-- **Proposition 1.** Consider an architecture `(π_0, ..., π_{L+1})` satisfying C1 (compatible
dimensions). The following are equivalent:

* C2 and C3 hold at every junction `k ≤ L` (between `π_k` and `π_{k+1}`);
* for every choice of Kronecker-sparse factors `K_k ∈ 𝒦_{π_k}`, the permuted factors `K̃_ℓ` of (2)
  (with `P_ℓ := P_{π_ℓ}` as in (7)) satisfy `K̃_ℓ ∈ 𝒦_{π'_ℓ}` with `π'_ℓ` as in (3): the first one
  for `(a_0, b_0, 2c_0, d_0)`, the interior ones for `(a_ℓ, 2b_ℓ, 2c_ℓ, d_ℓ)` and the last one
  `P_{L+1} K̄_{L+1}` for `(a_{L+1}, 2b_{L+1}, c_{L+1}, d_{L+1})`. -/
theorem proposition1 (L : ℕ) (ha : ∀ k, 0 < a k) (hb : ∀ k, 0 < b k) (hc : ∀ k, 0 < c k)
    (hd : ∀ k, 0 < d k) :
    (∀ k ≤ L, C2 (d k) (b (k + 1)) (d (k + 1)) ∧ C3 (a k) (a (k + 1))) ↔
      ∀ K_orig : (k : ℕ) → Matrix (Fin (a k) × Fin (b k) × Fin (d k))
          (Fin (a k) × Fin (c k) × Fin (d k)) ℂ,
        (∀ k, IsKSparse (a k) (b k) (c k) (d k) (K_orig k)) →
        IsKSparse (a 0) (b 0) (2 * c 0) (d 0)
            (Matrix.submatrix
              (Matrix.submatrix (Ktilde a b c d hC1 K_orig 0) (Equiv.refl _)
                (aDouble (chain_c1_at a b c d hC1 0)))
              (finChainEquiv (a 0) (b 0) (d 0)) (finChainEquiv (a 0) (2 * c 0) (d 0))) ∧
          (∀ k < L, IsKSparse (a (k + 1)) (2 * b (k + 1)) (2 * c (k + 1)) (d (k + 1))
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
  constructor
  · intro h K hK
    obtain ⟨h2, h3⟩ := h 0 (Nat.zero_le _)
    refine ⟨ktilde_zero_isKSparse a b c d hC1 K h2 h3 (ha 0) (ha 1) (hb 0) (hc 0) (hd 0) (hb 1)
      (hd 1) (hK 0), fun k hk => ?_,
      ktilde_last_isKSparse a b c d hC1 K L (hb _) (hc _) (hd _) (hK _)⟩
    obtain ⟨h2, h3⟩ := h (k + 1) hk
    exact ktilde_succ_isKSparse a b c d hC1 K k h2 h3 (ha _) (ha _) (hb _) (hc _) (hd _) (hb _)
      (hd _) (hK _)
  · intro h k hk
    obtain ⟨h0, hsucc, -⟩ := h (ksWitness a b c d) (ksWitness_isKSparse a b c d)
    rcases k with _ | k
    · exact conditions_of_ktilde_zero a b c d hC1 (ha 0) (ha 1) (hb 0) (hc 0) (hd 0) (hb 1)
        (hd 1) h0
    · exact conditions_of_ktilde_succ a b c d hC1 k (ha _) (ha _) (hb _) (hc _) (hd _) (hb _)
        (hd _) (hsucc k hk)
