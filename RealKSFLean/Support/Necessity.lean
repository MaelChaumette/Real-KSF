import RealKSFLean.Support.ChainSparse

/-!
# The "only if" direction of Proposition 1, at the level of the permuted factors

This file shows that if the permuted factor `K̃_ℓ` (`Ktilde`) built from the witness factors
`K_k := (1 + 𝚥) S_{π_k}` (`ksWitness`) is Kronecker-sparse with the pattern `π'_ℓ` of (3), then
equation (10) (`Prop1.Condition10`) holds at the junction between `π_ℓ` and `π_{ℓ+1}`; Proposition 1
(`Prop1.necessity`) then turns it into C2 ∧ C3 (`RealKSFLean.Paper.Proposition1Architecture`).

The argument is the paper's: the permutation matrices `P_ℓ` only reindex `K̄_ℓ`
(`ktilde_succ_apply`, `ktilde_zero_apply`), and with the witness factors every entry of `K̄_ℓ`
in the first block-row is `1` on the support of the stacked supports and `0` elsewhere
(`kbar_succ_witness_inl`, `kbar_zero_witness`). For a flat index `n = idx(ε, i, k₁, k₂)` of the
stacked rows of `X_ℓ`, we pick a row `x` of `K_ℓ` with the same `(i, k₂)`-label: the entry of
`K̃_ℓ` at `(ρ_{π_ℓ}(x), ρ_{π_{ℓ+1}}(n))` is then `1`, so Kronecker-sparsity of `K̃_ℓ` forces the
labels of these two indices to agree — which is exactly (10) at `n`.
-/

open Matrix Prop1

variable (a b c d : ℕ → ℕ)

/-- `Pfor k` is the permutation matrix of `pforEquiv k`. -/
theorem Pfor_apply (k : ℕ) (I : Fin (a k * (2 * b k * d k))) (p : Jfam a b d k ⊕ Jfam a b d k) :
    Pfor a b d k I p = if I = pforEquiv a b d k p then 1 else 0 := by
  unfold Pfor pforEquiv
  rw [Matrix.submatrix_apply, PpermF_eq_submatrix_one, Matrix.submatrix_apply, Matrix.one_apply]
  rfl

/-- Left-multiplying by `Pfor k` permutes the rows by `pforEquiv k`. -/
theorem Pfor_mul_apply {n : Type*} (k : ℕ) (M : Matrix (Jfam a b d k ⊕ Jfam a b d k) n ℝ)
    (I : Fin (a k * (2 * b k * d k))) (j : n) :
    (Pfor a b d k * M) I j = M ((pforEquiv a b d k).symm I) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ((pforEquiv a b d k).symm I)]
  · simp [Pfor_apply]
  · intro p _ hp
    have h : I ≠ pforEquiv a b d k p := fun h => hp (by rw [h, Equiv.symm_apply_apply])
    simp [Pfor_apply, h]
  · exact fun h => absurd (Finset.mem_univ _) h

/-- Right-multiplying by `(Pfor k)ᵀ` permutes the columns by `pforEquiv k`. -/
theorem mul_PforT_apply {m : Type*} (k : ℕ) (M : Matrix m (Jfam a b d k ⊕ Jfam a b d k) ℝ)
    (i : m) (J : Fin (a k * (2 * b k * d k))) :
    (M * (Pfor a b d k)ᵀ) i J = M i ((pforEquiv a b d k).symm J) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ((pforEquiv a b d k).symm J)]
  · simp [Pfor_apply]
  · intro p _ hp
    have h : J ≠ pforEquiv a b d k p := fun h => hp (by rw [h, Equiv.symm_apply_apply])
    simp [Pfor_apply, h]
  · exact fun h => absurd (Finset.mem_univ _) h

variable (hC1 : ∀ k, C1 (a k) (c k) (d k) (a (k + 1)) (b (k + 1)) (d (k + 1)))
variable (K_orig : (k : ℕ) → Matrix (Fin (a k) × Fin (b k) × Fin (d k))
  (Fin (a k) × Fin (c k) × Fin (d k)) ℂ)

/-- The interior permuted factor `K̃_{k+1} = P_{k+1} K̄_{k+1} P_{k+2}ᵀ` is `K̄_{k+1}` reindexed. -/
theorem ktilde_succ_apply (k : ℕ) (I : Fin (a (k + 1) * (2 * b (k + 1) * d (k + 1))))
    (J : Fin (a (k + 2) * (2 * b (k + 2) * d (k + 2)))) :
    Ktilde a b c d hC1 K_orig (k + 1) I J =
      Kbar (Kflat a b c d hC1 K_orig) (k + 1) ((pforEquiv a b d (k + 1)).symm I)
        ((pforEquiv a b d (k + 2)).symm J) := by
  change (Pfor a b d (k + 1) * Kbar (Kflat a b c d hC1 K_orig) (k + 1) *
    (Pfor a b d (k + 2))ᵀ) I J = _
  rw [mul_PforT_apply, Pfor_mul_apply]

/-- The first permuted factor `K̃_0 = K̄_0 P_1ᵀ` is `K̄_0` with its columns reindexed. -/
theorem ktilde_zero_apply (I : Jfam a b d 0) (J : Fin (a 1 * (2 * b 1 * d 1))) :
    Ktilde a b c d hC1 K_orig 0 I J =
      Kbar (Kflat a b c d hC1 K_orig) 0 I ((pforEquiv a b d 1).symm J) := by
  change (Kbar (Kflat a b c d hC1 K_orig) 0 * (Pfor a b d 1)ᵀ) I J = _
  rw [mul_PforT_apply]

/-- The witness factor `K_k = (1 + 𝚥) S_{π_k}`, read flatly: `1 + 𝚥` on the support, `0` off it. -/
theorem kflat_witness_apply (k : ℕ) (hb : 0 < b k) (hc : 0 < c k) (hd : 0 < d k)
    (x : Jfam a b d k) (y : Jfam a b d (k + 1)) :
    Kflat a b c d hC1 (ksWitness a b c d) k x y =
      if x.val / (b k * d k) = y.val / (c k * d k) ∧ x.val % d k = y.val % d k
        then 1 + Complex.I else 0 := by
  have h := SF_apply (R := ℂ) (a k) (b k) (c k) (d k) hb hc hd x
    ((colCastEquiv a b c d hC1 k).symm y)
  simp only [colCastEquiv_symm_apply_val] at h
  have e : Kflat a b c d hC1 (ksWitness a b c d) k x y =
      (1 + Complex.I) * (SF (a k) (b k) (c k) (d k) : Matrix _ _ ℂ) x
        ((colCastEquiv a b c d hC1 k).symm y) := rfl
  rw [e, h]
  split_ifs <;> simp

/-- The witness factors are Kronecker-sparse. -/
theorem ksWitness_isKSparse (k : ℕ) :
    IsKSparse (a k) (b k) (c k) (d k) (ksWitness a b c d k) := by
  intro i j hij
  rcases hij with h | h <;> simp [ksWitness, SG, h]

/-- With the witness factors, the first block-row of `K̄_{k+1}` is the support indicator. -/
theorem kbar_succ_witness_inl (k : ℕ) (hb : 0 < b (k + 1)) (hc : 0 < c (k + 1))
    (hd : 0 < d (k + 1)) (x : Jfam a b d (k + 1))
    (q : Jfam a b d (k + 2) ⊕ Jfam a b d (k + 2)) :
    Kbar (Kflat a b c d hC1 (ksWitness a b c d)) (k + 1) (Sum.inl x) q =
      if x.val / (b (k + 1) * d (k + 1)) = (q.elim id id).val / (c (k + 1) * d (k + 1)) ∧
          x.val % d (k + 1) = (q.elim id id).val % d (k + 1) then 1 else 0 := by
  have hKbar : Kbar (Kflat a b c d hC1 (ksWitness a b c d)) (k + 1) =
      Matrix.fromBlocks ((Kflat a b c d hC1 (ksWitness a b c d) (k + 1)).map Complex.re)
        ((Kflat a b c d hC1 (ksWitness a b c d) (k + 1)).map Complex.im)
        (-(Kflat a b c d hC1 (ksWitness a b c d) (k + 1)).map Complex.im)
        ((Kflat a b c d hC1 (ksWitness a b c d) (k + 1)).map Complex.re) := rfl
  rw [hKbar]
  rcases q with y | y
  · change (Kflat a b c d hC1 (ksWitness a b c d) (k + 1) x y).re =
      if x.val / (b (k + 1) * d (k + 1)) = y.val / (c (k + 1) * d (k + 1)) ∧
        x.val % d (k + 1) = y.val % d (k + 1) then 1 else 0
    rw [kflat_witness_apply a b c d hC1 (k + 1) hb hc hd]
    split_ifs <;> simp
  · change (Kflat a b c d hC1 (ksWitness a b c d) (k + 1) x y).im =
      if x.val / (b (k + 1) * d (k + 1)) = y.val / (c (k + 1) * d (k + 1)) ∧
        x.val % d (k + 1) = y.val % d (k + 1) then 1 else 0
    rw [kflat_witness_apply a b c d hC1 (k + 1) hb hc hd]
    split_ifs <;> simp

/-- With the witness factors, `K̄_0 = [Re K_0 | Im K_0]` is the support indicator. -/
theorem kbar_zero_witness (hb : 0 < b 0) (hc : 0 < c 0) (hd : 0 < d 0) (x : Jfam a b d 0)
    (q : Jfam a b d 1 ⊕ Jfam a b d 1) :
    Kbar (Kflat a b c d hC1 (ksWitness a b c d)) 0 x q =
      if x.val / (b 0 * d 0) = (q.elim id id).val / (c 0 * d 0) ∧
          x.val % d 0 = (q.elim id id).val % d 0 then 1 else 0 := by
  have hKbar : Kbar (Kflat a b c d hC1 (ksWitness a b c d)) 0 =
      fromCols ((Kflat a b c d hC1 (ksWitness a b c d) 0).map Complex.re)
        ((Kflat a b c d hC1 (ksWitness a b c d) 0).map Complex.im) := rfl
  rw [hKbar]
  rcases q with y | y
  · change (Kflat a b c d hC1 (ksWitness a b c d) 0 x y).re =
      if x.val / (b 0 * d 0) = y.val / (c 0 * d 0) ∧ x.val % d 0 = y.val % d 0 then 1 else 0
    rw [kflat_witness_apply a b c d hC1 0 hb hc hd]
    split_ifs <;> simp
  · change (Kflat a b c d hC1 (ksWitness a b c d) 0 x y).im =
      if x.val / (b 0 * d 0) = y.val / (c 0 * d 0) ∧ x.val % d 0 = y.val % d 0 then 1 else 0
    rw [kflat_witness_apply a b c d hC1 0 hb hc hd]
    split_ifs <;> simp

/-- For a flat index `y` of the `(a, c, d)`-grouping of pattern `π_k`'s column space, a row `x`
of `K_k` carrying the same `(i, k₂)`-label: `x = idx(i, 0, k₂)`. -/
theorem exists_row_label (k : ℕ) (hb : 0 < b k) (hc : 0 < c k) (hd : 0 < d k) (y : ℕ)
    (hy : y < a k * (c k * d k)) :
    ∃ x : Jfam a b d k, x.val / (b k * d k) = y / (c k * d k) ∧ x.val % d k = y % d k := by
  have hbd : 0 < b k * d k := by positivity
  have hcd : 0 < c k * d k := by positivity
  have hQa : y / (c k * d k) < a k :=
    Nat.div_lt_of_lt_mul (lt_of_lt_of_eq hy (mul_comm _ _))
  have hRd : y % d k < d k := Nat.mod_lt _ hd
  have h1 : y % d k < b k * d k := lt_of_lt_of_le hRd (Nat.le_mul_of_pos_left _ hb)
  have hxlt : y / (c k * d k) * (b k * d k) + y % d k < a k * (b k * d k) := by
    have h2 : (y / (c k * d k) + 1) * (b k * d k) ≤ a k * (b k * d k) :=
      Nat.mul_le_mul_right _ hQa
    nlinarith
  refine ⟨⟨y / (c k * d k) * (b k * d k) + y % d k, hxlt⟩, ?_, ?_⟩
  · change (y / (c k * d k) * (b k * d k) + y % d k) / (b k * d k) = _
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hbd, Nat.div_eq_of_lt h1, zero_add]
  · change (y / (c k * d k) * (b k * d k) + y % d k) % d k = _
    rw [show y / (c k * d k) * (b k * d k) + y % d k =
        y % d k + d k * (y / (c k * d k) * b k) by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hRd]

set_option maxHeartbeats 800000 in
-- the label bookkeeping below accumulates many `Nat.div`/`Nat.mod` rewrites
/-- **Necessity, interior junction.** If `K̃_{k+1}` (built from the witness factors) is
Kronecker-sparse with pattern `(a, 2b, 2c, d)_{k+1}`, then equation (10) holds at the junction
between `π_{k+1}` and `π_{k+2}`. -/
theorem condition10_of_ktilde_succ (k : ℕ) (hb1 : 0 < b (k + 1)) (hc1 : 0 < c (k + 1))
    (hd1 : 0 < d (k + 1)) (hb2 : 0 < b (k + 2)) (hd2 : 0 < d (k + 2))
    (hKS : IsKSparseFlat (a (k + 1)) (2 * b (k + 1)) (2 * c (k + 1)) (d (k + 1))
      (Matrix.submatrix (Ktilde a b c d hC1 (ksWitness a b c d) (k + 1)) (Equiv.refl _)
        (aDouble (chain_c1_at a b c d hC1 (k + 1))))) :
    Condition10 (c (k + 1)) (d (k + 1)) (b (k + 2)) (d (k + 2))
      (a (k + 1) * (c (k + 1) * d (k + 1))) := by
  intro n hn
  have hN : a (k + 1) * (c (k + 1) * d (k + 1)) = a (k + 2) * (b (k + 2) * d (k + 2)) :=
    chain_c1_at a b c d hC1 (k + 1)
  have hn' : n < 2 * (a (k + 2) * (b (k + 2) * d (k + 2))) := hN ▸ hn
  obtain ⟨q, hq⟩ : ∃ q, sumToFinEquiv (a (k + 2) * (b (k + 2) * d (k + 2))) q = ⟨n, hn'⟩ :=
    ⟨_, Equiv.apply_symm_apply _ _⟩
  obtain ⟨hymod, -⟩ := sumToFinEquiv_mod_self _ q
  have hyn : (q.elim id id).val = n % (a (k + 1) * (c (k + 1) * d (k + 1))) := by
    rw [hN, ← hymod, hq]
  have hylt : (q.elim id id).val < a (k + 1) * (c (k + 1) * d (k + 1)) :=
    lt_of_lt_of_eq (q.elim id id).isLt hN.symm
  obtain ⟨x, hxQ, hxR⟩ := exists_row_label a b c d (k + 1) hb1 hc1 hd1 _ hylt
  obtain ⟨I, hI⟩ : ∃ I, I = pforEquiv a b d (k + 1) (Sum.inl x) := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J, J = pforEquiv a b d (k + 2) q := ⟨_, rfl⟩
  have hval : Ktilde a b c d hC1 (ksWitness a b c d) (k + 1) I J = 1 := by
    rw [ktilde_succ_apply, hI, hJ, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      kbar_succ_witness_inl a b c d hC1 k hb1 hc1 hd1]
    simp [hxQ, hxR]
  have hlab : I.val / (2 * b (k + 1) * d (k + 1)) = J.val / (2 * c (k + 1) * d (k + 1)) ∧
      I.val % d (k + 1) = J.val % d (k + 1) := by
    by_contra hcon
    have hor : I.val / (2 * b (k + 1) * d (k + 1)) ≠
          ((aDouble (chain_c1_at a b c d hC1 (k + 1))).symm J).val / (2 * c (k + 1) * d (k + 1)) ∨
        I.val % d (k + 1) ≠
          ((aDouble (chain_c1_at a b c d hC1 (k + 1))).symm J).val % d (k + 1) := by
      rw [aDouble_symm_apply_val]
      exact not_and_or.mp hcon
    have h0 := hKS I ((aDouble (chain_c1_at a b c d hC1 (k + 1))).symm J) hor
    simp only [Matrix.submatrix_apply, Equiv.refl_apply, Equiv.apply_symm_apply] at h0
    rw [hval] at h0
    exact one_ne_zero h0
  have hPp : (PpermF (a (k + 1)) (b (k + 1)) (d (k + 1)) : Matrix _ _ ℝ) I
      (sumToFinEquiv (a (k + 1) * (b (k + 1) * d (k + 1))) (Sum.inl x)) ≠ 0 := by
    change Pfor a b d (k + 1) I (Sum.inl x) ≠ 0
    simp [Pfor_apply, hI]
  obtain ⟨hr1, hr2⟩ := row_label_eq (a (k + 1)) (b (k + 1)) (d (k + 1)) hb1 hd1 I (Sum.inl x) hPp
  simp only [Sum.elim_inl, id_eq] at hr1 hr2
  have hJval : J.val = rho (b (k + 2)) (d (k + 2)) (a (k + 2) * (b (k + 2) * d (k + 2))) n := by
    have h := (rhoEquiv_apply_eq_iff (a (k + 2)) (b (k + 2)) (d (k + 2)) hb2 hd2 J
      (sumToFinEquiv _ q)).mp (by rw [hJ]; rfl)
    rw [h, hq]
  have hrho : rho (b (k + 2)) (d (k + 2)) (a (k + 1) * (c (k + 1) * d (k + 1))) n = J.val := by
    rw [hJval, hN]
  have hdN : d (k + 1) ∣ a (k + 1) * (c (k + 1) * d (k + 1)) := ⟨a (k + 1) * c (k + 1), by ring⟩
  have e1 : J.val / (2 * c (k + 1) * d (k + 1)) =
      n % (a (k + 1) * (c (k + 1) * d (k + 1))) / (c (k + 1) * d (k + 1)) := by
    rw [← hlab.1, congrArg (I.val / ·) (Nat.mul_assoc 2 (b (k + 1)) (d (k + 1))), hr1, hxQ,
      hyn]
  have e2 : J.val % d (k + 1) = n % d (k + 1) := by
    rw [← hlab.2, hr2, hxR, hyn, Nat.mod_mod_of_dvd n hdN]
  change (rho (b (k + 2)) (d (k + 2)) (a (k + 1) * (c (k + 1) * d (k + 1))) n /
      (2 * c (k + 1) * d (k + 1)),
    rho (b (k + 2)) (d (k + 2)) (a (k + 1) * (c (k + 1) * d (k + 1))) n % d (k + 1)) =
    (n % (a (k + 1) * (c (k + 1) * d (k + 1))) / (c (k + 1) * d (k + 1)), n % d (k + 1))
  rw [hrho, e1, e2]

set_option maxHeartbeats 800000 in
-- same bookkeeping as `condition10_of_ktilde_succ`, without the row-side permutation
/-- **Necessity, first junction.** If `K̃_0` (built from the witness factors) is
Kronecker-sparse with pattern `(a_0, b_0, 2c_0, d_0)`, then equation (10) holds at the junction
between `π_0` and `π_1`. -/
theorem condition10_of_ktilde_zero (hb0 : 0 < b 0) (hc0 : 0 < c 0) (hd0 : 0 < d 0)
    (hb1 : 0 < b 1) (hd1 : 0 < d 1)
    (hKS : IsKSparseFlat (a 0) (b 0) (2 * c 0) (d 0)
      (Matrix.submatrix (Ktilde a b c d hC1 (ksWitness a b c d) 0) (Equiv.refl _)
        (aDouble (chain_c1_at a b c d hC1 0)))) :
    Condition10 (c 0) (d 0) (b 1) (d 1) (a 0 * (c 0 * d 0)) := by
  intro n hn
  have hN : a 0 * (c 0 * d 0) = a 1 * (b 1 * d 1) := chain_c1_at a b c d hC1 0
  have hn' : n < 2 * (a 1 * (b 1 * d 1)) := hN ▸ hn
  obtain ⟨q, hq⟩ : ∃ q, sumToFinEquiv (a 1 * (b 1 * d 1)) q = ⟨n, hn'⟩ :=
    ⟨_, Equiv.apply_symm_apply _ _⟩
  obtain ⟨hymod, -⟩ := sumToFinEquiv_mod_self _ q
  have hyn : (q.elim id id).val = n % (a 0 * (c 0 * d 0)) := by
    rw [hN, ← hymod, hq]
  have hylt : (q.elim id id).val < a 0 * (c 0 * d 0) :=
    lt_of_lt_of_eq (q.elim id id).isLt hN.symm
  obtain ⟨x, hxQ, hxR⟩ := exists_row_label a b c d 0 hb0 hc0 hd0 _ hylt
  obtain ⟨J, hJ⟩ : ∃ J, J = pforEquiv a b d 1 q := ⟨_, rfl⟩
  have hval : Ktilde a b c d hC1 (ksWitness a b c d) 0 x J = 1 := by
    rw [ktilde_zero_apply, hJ, Equiv.symm_apply_apply, kbar_zero_witness a b c d hC1 hb0 hc0 hd0]
    simp [hxQ, hxR]
  have hlab : x.val / (b 0 * d 0) = J.val / (2 * c 0 * d 0) ∧ x.val % d 0 = J.val % d 0 := by
    by_contra hcon
    have hor : x.val / (b 0 * d 0) ≠
          ((aDouble (chain_c1_at a b c d hC1 0)).symm J).val / (2 * c 0 * d 0) ∨
        x.val % d 0 ≠ ((aDouble (chain_c1_at a b c d hC1 0)).symm J).val % d 0 := by
      rw [aDouble_symm_apply_val]
      exact not_and_or.mp hcon
    have h0 := hKS x ((aDouble (chain_c1_at a b c d hC1 0)).symm J) hor
    simp only [Matrix.submatrix_apply, Equiv.refl_apply, Equiv.apply_symm_apply] at h0
    rw [hval] at h0
    exact one_ne_zero h0
  have hJval : J.val = rho (b 1) (d 1) (a 1 * (b 1 * d 1)) n := by
    have h := (rhoEquiv_apply_eq_iff (a 1) (b 1) (d 1) hb1 hd1 J
      (sumToFinEquiv _ q)).mp (by rw [hJ]; rfl)
    rw [h, hq]
  have hrho : rho (b 1) (d 1) (a 0 * (c 0 * d 0)) n = J.val := by
    rw [hJval, hN]
  have hdN : d 0 ∣ a 0 * (c 0 * d 0) := ⟨a 0 * c 0, by ring⟩
  have e1 : J.val / (2 * c 0 * d 0) = n % (a 0 * (c 0 * d 0)) / (c 0 * d 0) := by
    rw [← hlab.1, hxQ, hyn]
  have e2 : J.val % d 0 = n % d 0 := by
    rw [← hlab.2, hxR, hyn, Nat.mod_mod_of_dvd n hdN]
  change (rho (b 1) (d 1) (a 0 * (c 0 * d 0)) n / (2 * c 0 * d 0),
    rho (b 1) (d 1) (a 0 * (c 0 * d 0)) n % d 0) =
    (n % (a 0 * (c 0 * d 0)) / (c 0 * d 0), n % d 0)
  rw [hrho, e1, e2]
