import RealKSFLean.Support.ChainAssembly
import RealKSFLean.Paper.Proposition1

/-!
# Kronecker-sparsity of the permuted factors `K̃_ℓ`

This file shows that each `K̃_ℓ` (`Ktilde`, `RealKSFLean.Definitions`) is *genuinely*
Kronecker-sparse, for the "doubled" chain `(a_ℓ, 2 b_ℓ, 2 c_ℓ, d_ℓ)` (interior factors) or
`(a_0, b_0, 2 c_0, d_0)` (the very first factor, which has no row-side permutation to undo).
`RealKSFLean.Paper.Corollary1` packages the results proved here (`ktilde_zero_ksparse`,
`ktilde_succ_ksparse`) into the paper-facing, product-typed statement (`IsKSparse`).

The proof computes `Ktilde ℓ I J` directly: `Pfor`'s two sandwich permutations each collapse a
`Finset.sum` to a single term (they are `{0,1}`-valued with a single nonzero entry per row,
`PpermF_apply`), landing on a single entry of `Kbar`, itself a `±Re/Im` block of the original
factor `K_orig`. Two label-matching facts control when this collapses to zero:

* **the row side** (`row_label_eq`) is *unconditional* pure combinatorics (`Prop1.rho`'s own
  formula only permutes the `b`/`ε` slot, leaving the `a`, `d` slots untouched) — this is
  Lemma 2's content, needing no chainability hypothesis;
* **the column side** (`column_label_eq`) genuinely needs the junction to be chainable
  (`Chainable2`, via `Prop1.chainable_condition10`), since it identifies *two different*
  chains' flat index sets and only chainability (C1 ∧ C2 ∧ C3) guarantees this identification
  respects the `(a, d)`-grouping.

This is an alternative, more direct route to the same fact `RealKSFLean.Support.Assembly` targets
(`matrix_iff_C2_C3`, via Lemma 3): it does not use Lemma 3 at all, computing entries by hand
instead.
-/

open Matrix Prop1

/-- **Lemma 2's pointwise content, made explicit.** If `PpermF a b d` connects `I` to `p` (i.e.
`Pfor`'s entry there is nonzero), then `I`'s `(a, d)`-label in the *doubled* chain `(a, 2b, d)`
exactly equals `p`'s own `(a, d)`-label (regardless of which side of the stack, `inl`/`inr`, `p`
is on) in the *original* chain `(a, b, d)`. Unconditional: no chainability needed, since `rho`
only ever touches the `b`/`ε` slot. -/
theorem row_label_eq (a b d : ℕ) (hb : 0 < b) (hd0 : 0 < d)
    (I : Fin (a * (2 * b * d))) (p : Fin (a * (b * d)) ⊕ Fin (a * (b * d)))
    (hp : (PpermF a b d : Matrix _ _ ℝ) I (sumToFinEquiv (a * (b * d)) p) ≠ 0) :
    I.val / (2 * (b * d)) = (p.elim id id).val / (b * d) ∧
      I.val % d = (p.elim id id).val % d := by
  rw [PpermF_apply a b d hb hd0] at hp
  have hI : I.val = Prop1.rho b d (a * (b * d)) (sumToFinEquiv (a * (b * d)) p).val := by
    by_contra h
    simp [h] at hp
  have hbd0 : 0 < b * d := by positivity
  have h2bd0 : 0 < 2 * (b * d) := by positivity
  have final : ∀ (x : Fin (a * (b * d))) (ε : ℕ), ε ≤ 1 →
      I.val = 2 * (b * d) * (x.val / (b * d)) + (b * d * ε + x.val % (b * d)) →
      I.val / (2 * (b * d)) = x.val / (b * d) ∧ I.val % d = x.val % d := by
    intro x ε hε hI'
    have hrlt : b * d * ε + x.val % (b * d) < 2 * (b * d) := by
      have h1 := Nat.mod_lt x.val hbd0
      have h2 : b * d * ε ≤ b * d := by
        calc b * d * ε ≤ b * d * 1 := Nat.mul_le_mul_left (b * d) hε
          _ = b * d := Nat.mul_one _
      omega
    refine ⟨?_, ?_⟩
    · rw [hI', Nat.add_comm (2 * (b * d) * (x.val / (b * d))),
        Nat.add_mul_div_left _ _ h2bd0, Nat.div_eq_of_lt hrlt, Nat.zero_add]
    · rw [hI']
      have hrw : 2 * (b * d) * (x.val / (b * d)) + (b * d * ε + x.val % (b * d)) =
          x.val % (b * d) + d * (2 * (b * (x.val / (b * d))) + b * ε) := by ring
      rw [hrw, Nat.add_mul_mod_self_left, Nat.mod_mod_of_dvd x.val (dvd_mul_left d b)]
  rcases p with x | x <;>
    simp only [Sum.elim_inl, Sum.elim_inr, id_eq] at *
  · rw [sumToFinEquiv_apply_inl_val] at hI
    unfold Prop1.rho at hI
    rw [Nat.mod_eq_of_lt x.isLt, Nat.div_eq_of_lt x.isLt, Nat.mul_zero, Nat.add_zero] at hI
    exact final x 0 (by norm_num) (by rw [hI]; ring)
  · have hN0 : 0 < a * (b * d) := by have := x.isLt; omega
    rw [sumToFinEquiv_apply_inr_val] at hI
    unfold Prop1.rho at hI
    have e1 : (a * (b * d) + x.val) % (a * (b * d)) = x.val := by
      rw [Nat.add_mod_left]; exact Nat.mod_eq_of_lt x.isLt
    have e2 : (a * (b * d) + x.val) / (a * (b * d)) = 1 := by
      rw [Nat.add_div_left _ hN0, Nat.div_eq_of_lt x.isLt]
    have e3 : (a * (b * d) + x.val) % (b * d) = x.val % (b * d) := by
      rw [show a * (b * d) + x.val = x.val + (b * d) * a from by ring, Nat.add_mul_mod_self_left]
    rw [e1, e2, e3] at hI
    exact final x 1 (by norm_num) (by rw [hI]; ring)

/-- **Auxiliary: `n % N' = q`'s own underlying value**, for `q` sitting on either side of the
stack `Fin N' ⊕ Fin N'` fed through `sumToFinEquiv`. Purely the combinatorics of
`sumToFinEquiv`, no chainability needed — isolated since both `column_label_eq` and its proof
of `n < 2 * N'` need it. -/
theorem sumToFinEquiv_mod_self (N' : ℕ) (q : Fin N' ⊕ Fin N') :
    (sumToFinEquiv N' q).val % N' = (q.elim id id).val ∧ (sumToFinEquiv N' q).val < 2 * N' := by
  rcases q with y | y <;> simp only [Sum.elim_inl, Sum.elim_inr, id_eq]
  · rw [sumToFinEquiv_apply_inl_val, Nat.mod_eq_of_lt y.isLt]
    exact ⟨rfl, by have := y.isLt; omega⟩
  · rw [sumToFinEquiv_apply_inr_val, Nat.add_mod_left, Nat.mod_eq_of_lt y.isLt]
    exact ⟨rfl, by have := y.isLt; omega⟩

/-- **Proposition 1's pointwise content, made explicit for the junction.** If chain `(a, c, d)`
and chain `(a', b', d')` are connected by `Condition10` (in particular, if they come from a
`Chainable2` junction, via `Prop1.chainable_condition10`), and `PpermF a' b' d'` connects `J` to
`q`, then `J`'s `(a, d)`-label in the "doubled-`c`" chain `(a, 2c, d)` exactly equals `q`'s own
`(a, d)`-label in the *original* chain `(a, c, d)`. This is where chainability is genuinely
used: unlike the row side, this identifies *two different* chains' flat index sets, and only
`Condition10` (hence C1 ∧ C2 ∧ C3) guarantees the identification respects the grouping. -/
theorem column_label_eq (c d b' d' a a' : ℕ) (hb' : 0 < b') (hd'0 : 0 < d')
    (hC1 : a * (c * d) = a' * (b' * d')) (hCond : Condition10 c d b' d' (a * (c * d)))
    (J : Fin (a' * (2 * b' * d'))) (q : Fin (a' * (b' * d')) ⊕ Fin (a' * (b' * d')))
    (hq : (PpermF a' b' d' : Matrix _ _ ℝ) J (sumToFinEquiv (a' * (b' * d')) q) ≠ 0) :
    J.val / (2 * c * d) = (q.elim id id).val / (c * d) ∧
      J.val % d = (q.elim id id).val % d := by
  rw [PpermF_apply a' b' d' hb' hd'0] at hq
  have hJ : J.val = Prop1.rho b' d' (a' * (b' * d')) (sumToFinEquiv (a' * (b' * d')) q).val := by
    by_contra h
    simp [h] at hq
  set n := (sumToFinEquiv (a' * (b' * d')) q).val with hn
  obtain ⟨hnmod, hnlt⟩ := sumToFinEquiv_mod_self (a' * (b' * d')) q
  rw [← hn] at hnmod hnlt
  have hnlt' : n < 2 * (a * (c * d)) := by rw [hC1]; exact hnlt
  have hrho_eq : Prop1.rho b' d' (a * (c * d)) n = Prop1.rho b' d' (a' * (b' * d')) n :=
    congrArg (fun N => Prop1.rho b' d' N n) hC1
  have hlabel := hCond n hnlt'
  rw [Prop1.label2, Prop1.label1, hrho_eq, ← hJ] at hlabel
  rw [hC1, hnmod] at hlabel
  obtain ⟨hl1, hl2⟩ := Prod.mk.injEq .. |>.mp hlabel
  refine ⟨hl1, hl2.trans ?_⟩
  have hdvd : d ∣ a' * (b' * d') := hC1 ▸ (⟨a * c, by ring⟩ : d ∣ a * (c * d))
  rw [← hnmod, Nat.mod_mod_of_dvd n hdvd]

variable (a b c d : ℕ → ℕ)
variable (hchain : ∀ k, Chainable2 (a k) (c k) (d k) (a (k + 1)) (b (k + 1)) (d (k + 1)))
variable (K_orig : (k : ℕ) → Matrix (Fin (a k) × Fin (b k) × Fin (d k))
  (Fin (a k) × Fin (c k) × Fin (d k)) ℂ)

/-- `Chainable2.c1` at junction `j` (between chain `j`'s output and chain `j + 1`'s input),
parenthesized the way `aDouble`/`colCastEquiv` need it (`a * (c * d) = a' * (b' * d')` rather
than `a * c * d = a' * b' * d'`). -/
theorem chain_c1_at
    (hchain : ∀ k, Chainable2 (a k) (c k) (d k) (a (k + 1)) (b (k + 1)) (d (k + 1))) (j : ℕ) :
    a j * (c j * d j) = a (j + 1) * (b (j + 1) * d (j + 1)) := by
  have h := (hchain j).c1
  unfold Prop1.C1 at h
  rw [← mul_assoc, h, mul_assoc]

/-- **`Kflat k` inherits `K_orig k`'s sparsity**, viewed flatly and with its column space
recast to chain `k`'s own `(a, c, d)`-grouping via `(colCastEquiv k)`: this is just `K_orig k`
reindexed by the value-preserving identifications `finChainEquiv`/`colCastEquiv`, so `IsKSparse`
transports unchanged. -/
theorem kflat_ksparseFlat (k : ℕ) (hb : 0 < b k) (hc : 0 < c k) (hd0 : 0 < d k)
    (hKorig : IsKSparse (a k) (b k) (c k) (d k) (K_orig k)) :
    IsKSparseFlat (a k) (b k) (c k) (d k)
      (Matrix.submatrix (Kflat a b c d hchain K_orig k) (Equiv.refl _)
        (colCastEquiv a b c d hchain k)) := by
  have heq : Matrix.submatrix (Kflat a b c d hchain K_orig k) (Equiv.refl _)
      (colCastEquiv a b c d hchain k) =
      Matrix.submatrix (K_orig k) (finChainEquiv (a k) (b k) (d k)).symm
        (finChainEquiv (a k) (c k) (d k)).symm := by
    ext i j
    have step : ((finChainEquiv (a k) (c k) (d k)).trans (colCastEquiv a b c d hchain k)).symm
        (colCastEquiv a b c d hchain k j) = (finChainEquiv (a k) (c k) (d k)).symm j := by
      rw [Equiv.symm_apply_eq, Equiv.trans_apply, Equiv.apply_symm_apply]
    simp only [Matrix.submatrix_apply, Equiv.refl_apply, Kflat, step]
  rw [heq, ← isKSparse_submatrix_finChainEquiv_iff (a k) (b k) (c k) (d k) hb hc hd0]
  have hcancel : Matrix.submatrix
      (Matrix.submatrix (K_orig k) (finChainEquiv (a k) (b k) (d k)).symm
        (finChainEquiv (a k) (c k) (d k)).symm)
      (finChainEquiv (a k) (b k) (d k)) (finChainEquiv (a k) (c k) (d k)) = K_orig k := by
    ext x y
    simp [Matrix.submatrix_apply]
  rwa [hcancel]

/-- `Kbar`'s value at `(p, q)` is, up to sign, `Re` or `Im` of `Kflat (k+1)` at `p`'s and `q`'s
own underlying (non-doubled) indices — so it vanishes whenever that underlying entry does. -/
theorem kbar_succ_zero_of_kflat_zero (k : ℕ) (p : Jfam a b d (k + 1) ⊕ Jfam a b d (k + 1))
    (q : Jfam a b d (k + 2) ⊕ Jfam a b d (k + 2))
    (hz : Kflat a b c d hchain K_orig (k + 1) (p.elim id id) (q.elim id id) = 0) :
    Kbar (Kflat a b c d hchain K_orig) (k + 1) p q = 0 := by
  have hKbar : Kbar (Kflat a b c d hchain K_orig) (k + 1) =
      Matrix.fromBlocks ((Kflat a b c d hchain K_orig (k + 1)).map Complex.re)
        ((Kflat a b c d hchain K_orig (k + 1)).map Complex.im)
        (-(Kflat a b c d hchain K_orig (k + 1)).map Complex.im)
        ((Kflat a b c d hchain K_orig (k + 1)).map Complex.re) := rfl
  rw [hKbar]
  rcases p with p | p <;> rcases q with q | q <;>
    simp only [Sum.elim_inl, Sum.elim_inr, id_eq] at hz <;>
    simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.map_apply, hz]

set_option maxHeartbeats 800000 in
-- the nested Finset.sum_eq_zero / row and column label collapsing below is elaboration-heavy
/-- **`K̃_{k+1}` is genuinely Kronecker-sparse**, for the doubled chain
`(a_{k+1}, 2 b_{k+1}, 2 c_{k+1}, d_{k+1})`. Combines `row_label_eq` (unconditional) on the left
sandwich with `column_label_eq` (via `Chainable2 → Condition10`) on the right sandwich, plus
`kflat_ksparseFlat` for the underlying entry. -/
theorem ktilde_succ_ksparse (k : ℕ) (ha1 : 0 < a (k + 1)) (ha2 : 0 < a (k + 2))
    (hb1 : 0 < b (k + 1)) (hc1 : 0 < c (k + 1)) (hd1 : 0 < d (k + 1)) (hb2 : 0 < b (k + 2))
    (hd2 : 0 < d (k + 2))
    (hKorig : IsKSparse (a (k + 1)) (b (k + 1)) (c (k + 1)) (d (k + 1)) (K_orig (k + 1))) :
    IsKSparseFlat (a (k + 1)) (2 * b (k + 1)) (2 * c (k + 1)) (d (k + 1))
      (Matrix.submatrix (Ktilde a b c d hchain K_orig (k + 1)) (Equiv.refl _)
        (aDouble (chain_c1_at a b c d hchain (k + 1)))) := by
  intro I J' hIJ
  have hJval : (aDouble (chain_c1_at a b c d hchain (k + 1)) J').val = J'.val :=
    natCastEquiv_apply_val _ J'
  change Ktilde a b c d hchain K_orig (k + 1) I
    (aDouble (chain_c1_at a b c d hchain (k + 1)) J') = 0
  set J := aDouble (chain_c1_at a b c d hchain (k + 1)) J' with hJdef
  have hK : Ktilde a b c d hchain K_orig (k + 1) =
      Pfor a b d (k + 1) * Kbar (Kflat a b c d hchain K_orig) (k + 1) *
        (Pfor a b d (k + 2))ᵀ := rfl
  rw [hK, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro q _
  rw [Matrix.transpose_apply]
  by_cases hq0 : (Pfor a b d (k + 2)) J q = 0
  · rw [hq0, mul_zero]
  · have hPq : (PpermF (a (k + 2)) (b (k + 2)) (d (k + 2)) : Matrix _ _ ℝ) J
        (sumToFinEquiv (a (k + 2) * (b (k + 2) * d (k + 2))) q) ≠ 0 := hq0
    have hCond : Condition10 (c (k + 1)) (d (k + 1)) (b (k + 2)) (d (k + 2))
        (a (k + 1) * (c (k + 1) * d (k + 1))) := by
      rw [← mul_assoc]
      exact Prop1.chainable_condition10 (a (k + 1)) (c (k + 1)) (d (k + 1)) (a (k + 2))
        (b (k + 2)) (d (k + 2)) ha1 ha2 hc1 hd1 hb2 hd2 (hchain (k + 1))
    obtain ⟨hcol1, hcol2⟩ := column_label_eq (c (k + 1)) (d (k + 1)) (b (k + 2)) (d (k + 2))
      (a (k + 1)) (a (k + 2)) hb2 hd2 (chain_c1_at a b c d hchain (k + 1)) hCond J q hPq
    rw [hJval] at hcol1 hcol2
    have hzero : (Pfor a b d (k + 1) * Kbar (Kflat a b c d hchain K_orig) (k + 1)) I q = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro p _
      by_cases hp0 : Pfor a b d (k + 1) I p = 0
      · rw [hp0, zero_mul]
      · have hPp : (PpermF (a (k + 1)) (b (k + 1)) (d (k + 1)) : Matrix _ _ ℝ) I
            (sumToFinEquiv (a (k + 1) * (b (k + 1) * d (k + 1))) p) ≠ 0 := hp0
        obtain ⟨hrow1, hrow2⟩ := row_label_eq (a (k + 1)) (b (k + 1)) (d (k + 1)) hb1 hd1 I p hPp
        have hkflat := kflat_ksparseFlat a b c d hchain K_orig (k + 1) hb1 hc1 hd1 hKorig
          (p.elim id id) ((colCastEquiv a b c d hchain (k + 1)).symm (q.elim id id))
        simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply,
          colCastEquiv_symm_apply_val] at hkflat
        have hmismatch : (p.elim id id).val / (b (k + 1) * d (k + 1)) ≠
              (q.elim id id).val / (c (k + 1) * d (k + 1)) ∨
            (p.elim id id).val % d (k + 1) ≠ (q.elim id id).val % d (k + 1) := by
          rcases hIJ with h | h
          · left
            rw [← hrow1, ← hcol1,
              show (2 : ℕ) * (b (k + 1) * d (k + 1)) = 2 * b (k + 1) * d (k + 1) from by ring]
            exact h
          · right; rw [← hrow2, ← hcol2]; exact h
        have hz := hkflat hmismatch
        rw [kbar_succ_zero_of_kflat_zero a b c d hchain K_orig k p q hz, mul_zero]
    change (Pfor a b d (k + 1) * Kbar (Kflat a b c d hchain K_orig) (k + 1)) I q * _ = 0
    rw [hzero, zero_mul]

/-- `Kbar (Kflat ...) 0`'s value at `(i, q)` is `Re` or `Im` of `Kflat 0` at `i` and `q`'s own
underlying index — the `k = 0` analogue of `kbar_succ_zero_of_kflat_zero`, using `fromCols`
(no row-side doubling for the very first factor) instead of `fromBlocks`. -/
theorem kbar_zero_zero_of_kflat_zero (i : Jfam a b d 0) (q : Jfam a b d 1 ⊕ Jfam a b d 1)
    (hz : Kflat a b c d hchain K_orig 0 i (q.elim id id) = 0) :
    Kbar (Kflat a b c d hchain K_orig) 0 i q = 0 := by
  have hKbar : Kbar (Kflat a b c d hchain K_orig) 0 =
      fromCols ((Kflat a b c d hchain K_orig 0).map Complex.re)
        ((Kflat a b c d hchain K_orig 0).map Complex.im) := rfl
  rw [hKbar]
  rcases q with q | q <;> simp only [Sum.elim_inl, Sum.elim_inr, id_eq] at hz <;>
    simp [Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Matrix.map_apply, hz]

set_option maxHeartbeats 400000 in
-- the Finset.sum_eq_zero / column label collapsing below is elaboration-heavy
/-- **`K̃_0` is genuinely Kronecker-sparse**, for the chain `(a_0, b_0, 2 c_0, d_0)` — no
row-side doubling, since the very first factor `K̄_0 = [Re K_0 | Im K_0]` has no permutation on
its input. Only the column side (`column_label_eq`, via `Chainable2 → Condition10`) is needed. -/
theorem ktilde_zero_ksparse (ha0 : 0 < a 0) (ha1 : 0 < a 1) (hb0 : 0 < b 0) (hc0 : 0 < c 0)
    (hd00 : 0 < d 0) (hb1 : 0 < b 1) (hd1 : 0 < d 1)
    (hKorig : IsKSparse (a 0) (b 0) (c 0) (d 0) (K_orig 0)) :
    IsKSparseFlat (a 0) (b 0) (2 * c 0) (d 0)
      (Matrix.submatrix (Ktilde a b c d hchain K_orig 0) (Equiv.refl _)
        (aDouble (chain_c1_at a b c d hchain 0))) := by
  intro I J' hIJ
  have hJval : (aDouble (chain_c1_at a b c d hchain 0) J').val = J'.val :=
    natCastEquiv_apply_val _ J'
  change Ktilde a b c d hchain K_orig 0 I (aDouble (chain_c1_at a b c d hchain 0) J') = 0
  set J := aDouble (chain_c1_at a b c d hchain 0) J' with hJdef
  have hK : Ktilde a b c d hchain K_orig 0 =
      Kbar (Kflat a b c d hchain K_orig) 0 * (Pfor a b d 1)ᵀ := rfl
  rw [hK, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro q _
  rw [Matrix.transpose_apply]
  by_cases hq0 : Pfor a b d 1 J q = 0
  · rw [hq0, mul_zero]
  · have hPq : (PpermF (a 1) (b 1) (d 1) : Matrix _ _ ℝ) J
        (sumToFinEquiv (a 1 * (b 1 * d 1)) q) ≠ 0 := hq0
    have hCond : Condition10 (c 0) (d 0) (b 1) (d 1) (a 0 * (c 0 * d 0)) := by
      rw [← mul_assoc]
      exact Prop1.chainable_condition10 (a 0) (c 0) (d 0) (a 1) (b 1) (d 1)
        ha0 ha1 hc0 hd00 hb1 hd1 (hchain 0)
    obtain ⟨hcol1, hcol2⟩ := column_label_eq (c 0) (d 0) (b 1) (d 1) (a 0) (a 1) hb1 hd1
      (chain_c1_at a b c d hchain 0) hCond J q hPq
    rw [hJval] at hcol1 hcol2
    have hkflat := kflat_ksparseFlat a b c d hchain K_orig 0 hb0 hc0 hd00 hKorig
      I ((colCastEquiv a b c d hchain 0).symm (q.elim id id))
    simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply,
      colCastEquiv_symm_apply_val] at hkflat
    have hmismatch : I.val / (b 0 * d 0) ≠ (q.elim id id).val / (c 0 * d 0) ∨
        I.val % d 0 ≠ (q.elim id id).val % d 0 := by
      rcases hIJ with h | h
      · left; rwa [hcol1] at h
      · right; rwa [hcol2] at h
    rw [kbar_zero_zero_of_kflat_zero a b c d hchain K_orig I q (hkflat hmismatch), zero_mul]
