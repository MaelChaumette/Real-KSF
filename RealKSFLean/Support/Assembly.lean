import RealKSFLean.Support.FlatChain
import RealKSFLean.Paper.Proposition1

/-!
# `Condition10` as a matrix equation

This file connects `Prop1.Condition10`'s arithmetic (`RealKSFLean.Paper.Proposition1`) to an actual
*matrix* equation built from `PpermF`/`SF`/`repeatFstFlat` (`RealKSFLean.Definitions`), using the
equivalence `rhoEquiv` underlying `PpermF`: `matrix_of_condition10` shows `Condition10` is
exactly the entrywise content of `P_{π'} · [S_{(a,c,β,d)} ; S_{(a,c,β,d)}] = S_{(a,2c,β,d)}`
(equation (10)), and `matrix_iff_C2_C3` combines this with Proposition 1 to characterize when
`K̃_ℓ := Pℓ · K̄ℓ · Pℓ₊₁ᵀ` has the right support, via Lemma 3
(`RealKSFLean.Paper.Lemma3.lemma3_core`, not repeated here).

This was the first strategy explored for proving the final Kronecker-sparsity of `K̃_ℓ`
(`RealKSFLean.Paper.Corollary1`); the assembly that was actually completed
(`RealKSFLean.Support.ChainSparse`) instead computes `K̃_ℓ`'s entries directly, without going
through `repeatFstFlat`'s "stack of two copies" abstraction. The results here are independent,
mathematically meaningful supporting work — they are simply not on the critical path of the
final proof.
-/

open Matrix Prop1

/-- A value-preserving identification `Fin n ≃ Fin m`, for `n = m`. Unlike `Equiv.cast`, its
`.val` is *definitionally* the identity (`natCastEquiv_apply_val`), which is what lets the
proofs below track flat indices across a `C1`-induced identification without extra rewriting. -/
@[simp] theorem natCastEquiv_apply_val {n m : ℕ} (h : n = m) (i : Fin n) :
    (natCastEquiv h i).val = i.val := rfl

@[simp] theorem natCastEquiv_symm_apply_val {n m : ℕ} (h : n = m) (i : Fin m) :
    ((natCastEquiv h).symm i).val = i.val := rfl

@[simp] theorem castDouble_apply_val {a c d a' b' d' : ℕ} (h : a * (c * d) = a' * (b' * d'))
    (i : Fin (2 * (a * (c * d)))) : (castDouble h i).val = i.val :=
  natCastEquiv_apply_val _ i

@[simp] theorem aDouble_symm_apply_val {a c d a' b' d' : ℕ} (h : a * (c * d) = a' * (b' * d'))
    (i : Fin (a' * (2 * b' * d'))) : ((aDouble h).symm i).val = i.val :=
  natCastEquiv_symm_apply_val _ i

set_option maxHeartbeats 1000000 in
-- Unfolding `PpermF`/`repeatFstFlat`/`SF` down to `Nat.div`/`Nat.mod` (via `rhoEquiv_apply_eq_iff`
-- / `repeatFstFlat_apply` / `SF_apply`) accumulates enough terms that the default heartbeat
-- budget is too tight, even though every step is elementary.
/-- **The missing link.** `Condition10` is exactly the entrywise content of the matrix equation
`P_{π'} · [S_{(a,c,β,d)} ; S_{(a,c,β,d)}] = S_{(a,2c,β,d)}` (equation (10), for an arbitrary
"free" `β` — the already-doubled `b` slot inherited from the real/imaginary-part construction,
which plays no role in the combinatorics). We only need this one direction
(`Condition10 → ` the matrix equation). Stated for a general `CommSemiring R` (not just `ℕ`)
since it can be instantiated at `R = ℝ`; nothing in the proof below actually depends on the
ambient semiring, only on the `{0, 1}`-valued indices, so the exact same argument goes through
unchanged. -/
theorem matrix_of_condition10 {R : Type*} [CommSemiring R] (a c d a' b' d' β : ℕ) (hc : 0 < c)
    (hd0 : 0 < d) (hb' : 0 < b') (hd'0 : 0 < d') (hβ : 0 < β)
    (hC1 : a * (c * d) = a' * (b' * d')) (hCond : Condition10 c d b' d' (a * (c * d))) :
    Matrix.submatrix (PpermF a' b' d' : Matrix _ _ R) id (castDouble hC1) *
        (repeatFstFlat a c β d : Matrix _ _ R) =
      Matrix.submatrix (SF a (2 * c) β d : Matrix _ _ R) (aDouble hC1).symm id := by
  have hbd0 : 0 < b' * d' := by positivity
  have hPeq : ∀ (I : Fin (a' * (2 * b' * d'))) (K : Fin (2 * (a * (c * d)))),
      (PpermF a' b' d' : Matrix _ _ R) I (castDouble hC1 K) =
        if rhoEquiv a' b' d' (castDouble hC1 K) = I then 1 else 0 := by
    intro I K
    rw [PpermF_eq_submatrix_one, Matrix.submatrix_apply, Matrix.one_apply, id]
    exact if_congr eq_comm rfl rfl
  ext I J
  simp only [Matrix.submatrix_apply, id, Matrix.mul_apply]
  set K₀ : Fin (2 * (a * (c * d))) :=
    (castDouble hC1).symm ((rhoEquiv a' b' d').symm I) with hK₀def
  rw [Finset.sum_eq_single K₀]
  · -- terme central
    have hK₀I : rhoEquiv a' b' d' (castDouble hC1 K₀) = I := by
      simp [hK₀def]
    have hI : I.val = Prop1.rho b' d' (a' * (b' * d')) K₀.val := by
      have h := (rhoEquiv_apply_eq_iff a' b' d' hb' hd'0 I (castDouble hC1 K₀)).mp hK₀I
      simpa using h
    have hn0 : K₀.val < 2 * (a * (c * d)) := K₀.isLt
    have step : Prop1.rho b' d' (a' * (b' * d')) K₀.val = Prop1.rho b' d' (a * (c * d)) K₀.val :=
      congrArg (fun N => Prop1.rho b' d' N K₀.val) hC1.symm
    have hIrho : I.val = Prop1.rho b' d' (a * (c * d)) K₀.val := hI.trans step
    have hlabel := hCond K₀.val hn0
    rw [Prop1.label2, Prop1.label1, ← hIrho] at hlabel
    obtain ⟨hlab1, hlab2⟩ := Prod.mk.injEq .. |>.mp hlabel
    rw [hPeq]
    simp only [hK₀I, ite_true, one_mul, repeatFstFlat_apply a c β d hc hβ hd0,
      SF_apply a (2 * c) β d (by positivity) hβ hd0]
    simp only [aDouble_symm_apply_val]
    rw [hlab1, hlab2]
  · intro K _ hK
    have hne : rhoEquiv a' b' d' (castDouble hC1 K) ≠ I := by
      intro h
      apply hK
      apply (castDouble hC1).injective
      rw [hK₀def, Equiv.apply_symm_apply, ← h, Equiv.symm_apply_apply]
    rw [hPeq]
    have hne' : ¬rhoEquiv a' b' d' (castDouble hC1 K) = I := hne
    simp only [hne', ite_false, zero_mul]
  · exact fun h => absurd (Finset.mem_univ _) h

set_option maxHeartbeats 1000000 in
-- Same reason as `matrix_of_condition10`: several `set`-introduced local definitions
-- accumulate, slowing `positivity`/`simp` below the default heartbeat budget.
/-- **The converse of `matrix_of_condition10`**: the matrix equation also implies `Condition10`,
making the connection to the arithmetic world of Proposition 1 a genuine "if and only if",
matching Proposition 1's own "necessary and sufficient" character. -/
theorem condition10_of_matrix (a c d a' b' d' β : ℕ) (ha : 0 < a) (hc : 0 < c) (hd0 : 0 < d)
    (hb' : 0 < b') (hd'0 : 0 < d') (hβ : 0 < β) (hC1 : a * (c * d) = a' * (b' * d'))
    (hmatrix : Matrix.submatrix (PpermF a' b' d' : Matrix _ _ ℕ) id (castDouble hC1) *
        (repeatFstFlat a c β d : Matrix _ _ ℕ) =
      Matrix.submatrix (SF a (2 * c) β d : Matrix _ _ ℕ) (aDouble hC1).symm id) :
    Condition10 c d b' d' (a * (c * d)) := by
  have hbd0 : 0 < b' * d' := by positivity
  have hcd0 : 0 < c * d := by positivity
  have hPeq : ∀ (I : Fin (a' * (2 * b' * d'))) (K : Fin (2 * (a * (c * d)))),
      (PpermF a' b' d' : Matrix _ _ ℕ) I (castDouble hC1 K) =
        if rhoEquiv a' b' d' (castDouble hC1 K) = I then 1 else 0 := by
    intro I K
    rw [PpermF_eq_submatrix_one, Matrix.submatrix_apply, Matrix.one_apply, id]
    exact if_congr eq_comm rfl rfl
  intro n hn
  set K₀ : Fin (2 * (a * (c * d))) := ⟨n, hn⟩ with hK₀def
  set I : Fin (a' * (2 * b' * d')) := rhoEquiv a' b' d' (castDouble hC1 K₀) with hIdef
  set q := (K₀.val % (a * (c * d))) / (c * d) with hqdef
  set r := K₀.val % d with hrdef
  have hqlt : q < a := Nat.div_lt_of_lt_mul (by
    rw [← show a * (c * d) = c * d * a from by ring]
    exact Nat.mod_lt _ (by positivity))
  have hrlt : r < d := Nat.mod_lt _ hd0
  have hdlebd : d ≤ β * d := Nat.le_mul_of_pos_left d hβ
  have hrltbd : r < β * d := lt_of_lt_of_le hrlt hdlebd
  have hJlt : q * (β * d) + r < a * (β * d) := by
    calc q * (β * d) + r < q * (β * d) + β * d := by omega
      _ = (q + 1) * (β * d) := by ring
      _ ≤ a * (β * d) := Nat.mul_le_mul_right (β * d) hqlt
  set J : Fin (a * (β * d)) := ⟨q * (β * d) + r, hJlt⟩ with hJdef
  have hJq : J.val / (β * d) = q := by
    change (q * (β * d) + r) / (β * d) = q
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity : (0:ℕ) < β * d),
      Nat.div_eq_of_lt hrltbd, Nat.zero_add]
  have hJr : J.val % d = r := by
    change (q * (β * d) + r) % d = r
    have hrw : q * (β * d) + r = r + d * (q * β) := by ring
    rw [hrw, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrlt]
  have hLHS1 : repeatFstFlat a c β d K₀ J = 1 := by
    rw [repeatFstFlat_apply a c β d hc hβ hd0, hJq, hJr]
    simp [hqdef, hrdef]
  have hLHS : (Matrix.submatrix (PpermF a' b' d' : Matrix _ _ ℕ) id (castDouble hC1) *
      (repeatFstFlat a c β d : Matrix _ _ ℕ)) I J = 1 := by
    simp only [Matrix.submatrix_apply, id, Matrix.mul_apply]
    rw [Finset.sum_eq_single K₀]
    · rw [hPeq]
      simp only [hIdef, ite_true, one_mul]
      exact hLHS1
    · intro K _ hK
      have hne : rhoEquiv a' b' d' (castDouble hC1 K) ≠ I := by
        intro h
        apply hK
        apply (castDouble hC1).injective
        rw [hIdef] at h
        exact (rhoEquiv a' b' d').injective h
      rw [hPeq]
      have hne' : ¬rhoEquiv a' b' d' (castDouble hC1 K) = I := hne
      simp only [hne', ite_false, zero_mul]
    · exact fun h => absurd (Finset.mem_univ _) h
  rw [hmatrix] at hLHS
  simp only [Matrix.submatrix_apply, id, SF_apply a (2 * c) β d (by positivity) hβ hd0,
    aDouble_symm_apply_val] at hLHS
  rw [hJq, hJr] at hLHS
  by_cases hcase : I.val / (2 * c * d) = q ∧ I.val % d = r
  · have hI : I.val = Prop1.rho b' d' (a' * (b' * d')) K₀.val := by
      have h := (rhoEquiv_apply_eq_iff a' b' d' hb' hd'0 I (castDouble hC1 K₀)).mp (by
        rw [hIdef])
      simpa using h
    have step : Prop1.rho b' d' (a' * (b' * d')) K₀.val = Prop1.rho b' d' (a * (c * d)) K₀.val :=
      congrArg (fun N => Prop1.rho b' d' N K₀.val) hC1.symm
    change Prop1.label2 c d (Prop1.rho b' d' (a * (c * d)) K₀.val) =
      Prop1.label1 c d (a * (c * d)) K₀.val
    rw [← step, ← hI, Prop1.label2, Prop1.label1]
    obtain ⟨e1, e2⟩ := hcase
    rw [e1, e2]
  · exact absurd hLHS (by simp [hcase])

/-- **Equation (10), as a genuine "if and only if" with the matrix world**: combining
`matrix_of_condition10` and its converse `condition10_of_matrix`. -/
theorem matrix_iff_condition10 (a c d a' b' d' β : ℕ) (ha : 0 < a) (hc : 0 < c) (hd0 : 0 < d)
    (hb' : 0 < b') (hd'0 : 0 < d') (hβ : 0 < β) (hC1 : a * (c * d) = a' * (b' * d')) :
    (Matrix.submatrix (PpermF a' b' d' : Matrix _ _ ℕ) id (castDouble hC1) *
        (repeatFstFlat a c β d : Matrix _ _ ℕ) =
      Matrix.submatrix (SF a (2 * c) β d : Matrix _ _ ℕ) (aDouble hC1).symm id) ↔
      Condition10 c d b' d' (a * (c * d)) :=
  ⟨condition10_of_matrix a c d a' b' d' β ha hc hd0 hb' hd'0 hβ hC1,
    matrix_of_condition10 a c d a' b' d' β hc hd0 hb' hd'0 hβ hC1⟩

/-- **The master "if and only if" for a single junction**: the matrix equation (10) — the one
Lemma 3 (`RealKSFLean.Paper.Lemma3.lemma3_core`) shows is equivalent, after transposing, to equation
(7) (the actual condition for `K̃_ℓ := Pℓ · K̄ℓ · Pℓ₊₁ᵀ` to have the Kronecker-sparse support of
the doubled chain) — holds if and only if C2 ∧ C3 (C1 being the standing well-typedness
hypothesis). Chaining through `lemma3_core` (an unconditional matrix identity, not repeated
here) this is exactly

  `K̃_ℓ has the right support ⟺ equation (10) holds ⟺ C1 ∧ C2 ∧ C3`

for one junction of the architecture; Corollary 1
(`Chainable2 → Condition10`, `RealKSFLean.Paper.Corollary1.chainable_condition10`) is the "if"
direction specialized to `Chainable2`. -/
theorem matrix_iff_C2_C3 (a c d a' b' d' β : ℕ) (ha : 0 < a) (ha' : 0 < a') (hc : 0 < c)
    (hd0 : 0 < d) (hb' : 0 < b') (hd'0 : 0 < d') (hβ : 0 < β)
    (hC1 : a * (c * d) = a' * (b' * d')) :
    (Matrix.submatrix (PpermF a' b' d' : Matrix _ _ ℕ) id (castDouble hC1) *
        (repeatFstFlat a c β d : Matrix _ _ ℕ) =
      Matrix.submatrix (SF a (2 * c) β d : Matrix _ _ ℕ) (aDouble hC1).symm id) ↔
      C2 a c d a' b' d' ∧ C3 a a' :=
  (matrix_iff_condition10 a c d a' b' d' β ha hc hd0 hb' hd'0 hβ hC1).trans
    ((mul_assoc a c d ▸ Iff.rfl : Condition10 c d b' d' (a * (c * d)) ↔
        Condition10 c d b' d' (a * c * d)).trans
      (prop1_core a c d a' b' d' ha ha' hc hd0 hb' hd'0 (by rw [mul_assoc, mul_assoc]; exact hC1)))
