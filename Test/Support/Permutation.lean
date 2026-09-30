import Test.Definitions

/-!
# `Pperm`'s technical properties

Supporting facts about `Pperm`/`SG` (`Test.Definitions`) needed to assemble Lemma 3
(`Test.Paper.Lemma3`) and the final telescoping construction (`Test.Support.ChainAssembly`):
`Pperm_apply` gives `Pperm`'s entries explicitly, `Pperm_orthogonal` shows it is a genuine
permutation matrix, and `SG_transpose` shows `S_π`'s support is (up to swapping `b` and `c`)
symmetric under transposition. None of this is stated as such in the paper — it is the
bookkeeping needed to reuse `Pperm` freely once it has been built.
-/

open Matrix

variable {A B C D : Type*} [DecidableEq A] [Fintype A] [DecidableEq B] [Fintype B]
  [DecidableEq C] [DecidableEq D] [Fintype D] {R : Type*} [CommSemiring R]

omit [Fintype A] [Fintype B] [DecidableEq C] [Fintype D] in
/-- `Pperm`'s entries directly in terms of `groupEquiv`'s formula `(ε, x, y, z) ↦ (x, (ε, y),
z)`: this is the same computation as in the proof of `Pperm_mul_repeatFst`, isolated so it can
also be used to show `Pperm` is a genuine permutation matrix (`Pperm_orthogonal`). -/
theorem Pperm_apply (i : A × (Bool × B) × D) (k : Bool × A × B × D) :
    (Pperm : Matrix (A × (Bool × B) × D) (Bool × A × B × D) R) i k =
      if k = (i.2.1.1, i.1, i.2.1.2, i.2.2) then 1 else 0 := by
  simp only [Pperm, commutationMatrix, Matrix.of_apply, Prod.swap_prod_mk]
  rcases eq_or_ne (i.1, i.2.1.1) (k.2.1, k.1) with h | h
  · rcases eq_or_ne i.2.1.2 k.2.2.1 with hy | hy
    · rcases eq_or_ne i.2.2 k.2.2.2 with h2 | h2
      · have hk : k = (i.2.1.1, i.1, i.2.1.2, i.2.2) := by
          obtain ⟨h1, h1'⟩ := Prod.mk.injEq .. |>.mp h
          have base : k = (k.1, k.2.1, k.2.2.1, k.2.2.2) := rfl
          rw [← h1', ← h1, ← hy, ← h2] at base
          exact base
        simp [hk]
      · have hk : k ≠ (i.2.1.1, i.1, i.2.1.2, i.2.2) := fun hk => h2 (by rw [hk])
        simp [hk, h2]
    · have hk : k ≠ (i.2.1.1, i.1, i.2.1.2, i.2.2) := fun hk => hy (by rw [hk])
      simp [hk, hy]
  · have hk : k ≠ (i.2.1.1, i.1, i.2.1.2, i.2.2) := fun hk => h (by rw [hk])
    simp [hk, h]

omit [DecidableEq C] in
/-- **`Pperm` is a genuine permutation matrix**: `Ppermᵀ * Pperm = 1`. This is the fact that
lets the "telescoping" construction of the new Kronecker-sparse factors `K̃_ℓ` cancel adjacent
`Pᵀ · P` pairs. -/
theorem Pperm_orthogonal :
    (Pperm : Matrix (A × (Bool × B) × D) (Bool × A × B × D) R)ᵀ * Pperm =
      (1 : Matrix (Bool × A × B × D) (Bool × A × B × D) R) := by
  ext k k'
  set i₀ : A × (Bool × B) × D := (k.2.1, (k.1, k.2.2.1), k.2.2.2) with hi₀def
  have hi₀ : (i₀.2.1.1, i₀.1, i₀.2.1.2, i₀.2.2) = k := rfl
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  rw [Finset.sum_eq_single i₀]
  · rw [Pperm_apply i₀ k, Pperm_apply i₀ k', hi₀]
    simp only [ite_true, one_mul, Matrix.one_apply]
    by_cases hkk : k' = k
    · simp [hkk]
    · simp [hkk, Ne.symm hkk]
  · intro i _ hine
    by_contra hcontra
    apply hine
    have hne0 : (Pperm : Matrix (A × (Bool × B) × D) (Bool × A × B × D) R) i k ≠ 0 :=
      fun h0 => hcontra (by rw [h0, zero_mul])
    rw [Pperm_apply i k] at hne0
    have hkform : k = (i.2.1.1, i.1, i.2.1.2, i.2.2) := by
      by_contra hne
      exact hne0 (by simp [hne])
    have e1 : i.2.1.1 = k.1 := by rw [hkform]
    have e2 : i.1 = k.2.1 := by rw [hkform]
    have e3 : i.2.1.2 = k.2.2.1 := by rw [hkform]
    have e4 : i.2.2 = k.2.2.2 := by rw [hkform]
    rw [hi₀def]
    have base : i = (i.1, (i.2.1.1, i.2.1.2), i.2.2) := rfl
    rw [e1, e2, e3, e4] at base
    exact base
  · exact fun h => absurd (Finset.mem_univ _) h

omit [Fintype A] [DecidableEq B] [Fintype B] [DecidableEq C] [Fintype D] in
/-- `S_π` only depends on the `(a, d)`-coordinates, so it is (up to swapping `b` and `c`)
symmetric under transposition: `S_(a,b,c,d)ᵀ = S_(a,c,b,d)`. This is what lets Lemma 2's
*row*-doubling statement also give a *column*-doubling one for free (Lemma 3's use of Lemma 2
"on the other side"). -/
theorem SG_transpose :
    (SG : Matrix (A × B × D) (A × C × D) R)ᵀ = (SG : Matrix (A × C × D) (A × B × D) R) := by
  ext i j
  simp only [Matrix.transpose_apply, SG, Matrix.of_apply, eq_comm (a := j.1), eq_comm (a := j.2.2)]
