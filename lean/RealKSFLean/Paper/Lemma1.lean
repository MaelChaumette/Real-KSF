import RealKSFLean.Definitions

/-!
# Lemma 1: the permutation `P_π` doubles the `b` slot of a Kronecker-sparse pattern

Given a pattern `π = (a, b, c, d)`, Section III-C stacks two copies of the support `S_π` on top
of each other and shows (**Lemma 1**) that the permutation `P_π := C_{a,2} ⊗ I_{bd}` of
equation (7) regroups the stack into the support `S_π̄` of the *doubled* pattern
`π̄ = (a, 2b, c, d)` (see Fig. 1 of the letter).

As in `RealKSFLean.Paper.Equation8`, we represent the doubled index set `⟦1, 2b⟧` by `Bool × B`
rather than by `Fin (2b)` (dropping the never-used trivial `Fin 1` factor of `1_{2×1}`), and
`P_π` is built *directly from the commutation matrix* of Definition 2, exactly as in the paper's
construction `P_π := C_{a,2} ⊗ I_{bd}` (equation (7)): `Pperm` acts by the commutation matrix
`commutationMatrix A Bool R` (i.e. `C_{a,2}`) on the `(a, ε)` coordinates, and by the identity
elsewhere. Lemma 1 is then proved by the *same* single-nonzero-term computation as equation (8),
generalized to carry the extra untouched `(b, d)` coordinates along for the ride (this is the
mixed-product step of the paper's proof).
-/

open Matrix

variable {A B C D : Type*} [DecidableEq A] [Fintype A] [DecidableEq B] [Fintype B]
  [DecidableEq C] [DecidableEq D] [Fintype D] {R : Type*} [CommSemiring R]

omit [DecidableEq C] in
/-- **Lemma 1.** `P_π · [S_π ; S_π] = S_π̄`: applying `Pperm` to the two stacked copies of `S_π`
(`repeatFst (SG A B C D)`, the analogue of `1_{2×1} ⊗ S_π`) yields exactly the support `S_π̄` of
the doubled pattern `π̄ = (a, 2b, c, d)`. -/
theorem Pperm_mul_repeatFst :
    (Pperm : Matrix (A × (Bool × B) × D) (Bool × A × B × D) R) *
        repeatFst (p := Bool) (SG : Matrix (A × B × D) (A × C × D) R) =
      (SG : Matrix (A × (Bool × B) × D) (A × C × D) R) := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (i.2.1.1, i.1, i.2.1.2, i.2.2)]
  · simp [Pperm, repeatFst, SG, commutationMatrix]
  · rintro ⟨ε, x, y, z⟩ - hk
    have hz : (Pperm : Matrix (A × (Bool × B) × D) (Bool × A × B × D) R) i (ε, x, y, z) = 0 := by
      simp only [Pperm, commutationMatrix, Matrix.of_apply, Prod.swap_prod_mk]
      rcases eq_or_ne (i.1, i.2.1.1) (x, ε) with h | h
      · rcases eq_or_ne i.2.1.2 y with hy | hy
        · rcases eq_or_ne i.2.2 z with h2 | h2
          · exact absurd (by simp_all [Prod.ext_iff]) hk
          · simp [h2]
        · simp [hy]
      · simp [h]
    rw [hz, zero_mul]
  · exact fun h => absurd (Finset.mem_univ _) h
