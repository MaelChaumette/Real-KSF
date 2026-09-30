import Test.Definitions

/-!
# Lemma 2: the permutation `P_π` doubles the `b` slot of a Kronecker-sparse chain

Given a chain `π = (a, b, c, d)`, Section III-B stacks two copies of the support `S_π` on top
of each other and shows (**Lemma 2**) that the permutation `P_π := C_{2,a} ⊗ I_{bd}` of
equation (9) regroups the stack into the support `S_π̄` of the *doubled* chain
`π̄ = (a, 2b, c, d)`.

As in `Test.Paper.Lemma1`, we represent the doubled index set `⟦1, 2b⟧` by `Bool × B` rather
than by `Fin (2b)` (dropping the never-used trivial `Fin 1` factor of `1_{2×1}`), and `P_π` is
built *directly from the commutation matrix* of Lemma 1, exactly as in the paper's construction
`P_π := C_{2,a} ⊗ I_{bd}` (equation (9)): `Pperm` acts by the commutation matrix
`commutationMatrix A Bool R` on the `(a, ε)` coordinates, and by the identity elsewhere.
Lemma 2 is then proved by the *same* single-nonzero-term computation as Lemma 1, generalized to
carry the extra untouched `(b, d)` coordinates along for the ride.
-/

open Matrix

variable {A B C D : Type*} [DecidableEq A] [Fintype A] [DecidableEq B] [Fintype B]
  [DecidableEq C] [DecidableEq D] [Fintype D] {R : Type*} [CommSemiring R]

omit [DecidableEq C] in
/-- **Lemma 2.** `P_π · [S_π ; S_π] = S_π̄` (equations (6)/(7)/(8), general form): applying
`Pperm` to the two stacked copies of `S_π` (`repeatFst (SG A B C D)`, the analogue of
`1_{2×1} ⊗ S_π`) yields exactly the support `S_π̄` of the doubled chain `π̄ = (a, 2b, c, d)`. -/
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
