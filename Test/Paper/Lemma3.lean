import Test.Paper.Lemma2
import Test.Support.Lemma1Aux
import Test.Support.Permutation

/-!
# Lemma 3

Lemma 3 relates equation (7) — for the *current* chain `π = (a, b, c, d)`, doubled on *both*
rows and columns via `Pπ` and then hit on the right by `P_{π'}ᵀ` for the *next* chain
`π' = (a', b', c', d')` — to equation (10), which is `Pπ'` applied (on the left) to `π`'s own
`(a, c, d)`-structure. The matrix products only make sense once the flat index sets
`A × C × D` and `A' × B' × D'` are identified — condition **C1** in the paper — which we take
here as an arbitrary hypothesis `e : A × C × D ≃ A' × B' × D'` (any witness that they have the
same cardinality; `Test.Support.FlatChain` builds the *canonical*, arithmetic one once `a, b, c,
d, a', b', d'` are actual naturals with `a * c * d = a' * b' * d'`).

The proof is *pure algebra*: substitute Lemma 2 (`Pperm_mul_repeatFst`) into the "doubled
twice" stack via `mul_repeatFstCol`, then transpose (`Matrix.transpose_mul`,
`Matrix.transpose_submatrix`, `repeatFst_transpose`) and apply `SG_transpose` to land back on
the same expression reindexed for the *other* chain. No combinatorics beyond Lemma 2 is used:
the genuinely hard, arithmetic question of *when* a *canonical* identification `e` makes this
usable (Proposition 1's conditions C2, C3) is deliberately not addressed here.
-/

open Matrix

variable {A B C D : Type*} [DecidableEq A] [Fintype A] [DecidableEq B] [Fintype B]
  [DecidableEq C] [DecidableEq D] [Fintype D] {R : Type*} [CommSemiring R]
variable {A' B' D' : Type*} [DecidableEq A'] [Fintype A'] [DecidableEq B'] [Fintype B']
  [DecidableEq D'] [Fintype D']

omit [DecidableEq C] in
/-- **Lemma 3.** Equation (7)'s left-hand side (`Pπ · [[Sπ,Sπ],[Sπ,Sπ]] · Pπ'ᵀ`, with the
column space of the doubled stack identified with `Pπ'`'s row space via `e`) equals equation
(10)'s left-hand side (`Pπ' · [S_(a,c,2b,d) ; S_(a,c,2b,d)]`, using `π`'s own `(a, c, d)` and
`Bool × B` as the already-`b`-doubled free slot), transposed. Consequently, for any target `T`,
(7) (`... = T`) holds if and only if (10) (`... = Tᵀ`) holds: apply `Matrix.transpose` to both
sides and use `Matrix.transpose_transpose`. -/
theorem lemma3_core (e : A × C × D ≃ A' × B' × D') :
    Matrix.submatrix
        ((Pperm : Matrix (A × (Bool × B) × D) (Bool × A × B × D) R) *
          repeatFstCol (p := Bool) (repeatFst (p := Bool) (SG : Matrix (A × B × D) (A × C × D) R)))
        id ((Equiv.refl Bool).prodCongr e).symm *
      (Pperm : Matrix (A' × (Bool × B') × D') (Bool × A' × B' × D') R)ᵀ =
      ((Pperm : Matrix (A' × (Bool × B') × D') (Bool × A' × B' × D') R) *
        Matrix.submatrix
          (repeatFst (p := Bool) (SG : Matrix (A × C × D) (A × (Bool × B) × D) R))
          ((Equiv.refl Bool).prodCongr e).symm id)ᵀ := by
  rw [mul_repeatFstCol, Pperm_mul_repeatFst, Matrix.transpose_mul, Matrix.transpose_submatrix,
    repeatFst_transpose, SG_transpose]
