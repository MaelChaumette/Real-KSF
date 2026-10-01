import RealKSFLean.Paper.Lemma1
import RealKSFLean.Support.Lemma2Aux
import RealKSFLean.Support.Permutation

/-!
# Lemma 2

Lemma 2 characterizes when the choice `P_ℓ := P_{π_ℓ}` satisfies conditions (4), (5), (6):

* (6) always holds, as a direct consequence of Lemma 1 (`Pperm_mul_repeatFst`,
  `RealKSFLean.Paper.Lemma1`);
* (4) (the first factor, `ℓ = 1`) rewrites, since `S_πᵀ = S_(a,c,b,d)` (`SG_transpose`), as
  `P_{π_2} · [S_(a,c,b,d) ; S_(a,c,b,d)] = S_(a,2c,b,d)`, i.e. as (9) for `ℓ = 1`
  (`lemma2_first`);
* (5) (the interior factors) — for the *current* pattern `π = (a, b, c, d)`, doubled on *both*
  rows and columns via `Pπ` and then hit on the right by `P_{π'}ᵀ` for the *next* pattern
  `π' = (a', b', c', d')` — is equivalent to (9), which is `Pπ'` applied (on the left) to `π`'s
  own `(a, c, d)`-structure (`lemma2_core`).

The matrix products only make sense once the flat index sets `A × C × D` and `A' × B' × D'`
are identified — condition **C1** in the paper — which we take here as an arbitrary hypothesis
`e : A × C × D ≃ A' × B' × D'` (any witness that they have the same cardinality;
`RealKSFLean.Support.FlatChain` builds the *canonical*, arithmetic one once `a, b, c, d, a', b',
d'` are actual naturals with `a * c * d = a' * b' * d'`).

The proof is *pure algebra*: substitute Lemma 1 (`Pperm_mul_repeatFst`) into the "doubled
twice" stack via `mul_repeatFstCol`, then transpose (`Matrix.transpose_mul`,
`Matrix.transpose_submatrix`, `repeatFst_transpose`) and apply `SG_transpose` to land back on
the same expression reindexed for the *other* pattern. No combinatorics beyond Lemma 1 is used:
the genuinely hard, arithmetic question of *when* a *canonical* identification `e` makes this
usable (Proposition 1's conditions C2, C3) is deliberately not addressed here.
-/

open Matrix

variable {A B C D : Type*} [DecidableEq A] [Fintype A] [DecidableEq B] [Fintype B]
  [DecidableEq C] [DecidableEq D] [Fintype D] {R : Type*} [CommSemiring R]
variable {A' B' D' : Type*} [DecidableEq A'] [Fintype A'] [DecidableEq B'] [Fintype B']
  [DecidableEq D'] [Fintype D']

omit [DecidableEq C] in
/-- **Lemma 2, interior factors.** Equation (5)'s left-hand side (`Pπ · [[Sπ,Sπ],[Sπ,Sπ]] · Pπ'ᵀ`,
with the column space of the doubled stack identified with `Pπ'`'s row space via `e`) equals
equation (9)'s left-hand side (`Pπ' · [S_(a,c,2b,d) ; S_(a,c,2b,d)]`, using `π`'s own `(a, c, d)`
and `Bool × B` as the already-`b`-doubled free slot), transposed. Consequently, for any target
`T`, (5) (`... = T`) holds if and only if (9) (`... = Tᵀ`) holds: apply `Matrix.transpose` to
both sides and use `Matrix.transpose_transpose`. -/
theorem lemma2_core (e : A × C × D ≃ A' × B' × D') :
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

omit [Fintype A] [DecidableEq B] [Fintype B] [DecidableEq C] [Fintype D] in
/-- **Lemma 2, first factor.** The left-hand side of (4), `P_{π_2} · [S_{π_1}ᵀ ; S_{π_1}ᵀ]`
(again with `π_1`'s column space identified with `π_2`'s row space via `e`), is equal to
`P_{π_2} · [S_(a_1,c_1,b_1,d_1) ; S_(a_1,c_1,b_1,d_1)]`, the left-hand side of (9) for `ℓ = 1`
(`b'_1 = b_1`, no doubling of the free slot). -/
theorem lemma2_first (e : A × C × D ≃ A' × B' × D') :
    (Pperm : Matrix (A' × (Bool × B') × D') (Bool × A' × B' × D') R) *
        Matrix.submatrix (repeatFst (p := Bool) (SG : Matrix (A × B × D) (A × C × D) R)ᵀ)
          ((Equiv.refl Bool).prodCongr e).symm id =
      (Pperm : Matrix (A' × (Bool × B') × D') (Bool × A' × B' × D') R) *
        Matrix.submatrix (repeatFst (p := Bool) (SG : Matrix (A × C × D) (A × B × D) R))
          ((Equiv.refl Bool).prodCongr e).symm id := by
  rw [SG_transpose]
