import RealKSFLean.Definitions

/-!
# Lemma 1's technical companions

Purely formal companions of `repeatFst`/`repeatFstCol` (`RealKSFLean.Definitions`), needed in
`RealKSFLean.Support.FlatChain` to handle the *column*-doubled matrices `[S_π S_π]` and
`[[S_π, S_π], [S_π, S_π]]` used by Lemma 3: `mul_repeatFstCol` says `repeatFstCol` commutes with
left-multiplication, and `repeatFstCol_transpose`/`repeatFst_transpose` relate it to
transposition. None of this is stated in the paper itself — it is bookkeeping needed to reuse
Lemma 1/2's machinery when assembling Lemma 3.
-/

open Matrix

variable {m p q : Type*} [DecidableEq m] [DecidableEq p] [Fintype m] [Fintype p]
variable {R : Type*} [NonAssocSemiring R]

omit [DecidableEq m] [DecidableEq p] [Fintype p] in
theorem mul_repeatFstCol {l : Type*} (M : Matrix l m R) (N : Matrix m q R) :
    M * repeatFstCol (p := p) N = repeatFstCol (M * N) := by
  ext i j
  simp [repeatFstCol, Matrix.mul_apply]

omit [DecidableEq p] [Fintype p] [NonAssocSemiring R] in
theorem repeatFstCol_transpose {l : Type*} {R : Type*} (N : Matrix l q R) :
    (repeatFstCol (p := p) N)ᵀ = repeatFst Nᵀ := by
  ext i j
  simp [repeatFstCol, repeatFst, Matrix.transpose_apply]

omit [DecidableEq p] [Fintype p] [NonAssocSemiring R] in
/-- The converse of `repeatFstCol_transpose`: transposing a row-repeat gives a column-repeat
of the transpose. -/
theorem repeatFst_transpose {l : Type*} {R : Type*} (N : Matrix l q R) :
    (repeatFst (p := p) N)ᵀ = repeatFstCol Nᵀ := by
  ext i j
  simp [repeatFstCol, repeatFst, Matrix.transpose_apply]
