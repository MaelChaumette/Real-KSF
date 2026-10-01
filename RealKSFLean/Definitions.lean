import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# All definitions used throughout the development

This file collects, in one place, every `def`/`structure` used anywhere in this project — both
in `RealKSFLean/Paper` (the paper's own objects: Kronecker-sparse factors, the permutation `P_π`,
the real/imaginary doubling `K̄`, the arithmetic of Proposition 1, ...) and in `RealKSFLean/Support`
(the extra bridging machinery — flat `Fin`-indexed reindexings, value-preserving casts, the
telescoping construction `K̃_ℓ`, ... — needed to connect the paper's statements to each other in
Lean but not part of the paper itself).

No proof of a paper *result* lives here — only definitions.

Each section below is a straight port of one original file's definitions, in the same order
they used to appear, so `RealKSFLean/Paper/*.lean` and `RealKSFLean/Support/*.lean` can be read side
by side with this file to see exactly which objects each proof is about.
-/

open Matrix

/-! ## From `commutationMatrix` (originally the project's root file) -/

section CommutationMatrix

variable (m n : Type*) [DecidableEq m] [DecidableEq n]
variable (R : Type*) [Zero R] [One R]

/-- The commutation matrix `C_{m,n} : Matrix (m × n) (n × m) R` of Definition 2: the permutation
matrix of `Prod.swap`. It satisfies `C_{m,n}.mulVec A.vec = A.transpose.vec` for every
`A : Matrix m n R'` (`RealKSFLean.Paper.Definition2`), and lets a product `C_{m,n} * X` turn a
"row-repeat" into another "row-repeat" (equation (8)). -/
def commutationMatrix : Matrix (m × n) (n × m) R :=
  Matrix.of fun i j => if i = j.swap then 1 else 0

end CommutationMatrix

/-! ## Row/column repetition (equation (8)) -/

section Repeat

variable {m p q : Type*} [DecidableEq m] [DecidableEq p] [Fintype m] [Fintype p]
variable {R : Type*} [NonAssocSemiring R]

/-- "Repeat `A`'s rows along `p`, with `p` first": the matrix analogue of `1_{p×1} ⊗ A`. -/
def repeatFst (A : Matrix m q R) : Matrix (p × m) q R := Matrix.of fun i j => A i.2 j

/-- "Repeat `A`'s rows along `p`, with `p` last": the matrix analogue of `A ⊗ 1_{p×1}`. -/
def repeatSnd (A : Matrix m q R) : Matrix (m × p) q R := Matrix.of fun i j => A i.1 j

/-- "Repeat `N`'s columns along `p`, with `p` first": the matrix analogue of `1_{1×p} ⊗ N`. Used
for the *column*-doubled matrix `[S_π S_π]` of equation (5). -/
def repeatFstCol {l : Type*} (N : Matrix l q R) : Matrix l (p × q) R :=
  Matrix.of fun i j => N i j.2

end Repeat

/-! ## From `KroneckerSparse` (Definition 1) -/

section KroneckerSparse

variable {a b c d : ℕ} {R : Type*}

/-- The support `S_π = I_a ⊗ 1_{b×c} ⊗ I_d` of a Kronecker-sparse factor of (sparsity) pattern
`π = (a, b, c, d)`, as a `{0, 1}`-valued matrix. -/
def KSupport (a b c d : ℕ) : Matrix (Fin a × Fin b × Fin d) (Fin a × Fin c × Fin d) ℕ :=
  Matrix.of fun i j => if i.1 = j.1 ∧ i.2.2 = j.2.2 then 1 else 0

/-- **Definition 1.** `K` is a Kronecker-sparse factor of pattern `(a, b, c, d)` (`K ∈ 𝒦_π`) when
its support
is included in `S_π`, i.e. `K i j` can only be nonzero when `i` and `j` agree on their `a`- and
`d`-components. -/
def IsKSparse [Zero R] (a b c d : ℕ)
    (K : Matrix (Fin a × Fin b × Fin d) (Fin a × Fin c × Fin d) R) : Prop :=
  ∀ i j, i.1 ≠ j.1 ∨ i.2.2 ≠ j.2.2 → K i j = 0

end KroneckerSparse

/-! ## The permutation `P_π` (Lemma 1 / Lemma 2's objects) -/

section Permutation

variable {A B C D : Type*} [DecidableEq A] [Fintype A] [DecidableEq B] [Fintype B]
  [DecidableEq C] [DecidableEq D] [Fintype D] {R : Type*} [CommSemiring R]

/-- Generic Kronecker-sparse support pattern `I_A ⊗ 1_{B×C} ⊗ I_D`, for arbitrary (not
necessarily `Fin`-indexed) finite "outer" (`A`) and "inner" (`D`) index types. -/
def SG : Matrix (A × B × D) (A × C × D) R :=
  Matrix.of fun i j => if i.1 = j.1 ∧ i.2.2 = j.2.2 then 1 else 0

/-- The purely combinatorial reshuffle underlying `Pperm`: move the "which stacked copy" bit
`ε` from the front of `(ε, x, y, z)` to sit next to the `b`-coordinate `y`. -/
def groupEquiv (A B D : Type*) : Bool × A × B × D ≃ A × (Bool × B) × D where
  toFun p := (p.2.1, (p.1, p.2.2.1), p.2.2.2)
  invFun p := (p.2.1.1, p.1, p.2.1.2, p.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The permutation `P_π := C_{a,2} ⊗ I_{bd}` of equation (7): it acts by the commutation matrix
`C_{a,2}` on the `(a, ε)` coordinates, and by the identity on the untouched `(b, d)`-coordinates. -/
def Pperm : Matrix (A × (Bool × B) × D) (Bool × A × B × D) R :=
  Matrix.of fun i k =>
    commutationMatrix A Bool R (i.1, i.2.1.1) (k.1, k.2.1) *
      (if i.2.1.2 = k.2.2.1 ∧ i.2.2 = k.2.2.2 then 1 else 0)

end Permutation

/-! ## The pre-factorization of the real part (equation (1)'s objects) -/

section RealPartChain

variable {J : ℕ → Type*} [∀ k, Fintype (J k)] [∀ k, DecidableEq (J k)]

/-- The product `K 0 * K 1 * ... * K (L-1) : Matrix (J 0) (J L) ℂ` of a sequence of complex
matrices. -/
def Kprod (K : (k : ℕ) → Matrix (J k) (J (k + 1)) ℂ) : (L : ℕ) → Matrix (J 0) (J L) ℂ
  | 0 => 1
  | L + 1 => Kprod K L * K L

/-- The same sequence of factors, with the first one multiplied by the scalar `z`: the factors
of `z K_1 ⋯ K_L`, used to treat `Im(K_1 ⋯ K_L) = Re((-𝚥 K_1) ⋯ K_L)` and more generally
`Re(z K_1 ⋯ K_L)` (Section III-D). -/
def scaleFirst (z : ℂ) (K : (k : ℕ) → Matrix (J k) (J (k + 1)) ℂ) (k : ℕ) :
    Matrix (J k) (J (k + 1)) ℂ :=
  if k = 0 then z • K k else K k

/-- The "doubled" index family: `J2 J 0 = J 0` and `J2 J (k+1) = J (k+1) ⊕ J (k+1)`. -/
@[reducible] def J2 (J : ℕ → Type*) : ℕ → Type _
  | 0 => J 0
  | k + 1 => J (k + 1) ⊕ J (k + 1)

instance instFintypeJ2 : ∀ k, Fintype (J2 J k)
  | 0 => (inferInstance : Fintype (J 0))
  | _ + 1 => (inferInstance : Fintype (_ ⊕ _))

instance instDecidableEqJ2 : ∀ k, DecidableEq (J2 J k)
  | 0 => (inferInstance : DecidableEq (J 0))
  | _ + 1 => (inferInstance : DecidableEq (_ ⊕ _))

/-- The real "doubled" factors `Kbar 0, Kbar 1, ...` of (1): `Kbar 0` concatenates `Re (K 0)`
and `Im (K 0)` as columns, while `Kbar (k+1)` is the `2 × 2` block matrix
`[Re (K (k+1)) Im (K (k+1)) ; -Im (K (k+1)) Re (K (k+1))]`. -/
def Kbar (K : (k : ℕ) → Matrix (J k) (J (k + 1)) ℂ) :
    (k : ℕ) → Matrix (J2 J k) (J2 J (k + 1)) ℝ
  | 0 => fromCols ((K 0).map Complex.re) ((K 0).map Complex.im)
  | k + 1 =>
      fromBlocks ((K (k + 1)).map Complex.re) ((K (k + 1)).map Complex.im)
        (-(K (k + 1)).map Complex.im) ((K (k + 1)).map Complex.re)

/-- The product `Kbar 0 * Kbar 1 * ... * Kbar (L-1) : Matrix (J 0) (J2 J L) ℝ`. -/
def Kbarprod (K : (k : ℕ) → Matrix (J k) (J (k + 1)) ℂ) : (L : ℕ) → Matrix (J 0) (J2 J L) ℝ
  | 0 => 1
  | L + 1 => Kbarprod K L * Kbar K L

end RealPartChain

/-! ## From `FlatChain` (the flat `Fin`-indexed bridge) -/

section FlatChain

variable {R : Type*} [CommSemiring R]

/-- The standard mixed-radix identification of the row (or column) space `Fin a × Fin b ×
Fin d` of a Kronecker-sparse pattern with the flat space `Fin (a * b * d)`, matching Definition 1
(`ℝ^{abd × acd}`). -/
def finChainEquiv (a b d : ℕ) : Fin a × Fin b × Fin d ≃ Fin (a * (b * d)) :=
  (Equiv.refl (Fin a)).prodCongr finProdFinEquiv |>.trans finProdFinEquiv

/-- The flat identification `Bool × Fin n ≃ Fin (2 * n)` of the two stacked copies (`ε = 0` or
`ε = 1`) of an `n`-element flat index set with a single `Fin (2 * n)`. -/
def boolFinEquiv (n : ℕ) : Bool × Fin n ≃ Fin (2 * n) :=
  (finTwoEquiv.symm.prodCongr (Equiv.refl (Fin n))).trans finProdFinEquiv

/-- The flat identification of the *stacked* row space `Bool × Fin a × Fin b × Fin d` (two
copies of pattern `(a, b, d)`) with `Fin (2 * (a * (b * d)))`. -/
def finChainEquivStack (a b d : ℕ) : Bool × Fin a × Fin b × Fin d ≃ Fin (2 * (a * (b * d))) :=
  (Equiv.refl Bool).prodCongr (finChainEquiv a b d) |>.trans (boolFinEquiv (a * (b * d)))

/-- The flat identification of the *doubled* row space `Fin a × (Bool × Fin b) × Fin d` (pattern
`(a, 2b, d)`, with the doubled slot represented as `Bool × Fin b`) with `Fin (a * (2 * b * d))`.
-/
def finChainEquiv' (a b d : ℕ) : Fin a × (Bool × Fin b) × Fin d ≃ Fin (a * (2 * b * d)) :=
  ((Equiv.refl (Fin a)).prodCongr ((boolFinEquiv b).prodCongr (Equiv.refl (Fin d)))) |>.trans
    ((Equiv.refl (Fin a)).prodCongr finProdFinEquiv) |>.trans finProdFinEquiv

/-- The flat, `Fin`-indexed support `S_π` of Definition 1, for pattern `π = (a, b, c, d)`:
`SF a b c d = KSupport a b c d` up to the reindexing `finChainEquiv`. -/
def SF (a b c d : ℕ) : Matrix (Fin (a * (b * d))) (Fin (a * (c * d))) R :=
  Matrix.submatrix (SG (A := Fin a) (B := Fin b) (C := Fin c) (D := Fin d))
    (finChainEquiv a b d).symm (finChainEquiv a c d).symm

/-- The flat, `Fin`-indexed version of `Pperm`, i.e. the actual permutation `P_π := C_{a,2} ⊗
I_{bd}` of equation (7), acting between the genuinely `Fin`-indexed spaces `Fin (2*(a*(b*d)))`
(stack of two copies of pattern `(a,b,d)`) and `Fin (a*(2*b*d))` (pattern `(a, 2b, d)`). -/
def PpermF (a b d : ℕ) : Matrix (Fin (a * (2 * b * d))) (Fin (2 * (a * (b * d)))) R :=
  Matrix.submatrix (Pperm (A := Fin a) (B := Fin b) (D := Fin d))
    (finChainEquiv' a b d).symm (finChainEquivStack a b d).symm

/-- The equivalence underlying `PpermF a b d`: `Fin (2*(a*(b*d))) ≃ Fin (a*(2*b*d))`, built by
composing the three combinatorial equivalences already in play. -/
def rhoEquiv (a b d : ℕ) : Fin (2 * (a * (b * d))) ≃ Fin (a * (2 * b * d)) :=
  (finChainEquivStack a b d).symm.trans
    ((groupEquiv (Fin a) (Fin b) (Fin d)).trans (finChainEquiv' a b d))

/-- The flat, `Fin`-indexed version of `[S_π ; S_π]` (the two stacked copies of `S_π`). -/
def repeatFstFlat (a b c d : ℕ) : Matrix (Fin (2 * (a * (b * d)))) (Fin (a * (c * d))) R :=
  Matrix.submatrix
    (repeatFst (p := Bool) (SG (A := Fin a) (B := Fin b) (C := Fin c) (D := Fin d)))
    (finChainEquivStack a b d).symm (finChainEquiv a c d).symm

/-- The flat identification `Fin N ⊕ Fin N ≃ Fin (2 * N)` of the two stacked copies of an
`N`-element flat index set built by the real/imaginary-part doubling of `Kbar`/`J2` (`Sum`-typed)
with the flat doubling used by `PpermF` (`Fin`-typed). -/
def sumToFinEquiv (N : ℕ) : Fin N ⊕ Fin N ≃ Fin (2 * N) :=
  finSumFinEquiv.trans (finCongr (by ring))

/-- The flat, `Fin`-indexed reformulation of Kronecker-sparsity (Definition 1): entries can only
be nonzero when their flat indices agree on the outer `a`-block and the inner `d`-remainder. -/
def IsKSparseFlat (a b c d : ℕ) (K : Matrix (Fin (a * (b * d))) (Fin (a * (c * d))) R) :
    Prop :=
  ∀ i j, i.val / (b * d) ≠ j.val / (c * d) ∨ i.val % d ≠ j.val % d → K i j = 0

end FlatChain

/-! ## From `Proposition1` (the arithmetic of C1, C2, C3, and chainability) -/

namespace Prop1

/-- The flat row-permutation `ρ_{π'}` associated to `P_{π'}` (equations (9)/(10)), for pattern
`π' = (a', b', d')`. -/
def rho (b' d' N n : ℕ) : ℕ :=
  2 * (b' * d') * ((n % N) / (b' * d')) + (b' * d') * (n / N) + n % (b' * d')

/-- Which of the `a * d` blocks of the *stacked* pattern `(a, c, d)` the flat index `n` belongs
to: the pair `(i, k₂)` of the paper's indexing `idx(ε, i, k₁, k₂)` of the rows of `X_ℓ`. -/
def label1 (c d N n : ℕ) : ℕ × ℕ := ((n % N) / (c * d), n % d)

/-- Which of the `a * d` blocks of the *doubled* pattern `(a, 2c, d)` the flat index `m`
belongs to: the pair `(i, k₂)` of the paper's indexing `idx'(i, k'₁, k₂)` of the rows of `Y_ℓ`. -/
def label2 (c d m : ℕ) : ℕ × ℕ := (m / (2 * c * d), m % d)

/-- **Equations (9)/(10).** `P_{π'}` sends each block of the stacked `(a,c,d)`-grouping to the
identically-labelled block of the doubled `(a,2c,d)`-grouping. -/
def Condition10 (c d b' d' N : ℕ) : Prop :=
  ∀ n < 2 * N, label2 c d (rho b' d' N n) = label1 c d N n

/-- **C1**: `a * c * d = a' * b' * d'` (dimension compatibility for `K_ℓ K_{ℓ+1}`). -/
def C1 (a c d a' b' d' : ℕ) : Prop := a * c * d = a' * b' * d'

/-- **C2**: `d ∣ b' * d'`. -/
def C2 (d b' d' : ℕ) : Prop := d ∣ b' * d'

/-- **C3**: `a ∣ a'`. -/
def C3 (a a' : ℕ) : Prop := a ∣ a'

/-- The three conditions **C1**, **C2**, **C3** of Proposition 1, at the junction between two
consecutive patterns `π_ℓ = (a, b, c, d)` and `π_{ℓ+1} = (a', b', c', d')`. -/
structure Conditions (a c d a' b' d' : ℕ) : Prop where
  /-- `a * c * d = a' * b' * d'`. -/
  c1 : C1 a c d a' b' d'
  /-- `d ∣ b' * d'`. -/
  c2 : C2 d b' d'
  /-- `a ∣ a'`. -/
  c3 : C3 a a'

/-- Two consecutive patterns are **chainable** [13, Def. 4.12]: as recalled in the letter's
footnote, this is `C1 ∧ C2 ∧ C3 ∧ (d' ∣ d)`. -/
structure Chainable2 (a c d a' b' d' : ℕ) : Prop extends Conditions a c d a' b' d' where
  /-- `d' ∣ d`: part of [13]'s chainability, not needed for Proposition 1. -/
  d_dvd : d' ∣ d

end Prop1

/-! ## From `Assembly` (value-preserving casts) -/

section Assembly

/-- A value-preserving identification `Fin n ≃ Fin m`, for `n = m`. Unlike `Equiv.cast`, its
`.val` is *definitionally* the identity. -/
def natCastEquiv {n m : ℕ} (h : n = m) : Fin n ≃ Fin m where
  toFun := Fin.cast h
  invFun := Fin.cast h.symm
  left_inv _ := by simp
  right_inv _ := by simp

/-- The `C1`-induced identification of the *doubled* flat spaces `Fin (2*(a*(c*d)))` and
`Fin (2*(a'*(b'*d')))`. -/
def castDouble {a c d a' b' d' : ℕ} (h : a * (c * d) = a' * (b' * d')) :
    Fin (2 * (a * (c * d))) ≃ Fin (2 * (a' * (b' * d'))) :=
  natCastEquiv (congrArg (2 * ·) h)

/-- The `C1`-induced identification of the two "doubled-once-more" flat spaces
`Fin (a*(2*c*d))` and `Fin (a'*(2*b'*d'))`. -/
def aDouble {a c d a' b' d' : ℕ} (h : a * (c * d) = a' * (b' * d')) :
    Fin (a * (2 * c * d)) ≃ Fin (a' * (2 * b' * d')) :=
  natCastEquiv (by rw [show a * (2 * c * d) = 2 * (a * (c * d)) from by ring, h]; ring)

end Assembly

/-! ## From `ChainAssembly` (the telescoping construction of `K̃_ℓ`) -/

section ChainAssembly

open Prop1

variable (a b c d : ℕ → ℕ)
variable (hC1 : ∀ k, C1 (a k) (c k) (d k) (a (k + 1)) (b (k + 1)) (d (k + 1)))

/-- The flat row space of pattern `k`: `Fin (a k * (b k * d k))`, matching `finChainEquiv`'s own
convention. -/
@[reducible] def Jfam (k : ℕ) : Type := Fin (a k * (b k * d k))

instance instFintypeJfam : ∀ k, Fintype (Jfam a b d k) :=
  fun _ => inferInstanceAs (Fintype (Fin _))
instance instDecidableEqJfam : ∀ k, DecidableEq (Jfam a b d k) :=
  fun _ => inferInstanceAs (DecidableEq (Fin _))

/-- The `C1`-induced identification of pattern `k`'s flat *column* space with pattern `k+1`'s
flat *row* space `Jfam (k+1)`. -/
def colCastEquiv (k : ℕ) : Fin (a k * (c k * d k)) ≃ Jfam a b d (k + 1) :=
  natCastEquiv (by
    rw [← mul_assoc, show a k * c k * d k = a (k + 1) * b (k + 1) * d (k + 1) from hC1 k,
      mul_assoc])

/-- The flat reindexing of a sequence of genuine (`Fin`-product-typed) Kronecker-sparse factors:
`Kflat k` is `K_orig k` after identifying its row space with `Jfam k` and its column space with
`Jfam (k+1)` (via C1). -/
def Kflat (K_orig : (k : ℕ) → Matrix (Fin (a k) × Fin (b k) × Fin (d k))
    (Fin (a k) × Fin (c k) × Fin (d k)) ℂ) (k : ℕ) :
    Matrix (Jfam a b d k) (Jfam a b d (k + 1)) ℂ :=
  Matrix.submatrix (K_orig k) (finChainEquiv (a k) (b k) (d k)).symm
    (((finChainEquiv (a k) (c k) (d k)).trans (colCastEquiv a b c d hC1 k)).symm)

/-- The permutation `P_{π_k} := C_{a_k,2} ⊗ I_{b_k d_k}` of equation (7), reindexed via
`sumToFinEquiv` so it can be inserted directly next to `Kbar`'s `Sum`-typed doubled spaces. -/
def Pfor (k : ℕ) : Matrix (Fin (a k * (2 * b k * d k))) (Jfam a b d k ⊕ Jfam a b d k) ℝ :=
  Matrix.submatrix (PpermF (a k) (b k) (d k)) (Equiv.refl _) (sumToFinEquiv (a k * (b k * d k)))

/-- The row-permutation `ρ_{π_k}` associated to `Pfor k` (i.e. to `P_{π_k}`), as an equivalence
from `Kbar`'s `Sum`-typed doubled space to `Pfor k`'s row space: `Pfor k I p = 1` exactly when
`I = pforEquiv k p`. -/
def pforEquiv (k : ℕ) : Jfam a b d k ⊕ Jfam a b d k ≃ Fin (a k * (2 * b k * d k)) :=
  (sumToFinEquiv (a k * (b k * d k))).trans (rhoEquiv (a k) (b k) (d k))

/-- The witness factors used for the "only if" direction of Proposition 1: `K_k := (1 + 𝚥) S_{π_k}`,
a Kronecker-sparse factor of pattern `π_k` whose real *and* imaginary parts have the full support
`S_{π_k}`, so that the support of each `K̄_k` is exactly the one of the paper's stacked supports. -/
def ksWitness (k : ℕ) : Matrix (Fin (a k) × Fin (b k) × Fin (d k))
    (Fin (a k) × Fin (c k) × Fin (d k)) ℂ :=
  (1 + Complex.I) • (SG : Matrix (Fin (a k) × Fin (b k) × Fin (d k))
    (Fin (a k) × Fin (c k) × Fin (d k)) ℂ)

variable (K_orig : (k : ℕ) → Matrix (Fin (a k) × Fin (b k) × Fin (d k))
  (Fin (a k) × Fin (c k) × Fin (d k)) ℂ)

/-- The row space of `Ktilde k`: `Jfam 0` for `k = 0` (no permutation on the very first factor),
and the flat "doubled" space `Fin (a k * (2 * b k * d k))` (`Pfor`'s own output) for `k ≥ 1`. -/
@[reducible] def KtildeRow : ℕ → Type
  | 0 => Jfam a b d 0
  | (k + 1) => Fin (a (k + 1) * (2 * b (k + 1) * d (k + 1)))

@[reducible] instance instFintypeKtildeRow : ∀ k, Fintype (KtildeRow a b d k)
  | 0 => inferInstanceAs (Fintype (Jfam a b d 0))
  | _ + 1 => inferInstanceAs (Fintype (Fin _))

@[reducible] instance instDecidableEqKtildeRow : ∀ k, DecidableEq (KtildeRow a b d k)
  | 0 => inferInstanceAs (DecidableEq (Jfam a b d 0))
  | _ + 1 => inferInstanceAs (DecidableEq (Fin _))

/-- **The new, permuted Kronecker-sparse factors** `K̃_k`, equation (2) (with `P_ℓ := P_{π_ℓ}`
as in (7)): `K̃_0 := K̄_0 · P_1ᵀ`, and `K̃_{k+1} := P_{k+1} · K̄_{k+1} · P_{k+2}ᵀ` for the
interior factors. The last factor `K̃_L := P_L · K̄_L` is not part of this family: it is the
trailing factor of `re_Kprod_eq_KtildeProd` (`RealKSFLean.Paper.Proposition1Architecture`). -/
def Ktilde : (k : ℕ) → Matrix (KtildeRow a b d k) (KtildeRow a b d (k + 1)) ℝ
  | 0 => Kbar (Kflat a b c d hC1 K_orig) 0 * (Pfor a b d 1)ᵀ
  | (k + 1) => Pfor a b d (k + 1) * Kbar (Kflat a b c d hC1 K_orig) (k + 1) *
      (Pfor a b d (k + 2))ᵀ

/-- The product `K̃_0 · K̃_1 · ... · K̃_{L-1} : Matrix (KtildeRow 0) (KtildeRow L) ℝ`. -/
def KtildeProd : (L : ℕ) → Matrix (KtildeRow a b d 0) (KtildeRow a b d L) ℝ
  | 0 => 1
  | L + 1 => KtildeProd L * Ktilde a b c d hC1 K_orig L

end ChainAssembly
