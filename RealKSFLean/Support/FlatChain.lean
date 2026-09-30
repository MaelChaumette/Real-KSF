import RealKSFLean.Definitions
import RealKSFLean.Paper.Lemma2
import RealKSFLean.Support.Permutation

/-!
# From the abstract `(A, B, D)` picture to flat `Fin`-indexed chains

`RealKSFLean.Paper.Lemma1` and `RealKSFLean.Paper.Lemma2` prove Lemma 1 and Lemma 2 for a single
chain, using *abstract* index types `A, B, D` for the "outer", "middle" and "inner" coordinates.
This is enough there because both lemmas only ever look at *one* chain's own structure.

Lemma 3 (and later Proposition 1) compare *two different* chains `π = (a, b, c, d)` and
`π' = (a', b', c', d')`, and the matrix product `Pπ' · (something built from π)` only makes
sense once we remember that Kronecker-sparse factors are really indexed by *flat* naturals:
`Kπ ⊆ ℝ^{abd × acd}`, i.e. rows/columns are `Fin (a*b*d)` and `Fin (a*c*d)`, not the product
type `Fin a × Fin b × Fin d`. Two chains with `a*c*d = a'*b'*d'` (condition **C1**) then share
the *same* flat index set on the nose, which is what makes Proposition 1's condition
meaningful.

This file establishes the technical properties of the flat bridge built in `RealKSFLean.Definitions`
(`finChainEquiv`, `SF`, `PpermF`, `repeatFstFlat`, `sumToFinEquiv`, `IsKSparseFlat`): explicit
value formulas, orthogonality, and the connection back to `IsKSparse`/`Prop1.rho`. None of this
is stated as such in the paper — it is the bookkeeping needed to make Lemma 2/3 and Proposition 1
usable on genuinely `Fin`-indexed matrices.
-/

open Matrix

variable {R : Type*} [CommSemiring R]

/-- The explicit mixed-radix formula for `finChainEquiv`, matching the flat-index conventions
`x*(b*d) + y*d + z`. This is what lets `PpermF`'s action be computed explicitly by
`Nat.div`/`Nat.mod` (`PpermF_apply`), connecting it to `Prop1.rho`. -/
theorem finChainEquiv_apply_val (a b d : ℕ) (x : Fin a) (y : Fin b) (z : Fin d) :
    (finChainEquiv a b d (x, y, z)).val = x.val * (b * d) + (y.val * d + z.val) := by
  simp [finChainEquiv, finProdFinEquiv]
  ring

/-- `repeatFst` commutes with reindexing: repeating a reindexed matrix is the same as
reindexing the repeated matrix. Lets us transport Lemma 1/2 from the abstract `(A, B, D)`
picture to the flat `Fin`-indexed one for free. -/
theorem repeatFst_submatrix {m m' q q' p : Type*} {R : Type*} (M : Matrix m q R)
    (f : m' → m) (g : q' → q) :
    repeatFst (p := p) (Matrix.submatrix M f g) =
      Matrix.submatrix (repeatFst M) (Prod.map id f) g := by
  ext i j
  simp [repeatFst, Matrix.submatrix_apply]

theorem boolFinEquiv_apply_val (n : ℕ) (ε : Bool) (y : Fin n) :
    (boolFinEquiv n (ε, y)).val = y.val + n * (bif ε then 1 else 0) := by
  simp only [boolFinEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map,
    finProdFinEquiv_apply_val, finTwoEquiv, Equiv.coe_fn_symm_mk, id]
  cases ε <;> simp

theorem finChainEquivStack_apply_val (a b d : ℕ) (ε : Bool) (x : Fin a) (y : Fin b) (z : Fin d) :
    (finChainEquivStack a b d (ε, x, y, z)).val =
      x.val * (b * d) + (y.val * d + z.val) + (a * (b * d)) * (bif ε then 1 else 0) := by
  change (boolFinEquiv (a * (b * d)) (ε, finChainEquiv a b d (x, y, z))).val = _
  rw [boolFinEquiv_apply_val, finChainEquiv_apply_val]

theorem finChainEquiv'_apply_val (a b d : ℕ) (x : Fin a) (ε : Bool) (y : Fin b) (z : Fin d) :
    (finChainEquiv' a b d (x, (ε, y), z)).val =
      x.val * (2 * b * d) + (y.val * d + z.val) + (b * d) * (bif ε then 1 else 0) := by
  change (finProdFinEquiv (x, finProdFinEquiv (boolFinEquiv b (ε, y), z))).val = _
  simp only [finProdFinEquiv_apply_val, boolFinEquiv_apply_val]
  ring

/-- **The explicit formula for `SF`.** Matches `Prop1.label1`-style conditions: `SF a b c d`'s
entry at `(i, j)` only depends on the "outer" and "inner" coordinates of `i` (w.r.t. its own
`(a,b,d)`-grouping) and `j` (w.r.t. `(a,c,d)`). -/
theorem SF_apply (a b c d : ℕ) (hb : 0 < b) (hc : 0 < c) (hd0 : 0 < d)
    (i : Fin (a * (b * d))) (j : Fin (a * (c * d))) :
    (SF a b c d : Matrix _ _ R) i j =
      if i.val / (b * d) = j.val / (c * d) ∧ i.val % d = j.val % d then 1 else 0 := by
  unfold SF
  rw [Matrix.submatrix_apply]
  rcases hix : (finChainEquiv a b d).symm i with ⟨x, y, z⟩
  rcases hjx : (finChainEquiv a c d).symm j with ⟨x', y', z'⟩
  have hi : i.val = x.val * (b * d) + (y.val * d + z.val) := by
    conv_lhs => rw [← Equiv.apply_symm_apply (finChainEquiv a b d) i, hix]
    rw [finChainEquiv_apply_val]
  have hj : j.val = x'.val * (c * d) + (y'.val * d + z'.val) := by
    conv_lhs => rw [← Equiv.apply_symm_apply (finChainEquiv a c d) j, hjx]
    rw [finChainEquiv_apply_val]
  have hjlt : y.val * d + z.val < b * d := by
    calc y.val * d + z.val < y.val * d + d := by omega
      _ = (y.val + 1) * d := by ring
      _ ≤ b * d := Nat.mul_le_mul_right d y.isLt
  have hj'lt : y'.val * d + z'.val < c * d := by
    calc y'.val * d + z'.val < y'.val * d + d := by omega
      _ = (y'.val + 1) * d := by ring
      _ ≤ c * d := Nat.mul_le_mul_right d y'.isLt
  have e1 : i.val / (b * d) = x.val := by
    rw [hi, Nat.add_comm (x.val * (b * d)), Nat.add_mul_div_right _ _ (by positivity),
      Nat.div_eq_of_lt hjlt, Nat.zero_add]
  have e2 : i.val % d = z.val := by
    rw [hi]
    have : x.val * (b * d) + (y.val * d + z.val) = z.val + d * (x.val * b + y.val) := by ring
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt z.isLt]
  have e3 : j.val / (c * d) = x'.val := by
    rw [hj, Nat.add_comm (x'.val * (c * d)), Nat.add_mul_div_right _ _ (by positivity),
      Nat.div_eq_of_lt hj'lt, Nat.zero_add]
  have e4 : j.val % d = z'.val := by
    rw [hj]
    have : x'.val * (c * d) + (y'.val * d + z'.val) = z'.val + d * (x'.val * c + y'.val) := by
      ring
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt z'.isLt]
  rw [e1, e2, e3, e4]
  unfold SG
  simp only [Matrix.of_apply, Fin.ext_iff]

theorem PpermF_eq_submatrix_one (a b d : ℕ) :
    (PpermF a b d : Matrix _ _ R) =
      (1 : Matrix (Fin (a * (2 * b * d))) (Fin (a * (2 * b * d))) R).submatrix id
        (rhoEquiv a b d) := by
  ext i k
  unfold PpermF rhoEquiv
  rw [Matrix.submatrix_apply, Pperm_apply, Matrix.submatrix_apply, Matrix.one_apply, id]
  simp only [Equiv.trans_apply]
  set y := (finChainEquivStack a b d).symm k with hy
  set x := (finChainEquiv' a b d).symm i with hx
  set e := groupEquiv (Fin a) (Fin b) (Fin d)
  have hiff : (y = e.symm x) ↔ (i = finChainEquiv' a b d (e y)) := by
    constructor
    · intro heq
      rw [hx] at heq
      have h1 : e y = (finChainEquiv' a b d).symm i := by
        rw [heq, Equiv.apply_symm_apply]
      rw [h1, Equiv.apply_symm_apply]
    · intro heq
      have h1 : (finChainEquiv' a b d).symm i = e y := by
        rw [heq, Equiv.symm_apply_apply]
      rw [hx, h1, Equiv.symm_apply_apply]
  exact if_congr hiff rfl rfl

/-- **`PpermF` is orthogonal**, at the flat level: since `PpermF a b d` is exactly the
permutation matrix of `rhoEquiv a b d` (`PpermF_eq_submatrix_one`), and the permutation matrix
of *any* equivalence is orthogonal, `PpermFᵀ * PpermF = 1`. This is the flat replacement for
`Pperm_orthogonal`, letting the final assembly stay entirely in the `Fin`-indexed world instead
of bridging back to the abstract `Bool ×`-typed `Pperm`. -/
theorem PpermF_orthogonal (a b d : ℕ) :
    (PpermF a b d : Matrix _ _ R)ᵀ * PpermF a b d =
      (1 : Matrix (Fin (2 * (a * (b * d)))) (Fin (2 * (a * (b * d)))) R) := by
  rw [PpermF_eq_submatrix_one, Matrix.transpose_submatrix, Matrix.transpose_one]
  have h := Matrix.one_submatrix_mul (α := R) (rhoEquiv a b d) (Equiv.refl _)
    (Matrix.submatrix (1 : Matrix (Fin (a * (2 * b * d))) _ R) id (rhoEquiv a b d))
  simp only [Equiv.refl_symm, Equiv.coe_refl] at h
  rw [h]
  ext i j
  simp [Matrix.submatrix_apply, Matrix.one_apply, (rhoEquiv a b d).injective.eq_iff]

/-- **The explicit formula for `repeatFstFlat`.** Matches `Prop1.label1`: entry `(k, j)` only
depends on which of the `a * d` blocks of the *stacked* `(a,b,d)`-grouping `k` belongs to. -/
theorem repeatFstFlat_apply (a b c d : ℕ) (hb : 0 < b) (hc : 0 < c) (hd0 : 0 < d)
    (k : Fin (2 * (a * (b * d)))) (j : Fin (a * (c * d))) :
    (repeatFstFlat a b c d : Matrix _ _ R) k j =
      if (k.val % (a * (b * d))) / (b * d) = j.val / (c * d) ∧ k.val % d = j.val % d
        then 1 else 0 := by
  unfold repeatFstFlat
  rw [Matrix.submatrix_apply]
  rcases hkk : (finChainEquivStack a b d).symm k with ⟨ε, x, y, z⟩
  rcases hjx : (finChainEquiv a c d).symm j with ⟨x', y', z'⟩
  have ha : 0 < a := by have := x.isLt; omega
  have habd0 : 0 < a * (b * d) := by positivity
  have hk : k.val = x.val * (b * d) + (y.val * d + z.val) + (a * (b * d)) *
      (bif ε then 1 else 0) := by
    conv_lhs => rw [← Equiv.apply_symm_apply (finChainEquivStack a b d) k, hkk]
    rw [finChainEquivStack_apply_val]
  have hj : j.val = x'.val * (c * d) + (y'.val * d + z'.val) := by
    conv_lhs => rw [← Equiv.apply_symm_apply (finChainEquiv a c d) j, hjx]
    rw [finChainEquiv_apply_val]
  have hjlt : y.val * d + z.val < b * d := by
    calc y.val * d + z.val < y.val * d + d := by omega
      _ = (y.val + 1) * d := by ring
      _ ≤ b * d := Nat.mul_le_mul_right d y.isLt
  have hj'lt : y'.val * d + z'.val < c * d := by
    calc y'.val * d + z'.val < y'.val * d + d := by omega
      _ = (y'.val + 1) * d := by ring
      _ ≤ c * d := Nat.mul_le_mul_right d y'.isLt
  have e0 : k.val % (a * (b * d)) = x.val * (b * d) + (y.val * d + z.val) := by
    rw [hk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by
      calc x.val * (b * d) + (y.val * d + z.val) < x.val * (b * d) + b * d := by omega
        _ = (x.val + 1) * (b * d) := by ring
        _ ≤ a * (b * d) := Nat.mul_le_mul_right (b * d) x.isLt)]
  have e1 : (k.val % (a * (b * d))) / (b * d) = x.val := by
    rw [e0, Nat.add_comm (x.val * (b * d)), Nat.add_mul_div_right _ _ (by positivity),
      Nat.div_eq_of_lt hjlt, Nat.zero_add]
  have e2 : k.val % d = z.val := by
    have hk' : k.val = z.val + d * (x.val * b + y.val + a * b *
        (bif ε then 1 else 0)) := by
      rw [hk]; ring
    rw [hk', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt z.isLt]
  have e3 : j.val / (c * d) = x'.val := by
    rw [hj, Nat.add_comm (x'.val * (c * d)), Nat.add_mul_div_right _ _ (by positivity),
      Nat.div_eq_of_lt hj'lt, Nat.zero_add]
  have e4 : j.val % d = z'.val := by
    have hj' : j.val = z'.val + d * (x'.val * c + y'.val) := by rw [hj]; ring
    rw [hj', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt z'.isLt]
  rw [e1, e2, e3, e4]
  unfold repeatFst SG
  simp only [Matrix.of_apply, Fin.ext_iff]

/-- **Lemma 2, flat version.** `P_π · [S_π ; S_π] = S_π̄`, genuinely as `Fin`-indexed
matrices, obtained from the abstract `Pperm_mul_repeatFst` purely by reindexing
(`Matrix.submatrix_mul_equiv`) along the shared identification `finChainEquivStack`. -/
theorem Pperm_mul_repeatFst_flat (a b c d : ℕ) :
    (PpermF a b d : Matrix _ _ R) * repeatFstFlat a b c d =
      Matrix.submatrix (SG (A := Fin a) (B := Bool × Fin b) (C := Fin c) (D := Fin d))
        (finChainEquiv' a b d).symm (finChainEquiv a c d).symm := by
  unfold PpermF repeatFstFlat
  rw [Matrix.submatrix_mul_equiv, Pperm_mul_repeatFst]

/-- The flat version of `SG_transpose`: `S_(a,b,c,d)ᵀ = S_(a,c,b,d)`. -/
theorem SF_transpose (a b c d : ℕ) : (SF a b c d : Matrix _ _ R)ᵀ = SF a c b d := by
  unfold SF
  rw [Matrix.transpose_submatrix, SG_transpose]

/-- **The explicit formula for `PpermF`.** `PpermF a b d` is exactly the permutation matrix of
`Prop1.rho b d (a*(b*d))`: this is the identity that connects the *matrix* `PpermF` (built from
the commutation matrix, `RealKSFLean.Paper.Lemma1`/`RealKSFLean.Paper.Lemma2`) to the *arithmetic*
permutation `rho` used to state Proposition 1. -/
theorem PpermF_apply (a b d : ℕ) (hb : 0 < b) (hd0 : 0 < d)
    (i : Fin (a * (2 * b * d))) (k : Fin (2 * (a * (b * d)))) :
    (PpermF a b d : Matrix _ _ R) i k =
      if i.val = Prop1.rho b d (a * (b * d)) k.val then 1 else 0 := by
  have hbd0 : 0 < b * d := by positivity
  unfold PpermF
  rw [Matrix.submatrix_apply, Pperm_apply]
  rcases hik : (finChainEquiv' a b d).symm i with ⟨x', ⟨ε', y'⟩, z'⟩
  rcases hkk : (finChainEquivStack a b d).symm k with ⟨ε, x, y, z⟩
  have hi : i.val = x'.val * (2 * b * d) + (y'.val * d + z'.val) + (b * d) *
      (bif ε' then 1 else 0) := by
    conv_lhs => rw [← Equiv.apply_symm_apply (finChainEquiv' a b d) i, hik]
    rw [finChainEquiv'_apply_val]
  have hk : k.val = x.val * (b * d) + (y.val * d + z.val) + (a * (b * d)) *
      (bif ε then 1 else 0) := by
    conv_lhs => rw [← Equiv.apply_symm_apply (finChainEquivStack a b d) k, hkk]
    rw [finChainEquivStack_apply_val]
  have ha : 0 < a := by have := x.isLt; omega
  have habd0 : 0 < a * (b * d) := by positivity
  have hjlt : y.val * d + z.val < b * d := by
    calc y.val * d + z.val < y.val * d + d := by omega
      _ = (y.val + 1) * d := by ring
      _ ≤ b * d := Nat.mul_le_mul_right d y.isLt
  have hxlt : x.val * (b * d) + (y.val * d + z.val) < a * (b * d) := by
    calc x.val * (b * d) + (y.val * d + z.val) < x.val * (b * d) + b * d := by omega
      _ = (x.val + 1) * (b * d) := by ring
      _ ≤ a * (b * d) := Nat.mul_le_mul_right (b * d) x.isLt
  have hrho : Prop1.rho b d (a * (b * d)) k.val =
      x.val * (2 * b * d) + (y.val * d + z.val) + (b * d) * (bif ε then 1 else 0) := by
    have e1 : k.val % (a * (b * d)) = x.val * (b * d) + (y.val * d + z.val) := by
      rw [hk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hxlt]
    have e2 : k.val / (a * (b * d)) = bif ε then 1 else 0 := by
      rw [hk, Nat.add_mul_div_left _ _ habd0, Nat.div_eq_of_lt hxlt, Nat.zero_add]
    have e3 : (x.val * (b * d) + (y.val * d + z.val)) / (b * d) = x.val := by
      rw [Nat.add_comm (x.val * (b * d)), Nat.add_mul_div_right _ _ hbd0,
        Nat.div_eq_of_lt hjlt, Nat.zero_add]
    have e4 : k.val % (b * d) = y.val * d + z.val := by
      have hk' : k.val = (y.val * d + z.val) + (b * d) * (x.val + a * (bif ε then 1 else 0)) := by
        rw [hk]; ring
      rw [hk', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hjlt]
    unfold Prop1.rho
    rw [e1, e2, e3, e4]
    ring
  rw [hi, hrho]
  have hiff : ((ε, x, y, z) = (ε', x', y', z')) ↔
      (x'.val * (2 * b * d) + (y'.val * d + z'.val) + b * d * (bif ε' then 1 else 0) =
        x.val * (2 * b * d) + (y.val * d + z.val) + b * d * (bif ε then 1 else 0)) := by
    constructor
    · intro heq
      obtain ⟨e1, e2, e3, e4⟩ : ε = ε' ∧ x = x' ∧ y = y' ∧ z = z' := by
        simpa [Prod.ext_iff] using heq
      rw [e1, e2, e3, e4]
    · intro hval
      have hival : i = finChainEquiv' a b d (x, (ε, y), z) := by
        apply Fin.ext
        rw [finChainEquiv'_apply_val]
        omega
      have hival' : i = finChainEquiv' a b d (x', (ε', y'), z') := by
        rw [← hik, Equiv.apply_symm_apply]
      have heq := (finChainEquiv' a b d).injective (hival'.symm.trans hival)
      obtain ⟨e1, e2, e3, e4⟩ : x' = x ∧ ε' = ε ∧ y' = y ∧ z' = z := by
        simpa [Prod.ext_iff, and_assoc] using heq
      simp [e1, e2, e3, e4]
  exact if_congr hiff rfl rfl

/-- **`rhoEquiv` at the value level.** Combining `PpermF_eq_submatrix_one` and `PpermF_apply`:
`rhoEquiv` sends `k` to `i` exactly when `i.val = Prop1.rho b d (a*(b*d)) k.val`. -/
theorem rhoEquiv_apply_eq_iff (a b d : ℕ) (hb : 0 < b) (hd0 : 0 < d)
    (i : Fin (a * (2 * b * d))) (k : Fin (2 * (a * (b * d)))) :
    rhoEquiv a b d k = i ↔ i.val = Prop1.rho b d (a * (b * d)) k.val := by
  have h1 : (PpermF a b d : Matrix _ _ ℕ) i k = if rhoEquiv a b d k = i then 1 else 0 := by
    conv_lhs => rw [PpermF_eq_submatrix_one]
    rw [Matrix.submatrix_apply, Matrix.one_apply, id]
    exact if_congr eq_comm rfl rfl
  rw [PpermF_apply (R := ℕ) a b d hb hd0] at h1
  by_cases h : rhoEquiv a b d k = i <;> by_cases h' : i.val = Prop1.rho b d (a * (b * d)) k.val <;>
    simp_all

@[simp] theorem sumToFinEquiv_apply_inl_val (N : ℕ) (x : Fin N) :
    (sumToFinEquiv N (Sum.inl x)).val = x.val := by
  simp [sumToFinEquiv]

@[simp] theorem sumToFinEquiv_apply_inr_val (N : ℕ) (x : Fin N) :
    (sumToFinEquiv N (Sum.inr x)).val = N + x.val := by
  simp [sumToFinEquiv, Nat.add_comm]

/-- `IsKSparseFlat`, in terms of `SF`'s own explicit support formula: `K`'s support is included
in `SF a b c d`'s support pattern. -/
theorem isKSparseFlat_iff_SF (a b c d : ℕ) (hb : 0 < b) (hc : 0 < c) (hd0 : 0 < d)
    (K : Matrix (Fin (a * (b * d))) (Fin (a * (c * d))) R) :
    IsKSparseFlat a b c d K ↔ ∀ i j, (SF a b c d : Matrix _ _ ℕ) i j = 0 → K i j = 0 := by
  unfold IsKSparseFlat
  simp_rw [SF_apply a b c d hb hc hd0]
  constructor
  · intro h i j hij
    apply h
    by_contra hcon
    push Not at hcon
    simp [hcon.1, hcon.2] at hij
  · intro h i j hij
    apply h
    have : ¬ (i.val / (b * d) = j.val / (c * d) ∧ i.val % d = j.val % d) := by tauto
    simp [this]

/-- **The bridge to `IsKSparse`.** `IsKSparseFlat` is exactly `IsKSparse` transported along the
mixed-radix identification `finChainEquiv`, i.e. Definition 1's literal `Fin a × Fin b × Fin d`
picture. -/
theorem isKSparse_submatrix_finChainEquiv_iff (a b c d : ℕ) (hb : 0 < b) (hc : 0 < c)
    (hd0 : 0 < d) (K : Matrix (Fin (a * (b * d))) (Fin (a * (c * d))) R) :
    IsKSparse a b c d (K.submatrix (finChainEquiv a b d) (finChainEquiv a c d)) ↔
      IsKSparseFlat a b c d K := by
  have key : ∀ (x : Fin a × Fin b × Fin d) (y : Fin a × Fin c × Fin d),
      (finChainEquiv a b d x).val / (b * d) = x.1.val ∧
        (finChainEquiv a b d x).val % d = x.2.2.val ∧
      (finChainEquiv a c d y).val / (c * d) = y.1.val ∧
        (finChainEquiv a c d y).val % d = y.2.2.val := by
    rintro ⟨x1, x2, x3⟩ ⟨y1, y2, y3⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [finChainEquiv_apply_val, Nat.add_comm (x1.val * (b * d)),
        Nat.add_mul_div_right _ _ (by positivity : (0:ℕ) < b * d),
        Nat.div_eq_of_lt (show x2.val * d + x3.val < b * d by
          calc x2.val * d + x3.val < x2.val * d + d := by omega
            _ = (x2.val + 1) * d := by ring
            _ ≤ b * d := Nat.mul_le_mul_right d x2.isLt), Nat.zero_add]
    · rw [finChainEquiv_apply_val]
      have h : x1.val * (b * d) + (x2.val * d + x3.val) = x3.val + d * (x1.val * b + x2.val) := by
        ring
      rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt x3.isLt]
    · rw [finChainEquiv_apply_val, Nat.add_comm (y1.val * (c * d)),
        Nat.add_mul_div_right _ _ (by positivity : (0:ℕ) < c * d),
        Nat.div_eq_of_lt (show y2.val * d + y3.val < c * d by
          calc y2.val * d + y3.val < y2.val * d + d := by omega
            _ = (y2.val + 1) * d := by ring
            _ ≤ c * d := Nat.mul_le_mul_right d y2.isLt), Nat.zero_add]
    · rw [finChainEquiv_apply_val]
      have h : y1.val * (c * d) + (y2.val * d + y3.val) = y3.val + d * (y1.val * c + y2.val) := by
        ring
      rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt y3.isLt]
  unfold IsKSparse IsKSparseFlat
  constructor
  · intro h i j hij
    have hi := (finChainEquiv a b d).apply_symm_apply i
    have hj := (finChainEquiv a c d).apply_symm_apply j
    obtain ⟨e1, e2, e3, e4⟩ := key ((finChainEquiv a b d).symm i) ((finChainEquiv a c d).symm j)
    rw [hi] at e1 e2
    rw [hj] at e3 e4
    have hcond : ((finChainEquiv a b d).symm i).1 ≠ ((finChainEquiv a c d).symm j).1 ∨
        ((finChainEquiv a b d).symm i).2.2 ≠ ((finChainEquiv a c d).symm j).2.2 := by
      rw [e1, e2, e3, e4] at hij
      rcases hij with h' | h'
      · left; exact fun hc => h' (congrArg Fin.val hc)
      · right; exact fun hc => h' (congrArg Fin.val hc)
    have := h ((finChainEquiv a b d).symm i) ((finChainEquiv a c d).symm j) hcond
    rwa [Matrix.submatrix_apply, hi, hj] at this
  · intro h x y hxy
    obtain ⟨e1, e2, e3, e4⟩ := key x y
    have hcond : (finChainEquiv a b d x).val / (b * d) ≠ (finChainEquiv a c d y).val / (c * d) ∨
        (finChainEquiv a b d x).val % d ≠ (finChainEquiv a c d y).val % d := by
      rw [e1, e2, e3, e4]
      rcases hxy with h' | h'
      · left; exact fun hc => h' (Fin.ext hc)
      · right; exact fun hc => h' (Fin.ext hc)
    exact h (finChainEquiv a b d x) (finChainEquiv a c d y) hcond
