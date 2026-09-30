import Test.Definitions

/-!
# Proposition 1's elementary arithmetic helpers

Two small, purely arithmetic lemmas used repeatedly inside the proofs of `sufficiency` and
`necessity` (`Test.Paper.Proposition1`): `divModEq` reads off a quotient and remainder from a
mixed-radix decomposition without re-deriving division facts by hand each time, and
`dvd_mod_zero` is the trivial "divisibility means zero remainder" fact. Neither is stated in the
paper — they are generic `Nat` bookkeeping.
-/

namespace Prop1

/-- Elementary uniqueness of Euclidean division: if `X = Y * Q + R` with `R < Y`, then `Q` and
`R` are exactly the quotient and remainder of `X` by `Y`. -/
theorem divModEq {X Y Q R : ℕ} (hY : 0 < Y) (hR : R < Y) (h : X = Y * Q + R) :
    X / Y = Q ∧ X % Y = R := by
  subst h
  rw [Nat.add_comm]
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_div_left R Q hY, Nat.div_eq_of_lt hR, Nat.zero_add]
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hR]

theorem dvd_mod_zero {d N : ℕ} (h : d ∣ N) : N % d = 0 := by
  obtain ⟨k, hk⟩ := h; rw [hk]; exact Nat.mul_mod_right d k

end Prop1
