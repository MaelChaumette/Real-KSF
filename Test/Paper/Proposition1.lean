import Test.Definitions
import Test.Support.Proposition1Aux

/-!
# Proposition 1: the necessary and sufficient condition C1, C2, C3

This file formalizes the arithmetic core of **Proposition 1**: given two consecutive chains
`π = (a, b, c, d)` and `π' = (a', b', c', d')` with `a * c * d = a' * b' * d'` (condition
**C1**), the permutation `P_{π'}` satisfies equation (10) — and hence, via
`Test.Paper.Lemma3.lemma3_core`, equations (6)/(7) — if and only if

* **C2**: `a * c / a' = b' * d' / d ∈ ℕ` (`∃ r, a * c = a' * r ∧ b' * d' = d * r`);
* **C3**: `a ∣ a'`.

## The precise form of condition (10)

Equation (10) (`P_{π'} · [S_(a,c,b',d) ; S_(a,c,b',d)] = S_(a,2c,b',d)`) is a matrix equation
between `{0,1}`-matrices whose entries only depend on the *outer* (`a`) and *inner* (`d`)
coordinates of their row (this is how `SG` is built, `Test.Definitions`). Consequently — this is
exactly the paper's equation (11), reached by restricting attention to the rows sharing a given
outer/inner coordinate pair `(i, k2)` — condition (10) is equivalent to a purely arithmetic
statement about the flat permutation

`ρ n := 2 * (b'*d') * ((n % N) / (b'*d')) + (b'*d') * (n / N) + n % (b'*d')`

of `Fin (2 * N)` (`N := a * c * d = a' * b' * d'`; this is the formula for `P_{π'}` unfolded via
`finProdFinEquiv`/`finTwoEquiv`, see `Test.Support.FlatChain`): it must send the "label"
`((n % N) / (c*d), n % d)` — which of the `a * d` blocks of the *stacked* `(a,c,d)`-grouping
`n` belongs to — to the label `(m / (2*c*d), m % d)` — which block of the *doubled*
`(a,2c,d)`-grouping `m = ρ n` belongs to — for every `n < 2 * N`. This is `Prop1.Condition10`
(`Test.Definitions`).

We checked this reformulation numerically against the paper's own formula, on several worked
examples, before proving anything, to make sure no meaning was lost in translation: e.g. for
`a=2, c=2, d=1, a'=4, b'=1, d'=1` (satisfying C1–C3 with `p = 2`) the condition holds, while for
`a=2, c=3, d=1, a'=3, b'=2, d'=1` (satisfying C1, C2 but *not* C3, since `2 ∤ 3`) it fails.

The proof of both directions follows the paper's own argument almost line by line: sufficiency
decomposes `c = p * r` (`p := a'/a` from C3, `r` from C2) and computes `ρ` directly; necessity
tests the *same* two specific inputs the paper tests — `n = N` (giving C2) and `n = c * d`
(giving C3, via a proof by contradiction identical to the paper's "so `q = 0`" step). -/

namespace Prop1

set_option maxHeartbeats 1000000 in
-- The many `set`/`clear_value` local definitions used to track the mixed-radix decomposition
-- of `n` make elaboration (in particular `positivity`/`nlinarith`) slower than the default
-- budget, even though every individual step is elementary.
/-- **Sufficiency of C2 and C3** (paper's part (a)): decompose `a' = a * p` (C3) and
`c = p * r` (from C1, C3 and the `r` of C2), then compute `ρ`'s two "coordinates"
(`Nat`-division by `2cd` and remainder mod `d`) directly and check they match `label1`. -/
theorem sufficiency (a c d a' b' d' r p : ℕ)
    (ha : 0 < a) (ha' : 0 < a') (hc : 0 < c) (hd : 0 < d) (hb' : 0 < b') (hd' : 0 < d')
    (hp : a' = a * p) (hr1 : a * c = a' * r) (hr2 : b' * d' = d * r)
    (n : ℕ) (hn : n < 2 * (a * c * d)) :
    label2 c d (rho b' d' (a * c * d) n) = label1 c d (a * c * d) n := by
  have hp0 : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · exfalso; rw [h0, Nat.mul_zero] at hp; omega
    · exact h0
  have hM0 : 0 < b' * d' := by positivity
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exfalso; rw [h0, Nat.mul_zero] at hr2; omega
    · exact h0
  have hcpr : c = p * r := by
    have h1 : a * c = a * (p * r) := by rw [hr1, hp]; ring
    exact Nat.eq_of_mul_eq_mul_left ha h1
  set N := a * c * d with hNdef
  set M := b' * d' with hMdef
  have hN0 : 0 < N := by rw [hNdef]; positivity
  have hNapM : N = a * p * M := by rw [hNdef, hcpr, hr2]; ring
  have hMdvdN : M ∣ N := ⟨a * p, by rw [hNapM]; ring⟩
  have hnm : n = N * (n / N) + n % N := (Nat.div_add_mod n N).symm
  have hmltN : n % N < N := Nat.mod_lt n hN0
  set ε := n / N with hεdef
  set m := n % N with hmdef
  have hε1 : ε ≤ 1 := by
    by_contra h
    have h : 2 ≤ ε := by omega
    have h2 : N * 2 ≤ N * ε := Nat.mul_le_mul_left N h
    omega
  have hmQS : m = M * (m / M) + m % M := (Nat.div_add_mod m M).symm
  have hSltM : m % M < M := Nat.mod_lt m hM0
  set Q := m / M with hQdef
  set S := m % M with hSdef
  have hQQ1Q2 : Q = p * (Q / p) + Q % p := (Nat.div_add_mod Q p).symm
  have hQ2ltp : Q % p < p := Nat.mod_lt Q hp0
  set Q1 := Q / p with hQ1def
  set Q2 := Q % p with hQ2def
  have hnMod : n % M = S := by rw [hSdef, hmdef, ← Nat.mod_mod_of_dvd n hMdvdN]
  have hrho : rho b' d' N n = 2 * M * Q + M * ε + S := by
    change 2 * M * ((n % N) / M) + M * (n / N) + n % M = 2 * M * Q + M * ε + S
    rw [← hεdef, ← hmdef, ← hQdef, hnMod]
  clear_value N M ε m Q S Q1 Q2
  have hcd : c * d = p * M := by rw [hcpr, hr2]; ring
  have h2cd : 2 * c * d = 2 * p * M := by rw [Nat.mul_assoc, hcd, ← Nat.mul_assoc]
  have hdvdM : d ∣ M := ⟨r, hr2⟩
  have hdvdN : d ∣ N := ⟨a * c, by rw [hNdef]; ring⟩
  have goalA : rho b' d' N n % d = n % d := by
    rw [hrho]
    have e1 : 2 * M * Q + M * ε + S = S + d * (2 * r * Q + r * ε) := by rw [hr2]; ring
    rw [e1, Nat.add_mul_mod_self_left]
    have e2 : S % d = m % d := by rw [hSdef, Nat.mod_mod_of_dvd m hdvdM]
    rw [e2]
    have e3 : n = m + d * (a * c * ε) := by rw [hnm, hNdef]; ring
    rw [e3, Nat.add_mul_mod_self_left]
  have hbound : 2 * M * Q2 + M * ε + S < 2 * p * M := by
    have b1 : Q2 + 1 ≤ p := hQ2ltp
    nlinarith [hSltM, hε1]
  have hbound2 : M * Q2 + S < p * M := by
    have b1 : Q2 + 1 ≤ p := hQ2ltp
    nlinarith [hSltM]
  have goalB : rho b' d' N n / (2 * c * d) = m / (c * d) := by
    rw [hrho, h2cd, hcd]
    have e1 : 2 * M * Q + M * ε + S = (2 * p * M) * Q1 + (2 * M * Q2 + M * ε + S) := by
      rw [hQQ1Q2]; ring
    have e2 : m = (p * M) * Q1 + (M * Q2 + S) := by
      rw [hmQS, hQQ1Q2]; ring
    have h1 := divModEq (Y := 2 * p * M) (Q := Q1) (R := 2 * M * Q2 + M * ε + S)
      (by positivity) hbound e1
    have h2 := divModEq (Y := p * M) (Q := Q1) (R := M * Q2 + S)
      (by positivity) hbound2 e2
    rw [h1.1, h2.1]
  change (rho b' d' N n / (2 * c * d), rho b' d' N n % d) = ((n % N) / (c * d), n % d)
  rw [← hmdef, goalA, goalB]

set_option maxHeartbeats 1000000 in
-- Same reason as `sufficiency`: several `set`-introduced local definitions accumulate in
-- context, which slows down `positivity`/`nlinarith` below the default heartbeat budget.
/-- **Necessity of C2 and C3** (paper's part (b)): test `n = N` (equation (10) applied there
forces `d ∣ b'*d'`, i.e. C2) and, when `a ≥ 2`, `n = c * d` (forces, by contradiction exactly as
in the paper's "so `q = 0`" step, that `r ∣ c`, hence C3). -/
theorem necessity (a c d a' b' d' : ℕ)
    (ha : 0 < a) (_ha' : 0 < a') (hc : 0 < c) (hd : 0 < d) (hb' : 0 < b') (hd' : 0 < d')
    (hC1 : a * c * d = a' * b' * d')
    (hCond : Condition10 c d b' d' (a * c * d)) :
    C2 a c d a' b' d' ∧ C3 a a' := by
  set N := a * c * d with hNdef
  set M := b' * d' with hMdef
  have hN0 : 0 < N := by rw [hNdef]; positivity
  have hM0 : 0 < M := by rw [hMdef]; positivity
  have hNaM : N = a' * M := by rw [hC1, hMdef]; ring
  have hdN : d ∣ N := ⟨a * c, by rw [hNdef]; ring⟩
  have hMdN : M ∣ N := ⟨a', by rw [hNaM]; ring⟩
  -- Step 1: test n = N, derive C2
  have h1 := hCond N (by omega)
  have hl1 : label1 c d N N = (0, 0) := by
    change ((N % N) / (c * d), N % d) = (0, 0)
    rw [Nat.mod_self, Nat.zero_div, dvd_mod_zero hdN]
  have hrhoN : rho b' d' N N = M := by
    change 2 * M * ((N % N) / M) + M * (N / N) + N % M = M
    rw [Nat.mod_self, Nat.zero_div, Nat.div_self hN0, dvd_mod_zero hMdN]
    ring
  rw [hrhoN, hl1] at h1
  have hdM : d ∣ M := by
    have := (Prod.mk.injEq .. ).mp h1
    exact Nat.dvd_of_mod_eq_zero this.2
  obtain ⟨r, hr⟩ := hdM
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exfalso; rw [h0, Nat.mul_zero] at hr; omega
    · exact h0
  have hC2r : a * c = a' * r := by
    have e1 : a * c * d = a' * r * d := by rw [← hNdef, hNaM, hr]; ring
    exact Nat.eq_of_mul_eq_mul_right hd e1
  refine ⟨⟨r, hC2r, hr⟩, ?_⟩
  -- Step 2: derive C3
  rcases Nat.lt_or_ge a 2 with ha1 | ha2
  · have : a = 1 := by omega
    rw [this]; exact one_dvd a'
  · -- a ≥ 2
    set p := c / r with hpdef
    set q := c % r with hqdef
    have hcpq : c = r * p + q := (Nat.div_add_mod c r).symm
    have hqltr : q < r := Nat.mod_lt c hr0
    have hcdltN : c * d < N := by
      rw [hNdef]; calc c * d < a * (c * d) := by nlinarith
        _ = a * c * d := by ring
    have h2 := hCond (c * d) (by omega)
    have hl2 : label1 c d N (c * d) = (1, 0) := by
      change ((c * d % N) / (c * d), c * d % d) = (1, 0)
      rw [Nat.mod_eq_of_lt hcdltN, Nat.div_self (by positivity : 0 < c * d),
        Nat.mul_mod_left]
    have hcdM : c * d = M * p + q * d := by rw [hcpq, hr]; ring
    have hqdltM : q * d < M := by
      rw [hr]; nlinarith [hqltr]
    have hcddiv := divModEq hM0 hqdltM hcdM
    have hrhocd : rho b' d' N (c * d) = 2 * M * p + q * d := by
      change 2 * M * ((c * d % N) / M) + M * (c * d / N) + c * d % M = 2 * M * p + q * d
      rw [Nat.mod_eq_of_lt hcdltN, Nat.div_eq_of_lt hcdltN, hcddiv.1, hcddiv.2]
      ring
    rw [hrhocd, hl2] at h2
    have hfirst : (2 * M * p + q * d) / (2 * c * d) = 1 := (Prod.mk.injEq .. ).mp h2 |>.1
    have hq0 : q = 0 := by
      by_contra hqne
      have hqpos : 0 < q := Nat.pos_of_ne_zero hqne
      have h2cd : 2 * c * d = 2 * M * p + 2 * q * d := by
        rw [show (2 : ℕ) * c * d = 2 * (c * d) from by ring, hcdM]; ring
      have hlt : 2 * M * p + q * d < 2 * c * d := by rw [h2cd]; nlinarith
      have : (2 * M * p + q * d) / (2 * c * d) = 0 := Nat.div_eq_of_lt hlt
      omega
    have hcrp : c = r * p := by rw [hcpq, hq0]; ring
    have hap : a * p = a' := by
      have e1 : a * (r * p) = a' * r := by rw [← hcrp]; exact hC2r
      have e2 : a * p * r = a' * r := by rw [← e1]; ring
      exact Nat.eq_of_mul_eq_mul_right hr0 e2
    exact ⟨p, hap.symm⟩

/-- **Proposition 1**, arithmetic core: given `C1` (`a*c*d = a'*b'*d'`), equation (10) holds if
and only if `C2 ∧ C3`. -/
theorem prop1_core (a c d a' b' d' : ℕ)
    (ha : 0 < a) (ha' : 0 < a') (hc : 0 < c) (hd : 0 < d) (hb' : 0 < b') (hd' : 0 < d')
    (hC1 : a * c * d = a' * b' * d') :
    Condition10 c d b' d' (a * c * d) ↔ C2 a c d a' b' d' ∧ C3 a a' := by
  refine ⟨necessity a c d a' b' d' ha ha' hc hd hb' hd' hC1,
    fun ⟨⟨r, hr1, hr2⟩, p, hp⟩ n hn =>
      sufficiency a c d a' b' d' r p ha ha' hc hd hb' hd' hp hr1 hr2 n hn⟩

/-- **Corollary 1** (pairwise form, [3, Def. 4.12] ⟹ Proposition 1's hypotheses). A chainable
pair of chains satisfies C1, C2 and C3, hence condition (10) holds — and, via
`Test.Paper.Lemma3.lemma3_core`, so do equations (6)/(7): the real part of the product is
Kronecker-sparse across this junction. This is the *pairwise* statement, which is the actual
arithmetic content: `C1` follows from `C2` alone (`Chainable2.c1`, `Test.Definitions`), so
chainability's own `C2`- and `C3`-parts already give exactly what `prop1_core` needs. The
architecture-level statement ("every junction of a chainable architecture") is this pairwise
fact applied at each junction, with no new arithmetic content — see
`Test.Paper.Corollary1` for the final assembly this feeds into. -/
theorem chainable_condition10 (a c d a' b' d' : ℕ)
    (ha : 0 < a) (ha' : 0 < a') (hc : 0 < c) (hd : 0 < d) (hb' : 0 < b') (hd' : 0 < d')
    (h : Chainable2 a c d a' b' d') :
    Condition10 c d b' d' (a * c * d) :=
  (prop1_core a c d a' b' d' ha ha' hc hd hb' hd' h.c1).mpr ⟨h.c2, h.c3⟩

end Prop1
