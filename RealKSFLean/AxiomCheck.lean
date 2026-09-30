import RealKSFLean.Paper.Lemma1
import RealKSFLean.Paper.Definition1
import RealKSFLean.Paper.Lemma2
import RealKSFLean.Paper.Lemma3
import RealKSFLean.Paper.RealPart
import RealKSFLean.Paper.RealPartChain
import RealKSFLean.Paper.Proposition1
import RealKSFLean.Paper.Corollary1

/-!
# Axiom audit for every result in `RealKSFLean.Paper`

This file is not a proof of anything: it runs `#print axioms` on every single theorem stated in
`RealKSFLean/Paper/*.lean` (i.e. every formalized statement of the paper), so that a reader — or CI
— can see in one place that none of them relies on a `sorry` (which would show up as the axiom
`sorryAx`) or on any axiom beyond the three Mathlib itself is built on:

* `Classical.choice` (excluded middle / choice, used pervasively in Mathlib);
* `Quot.sound` (quotient types, part of Lean's own kernel);
* `propext` (propositional extensionality).

If a future edit accidentally introduces a `sorry` or an extra axiom anywhere in the dependency
chain of a paper result, the corresponding line below will start printing `sorryAx` (or the
extra axiom's name) the next time this file is built.
-/

open Prop1

/-! ## `Lemma1.lean` -/

#print axioms commutationMatrix_mul_repeatFst

/-! ## `Definition1.lean` -/

#print axioms IsKSparse.map
#print axioms IsKSparse.re
#print axioms IsKSparse.im

/-! ## `Lemma2.lean` -/

#print axioms Pperm_mul_repeatFst

/-! ## `Lemma3.lean` -/

#print axioms lemma3_core

/-! ## `RealPart.lean` (equations (1)–(2)) -/

#print axioms re_mul
#print axioms im_mul

/-! ## `RealPartChain.lean` (equation (3), Remark 2) -/

#print axioms chain_re_im
#print axioms chain_re
#print axioms chain_im

/-! ## `Proposition1.lean` -/

#print axioms Prop1.sufficiency
#print axioms Prop1.necessity
#print axioms Prop1.prop1_core
#print axioms Prop1.chainable_condition10

/-! ## `Corollary1.lean` -/

#print axioms re_Kprod_eq_KtildeProd
#print axioms ktilde_zero_isKSparse
#print axioms ktilde_succ_isKSparse
