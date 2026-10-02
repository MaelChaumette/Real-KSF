import RealKSFLean.Paper.Definition1
import RealKSFLean.Paper.Definition2
import RealKSFLean.Paper.Equation8
import RealKSFLean.Paper.Lemma1
import RealKSFLean.Paper.Lemma2
import RealKSFLean.Paper.RealPart
import RealKSFLean.Paper.RealPartChain
import RealKSFLean.Paper.Proposition1
import RealKSFLean.Paper.Proposition1Architecture
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

/-! ## `Definition1.lean` -/

#print axioms IsKSparse.map
#print axioms IsKSparse.re
#print axioms IsKSparse.im
#print axioms IsKSparse.smul

/-! ## `Definition2.lean` -/

#print axioms commutationMatrix_mulVec_vec

/-! ## `Equation8.lean` -/

#print axioms commutationMatrix_mul_repeatFst

/-! ## `Lemma1.lean` -/

#print axioms Pperm_mul_repeatFst

/-! ## `Lemma2.lean` -/

#print axioms lemma2_core
#print axioms lemma2_first

/-! ## `RealPart.lean` -/

#print axioms re_mul
#print axioms im_mul

/-! ## `RealPartChain.lean` (equation (1), imaginary part) -/

#print axioms chain_re_im
#print axioms chain_re
#print axioms chain_im
#print axioms Kprod_scaleFirst
#print axioms im_Kprod_eq_re_scaleFirst

/-! ## `Proposition1.lean` -/

#print axioms Prop1.sufficiency
#print axioms Prop1.necessity
#print axioms Prop1.prop1_core
#print axioms Prop1.condition10_iff_conditions
#print axioms Prop1.conditions_condition10

/-! ## `Proposition1Architecture.lean` -/

#print axioms re_Kprod_eq_KtildeProd
#print axioms ktilde_zero_isKSparse
#print axioms ktilde_succ_isKSparse
#print axioms ktilde_last_isKSparse
#print axioms conditions_of_ktilde_zero
#print axioms conditions_of_ktilde_succ
#print axioms proposition1

/-! ## `Corollary1.lean` -/

#print axioms chainable_conditions
#print axioms corollary1
