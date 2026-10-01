# Kronecker-Sparse Factorizations — Lean 4 Formalization

![status: proved](https://img.shields.io/static/v1?label=status&message=proved&color=0f8f88&style=flat-square)
![Lean: 4.32.0](https://img.shields.io/static/v1?label=Lean&message=4.32.0&color=6b4fbb&style=flat-square)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)

A [Lean 4](https://leanprover.github.io/) / [Mathlib](https://leanprover-community.github.io/mathlib4_docs/)
formalization of the results of

> Maël Chaumette, Rémi Gribonval, Elisa Riccietti,
> *"On the Real Part of Butterfly Factorizations, with Application to Fast Transforms."*
> <!-- TODO: add venue / year / arXiv or DOI link once available -->

The paper studies **butterfly factorizations** — products of Kronecker-sparse factors, i.e. matrices whose supports follow a Kronecker pattern $\mathbf{I}_a ⊗ \mathbf{1}_{b×c} ⊗ \mathbf{I}_d$ — and shows that if a complex matrix $\mathbf{A}$ admits a butterfly factorization whose architecture satisfies three explicit conditions C1–C3 (in particular, any *chainable architecture* [[1, Definition 4.12]](#1)), then its real part $\mathrm{Re}(\mathbf{A})$ also admits an explicit butterfly factorization, doubling the row/column spaces along the way. The imaginary part, and more generally $\mathrm{Re}(z\mathbf{A})$, follows since $\mathrm{Im}(\mathbf{K}_1\cdots\mathbf{K}_L) = \mathrm{Re}((-\jmath\mathbf{K}_1)\cdots\mathbf{K}_L)$.

This repository formalizes the numbered statements of the paper (Definitions 1–2, equations (1)–(10), Lemmas 1–2, Proposition 1, Corollary 1) as machine-checked Lean theorems, with **no `sorry` and no additional axioms** beyond what Mathlib itself uses.

## Project layout

The project is split into three parts, so that a reader can tell at a glance which Lean declarations *are* the paper's results and which ones are bridging work needed to state them:

```
RealKSFLean.lean             — table of contents (this project's own front page, no imports)
RealKSFLean/Definitions.lean — every def/structure used anywhere below, in one place
RealKSFLean/Paper/           — the paper's results, proved exactly as stated
RealKSFLean/Support/         — bridging lemmas needed along the way, not stated in the paper
```

| Directory | Contents |
|---|---|
| [`RealKSFLean/Definitions.lean`](RealKSFLean/Definitions.lean) | Kronecker-sparse factors (`IsKSparse`), the commutation matrix (`commutationMatrix`), the permutation `P_π` (`Pperm`), the real/imaginary doubling `Kbar`/`Kbarprod`, `scaleFirst`, `ksWitness`, the arithmetic of Proposition 1 (`Prop1.rho`, `Condition10`, `C1`/`C2`/`C3`, `Conditions`, `Chainable2`), and the flat/telescoping objects (`Kflat`, `Pfor`, `Ktilde`, `KtildeProd`) used to assemble Proposition 1 at the architecture level. |
| [`RealKSFLean/Paper/`](RealKSFLean/Paper) | `Definition1.lean`, `Definition2.lean`, `RealPart.lean`, `RealPartChain.lean`, `Equation8.lean`, `Lemma1.lean`, `Lemma2.lean`, `Proposition1.lean`, `Proposition1Architecture.lean`, `Corollary1.lean` — one file per paper statement (or tight group of statements). |
| [`RealKSFLean/Support/`](RealKSFLean/Support) | `Lemma2Aux.lean`, `Permutation.lean`, `FlatChain.lean`, `Proposition1Aux.lean`, `Assembly.lean`, `ChainAssembly.lean`, `ChainSparse.lean`, `Necessity.lean` — reindexings between the abstract, `Bool×`-typed, and flat `Fin`-indexed pictures, orthogonality of permutation matrices, and the telescoping construction of `K̃_ℓ`. |

## Correspondence with the paper

| Paper statement | Lean declaration | File |
|---|---|---|
| Definition 1 (Kronecker-sparse factor of pattern `π`) | `IsKSparse` | [`RealKSFLean/Definitions.lean`](RealKSFLean/Definitions.lean) |
| Section III-A, `L = 1` (real/imaginary parts keep the pattern) | `IsKSparse.re`, `IsKSparse.im` | [`RealKSFLean/Paper/Definition1.lean`](RealKSFLean/Paper/Definition1.lean) |
| Section III-A, `L = 2` (linear algebra behind (1)) | `re_mul`, `im_mul` | [`RealKSFLean/Paper/RealPart.lean`](RealKSFLean/Paper/RealPart.lean) |
| Equation (1) (pre-factorization of `Re(A)`) | `chain_re` (and `chain_im` for `Im`) | [`RealKSFLean/Paper/RealPartChain.lean`](RealKSFLean/Paper/RealPartChain.lean) |
| Equations (2)–(3) (permuted factors `K̃_ℓ`, patterns `π'_ℓ`) | `Ktilde`, `KtildeProd` | [`RealKSFLean/Definitions.lean`](RealKSFLean/Definitions.lean) |
| Definition 2 (commutation matrix) | `commutationMatrix`, `commutationMatrix_mulVec_vec` | [`RealKSFLean/Paper/Definition2.lean`](RealKSFLean/Paper/Definition2.lean) |
| Equation (7) (`P_π := C_{a,2} ⊗ I_{bd}`) | `Pperm`, `PpermF` | [`RealKSFLean/Definitions.lean`](RealKSFLean/Definitions.lean) |
| Equation (8) | `commutationMatrix_mul_repeatFst` | [`RealKSFLean/Paper/Equation8.lean`](RealKSFLean/Paper/Equation8.lean) |
| Lemma 1 | `Pperm_mul_repeatFst` | [`RealKSFLean/Paper/Lemma1.lean`](RealKSFLean/Paper/Lemma1.lean) |
| Lemma 2 ((4) ⟺ (9) for `ℓ = 1`, (5) ⟺ (9) otherwise) | `lemma2_first`, `lemma2_core` | [`RealKSFLean/Paper/Lemma2.lean`](RealKSFLean/Paper/Lemma2.lean) |
| Equations (9)/(10) (matrix and row-permutation forms) | `Prop1.Condition10`, `matrix_iff_condition10` | [`RealKSFLean/Definitions.lean`](RealKSFLean/Definitions.lean), [`RealKSFLean/Support/Assembly.lean`](RealKSFLean/Support/Assembly.lean) |
| Proposition 1 (one junction: (9) ⟺ C2 ∧ C3 under C1) | `Prop1.prop1_core`, `Prop1.condition10_iff_conditions`, `matrix_iff_C2_C3` | [`RealKSFLean/Paper/Proposition1.lean`](RealKSFLean/Paper/Proposition1.lean), [`RealKSFLean/Support/Assembly.lean`](RealKSFLean/Support/Assembly.lean) |
| Proposition 1 (C2 ∧ C3 at every junction ⟺ every `K̃_ℓ ∈ 𝒦_{π'_ℓ}`, under C1) | `proposition1` | [`RealKSFLean/Paper/Proposition1Architecture.lean`](RealKSFLean/Paper/Proposition1Architecture.lean) |
| Proposition 1 (C1–C3 ⟹ `Re(A) = K̃_1 ⋯ K̃_L`) | `re_Kprod_eq_KtildeProd` | [`RealKSFLean/Paper/Proposition1Architecture.lean`](RealKSFLean/Paper/Proposition1Architecture.lean) |
| Proposition 1, sufficiency (C1–C3 ⟹ `K̃_ℓ ∈ 𝒦_{π'_ℓ}`) | `ktilde_zero_isKSparse`, `ktilde_succ_isKSparse`, `ktilde_last_isKSparse` | [`RealKSFLean/Paper/Proposition1Architecture.lean`](RealKSFLean/Paper/Proposition1Architecture.lean) |
| Proposition 1, necessity (`K̃_ℓ ∈ 𝒦_{π'_ℓ}` ⟹ C2 ∧ C3) | `conditions_of_ktilde_zero`, `conditions_of_ktilde_succ` | [`RealKSFLean/Paper/Proposition1Architecture.lean`](RealKSFLean/Paper/Proposition1Architecture.lean) |
| Corollary 1 (chainable architectures) | `chainable_conditions`, `corollary1` | [`RealKSFLean/Paper/Corollary1.lean`](RealKSFLean/Paper/Corollary1.lean) |
| Section III-D (imaginary part, `Re(zA)`) | `Kprod_scaleFirst`, `im_Kprod_eq_re_scaleFirst`, `IsKSparse.smul` | [`RealKSFLean/Paper/RealPartChain.lean`](RealKSFLean/Paper/RealPartChain.lean), [`RealKSFLean/Paper/Definition1.lean`](RealKSFLean/Paper/Definition1.lean) |

Both directions of Proposition 1 are formalized at the level of the permuted factors
(`proposition1`). The "only if" direction tests the Kronecker-sparse factors
`K_ℓ := (1 + 𝚥) S_{π_ℓ}` (`ksWitness`): if their permuted factors `K̃_ℓ` lie in `𝒦_{π'_ℓ}`, then
equation (10) holds at every junction, hence C2 ∧ C3.

Reading order for the mathematics: `Definition1 → RealPart → RealPartChain → Definition2 →
Equation8 → Lemma1 → Lemma2 → Proposition1 → Proposition1Architecture → Corollary1`. Every `RealKSFLean/Paper/*.lean` file starts with a
docstring explaining the statement it formalizes and how its proof is organized; consult the
matching `RealKSFLean/Support/*.lean` file for the proofs of any technical lemma it relies on that is
not itself part of the paper.

## Building

This project uses [Lean 4](https://leanprover.github.io/) and
[Mathlib](https://leanprover-community.github.io/mathlib4_docs/), managed through
[`elan`](https://github.com/leanprover/elan) and [`lake`](https://github.com/leanprover/lake).
The exact toolchain is pinned in [`lean-toolchain`](lean-toolchain); `elan` will fetch it
automatically.

```sh
# clone the repository
git clone https://github.com/<owner>/<repo>.git
cd <repo>

# fetch a prebuilt Mathlib cache instead of rebuilding it from source (fast)
lake exe cache get

# build everything (RealKSFLean.Definitions, RealKSFLean.Paper.*, RealKSFLean.Support.*)
lake build
```

A clean `lake build` produces **zero errors, zero warnings, and zero `sorry`s**.

### Browsing the documentation

CI ([`lean_action_ci.yml`](.github/workflows/lean_action_ci.yml)) builds the project on every
push. To generate hoverable HTML documentation locally with
[`doc-gen4`](https://github.com/leanprover/doc-gen4), add it as a dev dependency
(`lake add doc-gen4 --dev`) and run `lake -R -Kenv=dev build RealKSFLean:docs`.

## Status

* **No `sorry`**, anywhere in the project.
* **No custom axioms**: every theorem's proof term only relies on the axioms Mathlib itself
  uses (`Classical.choice`, `Quot.sound`, `propext`). This is checked, not just asserted:
  [`RealKSFLean/AxiomCheck.lean`](RealKSFLean/AxiomCheck.lean) runs `#print axioms` on every single theorem in
  `RealKSFLean/Paper/` and is built as part of `lake build` — a `sorry` anywhere in a paper result's
  dependency chain would make the corresponding line print `sorryAx` instead.
* Built against Mathlib `v4.34.0-rc2` (see [`lakefile.toml`](lakefile.toml)).

## Citing

If you use this formalization, please cite the paper it formalizes (see
[`CITATION.cff`](CITATION.cff)) and, if relevant, this repository itself.

## License

Licensed under the [Apache License, Version 2.0](LICENSE), the same license used by Mathlib.

## References
<a id="1">[1]</a>
Leon Zheng, Quoc-Tung Le, Elisa Riccietti, and Remi Gribonval, *Butterfly Factorization with Error Guarantees*, SIAM Journal on Matrix Analysis and Applications, 2025