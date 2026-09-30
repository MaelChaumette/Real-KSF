# Kronecker-Sparse Factorizations — Lean 4 Formalization

![status: proved](https://img.shields.io/static/v1?label=status&message=proved&color=0f8f88&style=flat-square)
![Lean: 4.32.0](https://img.shields.io/static/v1?label=Lean&message=4.32.0&color=6b4fbb&style=flat-square)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)

A [Lean 4](https://leanprover.github.io/) / [Mathlib](https://leanprover-community.github.io/mathlib4_docs/)
formalization of the results of

> Maël Chaumette, Rémi Gribonval, Elisa Riccietti,
> *"On the Real and Imaginary Parts of Kronecker-Sparse Factorizations, with Application to Fast Transforms."*
> <!-- TODO: add venue / year / arXiv or DOI link once available -->

The paper studies **Kronecker-sparse factorizations** — products of matrices whose supports follow a Kronecker pattern $\mathbf{I}_a ⊗ \mathbf{1}_{b×c} ⊗ \mathbf{I}_d$ — and shows that if a complex matrix $\mathbf{K}$ admits a Kronecker-sparse factorization along a *chainable architecture* [[1, Definition 4.12]](#1), then its real part $\mathrm{Re}(\mathbf{K})$ also admits an explicit Kronecker-sparse factorization, doubling the row/column spaces along the way.

This repository formalizes every numbered statement of the paper (Lemmas 1–3, Definition 1, equations (1)–(3), Proposition 1, Corollary 1) as machine-checked Lean theorems, with **no `sorry` and no additional axioms** beyond what Mathlib itself uses.

## Project layout

The project is split into three parts, so that a reader can tell at a glance which Lean declarations *are* the paper's results and which ones are bridging work needed to state them:

```
Test.lean                — table of contents (this project's own front page, no imports)
Test/Definitions.lean    — every def/structure used anywhere below, in one place
Test/Paper/              — the paper's results, proved exactly as stated
Test/Support/            — bridging lemmas needed along the way, not stated in the paper
```

| Directory | Contents |
|---|---|
| [`Test/Definitions.lean`](Test/Definitions.lean) | Kronecker-sparse factors (`IsKSparse`), the permutation `P_π` (`Pperm`), the real/imaginary doubling `Kbar`/`Kbarprod`, the arithmetic of Proposition 1 (`Prop1.rho`, `Condition10`, `C1`/`C2`/`C3`, `Chainable2`), and the flat/telescoping objects (`Kflat`, `Pfor`, `Ktilde`, `KtildeProd`) used to assemble Corollary 1. |
| [`Test/Paper/`](Test/Paper) | `Lemma1.lean`, `Definition1.lean`, `Lemma2.lean`, `Lemma3.lean`, `RealPart.lean`, `RealPartChain.lean`, `Proposition1.lean`, `Corollary1.lean` — one file per paper statement (or tight group of statements). |
| [`Test/Support/`](Test/Support) | `CommutationMatrix.lean`, `Lemma1Aux.lean`, `Permutation.lean`, `FlatChain.lean`, `Proposition1Aux.lean`, `Assembly.lean`, `ChainAssembly.lean`, `ChainSparse.lean` — reindexings between the abstract, `Bool×`-typed, and flat `Fin`-indexed pictures, orthogonality of permutation matrices, and the telescoping construction of `K̃_ℓ`. |

## Correspondence with the paper

| Paper statement | Lean declaration | File |
|---|---|---|
| Definition 1 (Kronecker-sparse factor) | `IsKSparse` | [`Test/Definitions.lean`](Test/Definitions.lean) |
| Definition 1 (real/imaginary parts stay Kronecker-sparse) | `IsKSparse.re`, `IsKSparse.im` | [`Test/Paper/Definition1.lean`](Test/Paper/Definition1.lean) |
| Lemma 1 | `commutationMatrix_mul_repeatFst` | [`Test/Paper/Lemma1.lean`](Test/Paper/Lemma1.lean) |
| Lemma 2 | `Pperm_mul_repeatFst` | [`Test/Paper/Lemma2.lean`](Test/Paper/Lemma2.lean) |
| Lemma 3 | `lemma3_core` | [`Test/Paper/Lemma3.lean`](Test/Paper/Lemma3.lean) |
| Equation (1) | `re_mul` | [`Test/Paper/RealPart.lean`](Test/Paper/RealPart.lean) |
| Equation (2) | `im_mul` | [`Test/Paper/RealPart.lean`](Test/Paper/RealPart.lean) |
| Equation (3) | `chain_re` | [`Test/Paper/RealPartChain.lean`](Test/Paper/RealPartChain.lean) |
| Remark 2 (DHT, imaginary-part analogue of (3)) | `chain_im` | [`Test/Paper/RealPartChain.lean`](Test/Paper/RealPartChain.lean) |
| Proposition 1 | `Prop1.prop1_core` | [`Test/Paper/Proposition1.lean`](Test/Paper/Proposition1.lean) |
| Corollary 1 (chainable ⟹ condition (10), pairwise) | `Prop1.chainable_condition10` | [`Test/Paper/Proposition1.lean`](Test/Paper/Proposition1.lean) |
| Corollary 1 (factorization of `Re(K)`) | `re_Kprod_eq_KtildeProd` | [`Test/Paper/Corollary1.lean`](Test/Paper/Corollary1.lean) |
| Corollary 1 (each new factor is Kronecker-sparse) | `ktilde_zero_isKSparse`, `ktilde_succ_isKSparse` | [`Test/Paper/Corollary1.lean`](Test/Paper/Corollary1.lean) |

Reading order for the mathematics: `Lemma1 → Definition1 → Lemma2 → Lemma3 → RealPart →
RealPartChain → Proposition1 → Corollary1`. Every `Test/Paper/*.lean` file starts with a
docstring explaining the statement it formalizes and how its proof is organized; consult the
matching `Test/Support/*.lean` file for the proofs of any technical lemma it relies on that is
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

# build everything (Test.Definitions, Test.Paper.*, Test.Support.*)
lake build
```

A clean `lake build` produces **zero errors, zero warnings, and zero `sorry`s**.

### Browsing the documentation

CI ([`lean_action_ci.yml`](.github/workflows/lean_action_ci.yml)) builds the project and
generates hoverable HTML documentation with
[`doc-gen4`](https://github.com/leanprover/doc-gen4) via
[`docgen-action`](https://github.com/leanprover-community/docgen-action) on every push,
ready to deploy to GitHub Pages. To generate the same documentation locally, add `doc-gen4` as a
dev dependency (`lake add doc-gen4 --dev` or see the `docgen-action` README) and run
`lake -R -Kenv=dev build Test:docs`.

## Status

* **No `sorry`**, anywhere in the project.
* **No custom axioms**: every theorem's proof term only relies on the axioms Mathlib itself
  uses (`Classical.choice`, `Quot.sound`, `propext`). This is checked, not just asserted:
  [`Test/AxiomCheck.lean`](Test/AxiomCheck.lean) runs `#print axioms` on every single theorem in
  `Test/Paper/` and is built as part of `lake build` — a `sorry` anywhere in a paper result's
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