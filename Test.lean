/-!
# On the Real and Imaginary Parts of Kronecker-Sparse Factorizations

This project formalizes the results of the paper *"On the Real and Imaginary Parts of
Kronecker-Sparse Factorizations, with Application to Fast Transforms"* (Maël Chaumette, Rémi
Gribonval, Elisa Riccietti), in Lean 4 / Mathlib.

The project is organized in three parts:

* **`Test.Definitions`** — every `def`/`structure` used anywhere below, in one place: Kronecker-
  sparse factors, the permutation `P_π`, the real/imaginary doubling `K̄`, the arithmetic of
  Proposition 1, and the flat/telescoping machinery needed to connect the paper's statements to
  each other in Lean.
* **`Test.Paper.*`** — the paper's own results, proved exactly as stated: `Lemma1`, `Lemma2`,
  `Lemma3`, `Definition1` (Kronecker-sparse factors and their real/imaginary parts), `RealPart`/
  `RealPartChain` (equations (1)–(3)), `Proposition1`, `Corollary1`.
* **`Test.Support.*`** — the extra bridging lemmas needed along the way (flat `Fin`-indexed
  reindexings, value-preserving casts, orthogonality of the permutations, the telescoping
  construction of `K̃_ℓ`, ...) that are not results of the paper itself, but plumbing required to
  state and connect them in Lean.

Reading order for the mathematics: `Lemma1 → Definition1 → Lemma2 → Lemma3 → RealPart →
RealPartChain → Proposition1 → Corollary1`, consulting `Test.Definitions` for any object's
formal statement and the matching `Test.Support` file for the proofs of its technical
properties.

This file itself carries no imports on purpose (every module below is already compiled as part
of the `Test` library via `lakefile.toml`'s `Test.*` glob, regardless of what this file
imports) — it is a pure table of contents.
-/
