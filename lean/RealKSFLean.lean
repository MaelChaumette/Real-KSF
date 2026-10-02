/-!
# On the Real Part of Butterfly Factorizations

This project formalizes the results of the paper *"On the Real Part of Butterfly
Factorizations, with Application to Fast Transforms"* (Maël Chaumette, Rémi Gribonval, Elisa
Riccietti), in Lean 4 / Mathlib.

The project is organized in three parts:

* **`RealKSFLean.Definitions`** — every `def`/`structure` used anywhere below, in one place:
  Kronecker-sparse factors, the commutation matrix, the permutation `P_π`, the real/imaginary
  doubling `K̄`, the conditions C1–C3 of Proposition 1 and chainability, and the
  flat/telescoping machinery needed to connect the paper's statements to each other in Lean.
* **`RealKSFLean.Paper.*`** — the paper's own results, proved exactly as stated: `Definition1`
  (Kronecker-sparse factors and their real/imaginary parts), `Definition2` (the commutation
  matrix), `RealPart`/`RealPartChain` (equation (1) and the imaginary part), `Equation8`,
  `Lemma1`, `Lemma2`, `Proposition1` (one junction) and `Proposition1Architecture` (whole
  architecture), `Corollary1`.
* **`RealKSFLean.Support.*`** — the extra bridging lemmas needed along the way (flat `Fin`-indexed
  reindexings, value-preserving casts, orthogonality of the permutations, the telescoping
  construction of `K̃_ℓ`, ...) that are not results of the paper itself, but plumbing required to
  state and connect them in Lean.

Reading order for the mathematics: `Definition1 → RealPart → RealPartChain → Definition2 →
Equation8 → Lemma1 → Lemma2 → Proposition1 → Proposition1Architecture → Corollary1`, consulting
`RealKSFLean.Definitions` for any object's formal statement and the matching
`RealKSFLean.Support` file for the proofs of its technical properties.

This file itself carries no imports on purpose (every module below is already compiled as part
of the `RealKSFLean` library via `lakefile.toml`'s `RealKSFLean.*` glob, regardless of what this
file imports) — it is a pure table of contents.
-/
