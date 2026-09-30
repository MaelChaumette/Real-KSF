# Contributing

Thanks for your interest in this formalization! Since this project tracks a specific paper, the
most useful contributions are:

* **Bug reports**: if you believe a formalized statement does not faithfully match the paper
  (wrong hypotheses, wrong conclusion, a silently vacuous statement, ...), please open an issue
  describing the discrepancy — ideally with the paper's equation/theorem number and the Lean
  declaration you think is wrong.
* **Mathlib/toolchain updates**: bumping [`lean-toolchain`](lean-toolchain) and the Mathlib
  `rev` in [`lakefile.toml`](lakefile.toml), and fixing whatever breaks. The
  [`update.yml`](.github/workflows/update.yml) workflow can open this kind of PR automatically.
* **Proof golfing / readability**: shorter or clearer proofs are welcome, provided they keep the
  same statement and don't introduce `sorry` or extra axioms.

## Before opening a PR

1. Run `lake exe cache get` once, then `lake build`. The project must build with **zero
   errors, zero warnings, and zero `sorry`s** — this is enforced by CI
   ([`lean_action_ci.yml`](.github/workflows/lean_action_ci.yml)).
2. Check `#print axioms <your_theorem>` doesn't pull in anything beyond Mathlib's own axioms
   (`Classical.choice`, `Quot.sound`, `propext`).
3. Follow the project's existing structure (see [`README.md`](README.md#project-layout)):
   * A `def`/`structure` belongs in [`Test/Definitions.lean`](Test/Definitions.lean), not in a
     `Test/Paper` or `Test/Support` file.
   * A theorem that states something the paper itself states belongs in `Test/Paper/`, named
     and grouped to match the paper's own numbering.
   * A theorem that exists only to connect two paper statements in Lean (reindexing, value
     lemmas, orthogonality, ...) belongs in `Test/Support/`.
4. Document *why*, not *what*: a docstring should explain which paper statement a declaration
   corresponds to and any non-obvious modeling choice, not restate the Lean code in prose.

## Getting help

If you're unsure whether a change fits, open an issue or a draft PR first — happy to discuss
before you invest time in a full proof.
