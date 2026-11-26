# Cantor sets of compactly supported Pauli partners

Shkarin asked whether a family of compactly supported wave functions with the same position and momentum distributions must be discrete modulo global phase. The manuscript constructs a Cantor set of such states, all supported on the unit interval. It also gives a second construction with real-valued binary phase masks. [Shkarin, Question 5.2](https://arxiv.org/pdf/1209.1225#page=8)

- [Manuscript (PDF)](pauli-sets.pdf)
- [LaTeX source](pauli-sets.tex)
- [Lean 4 proof](Pauli.lean)
- [Literature review and verification notes (Chinese)](literature-review.zh.txt)

## Machine-checked result

`Pauli.shkarin_counterexample` constructs normalized, compactly supported wave functions indexed by infinite Boolean sequences. It proves that their position moduli agree, their Fourier moduli agree at every real frequency, and distinct sequences give states that are inequivalent almost everywhere modulo a constant phase. `Pauli.no_countable_enumeration` proves directly that no sequence of wave functions can enumerate these states modulo phase.

The Lean code uses angular frequency and the representative supported on `(0, 1]`. The paper uses cycles per unit length and a representative supported on `[0, 1)`. The endpoints differ on a null set. Rescaling the frequency by a factor of 2π and applying the corresponding density normalization gives the same momentum data. The Cantor topology, nonvanishing Fourier modulus, and real binary construction are proved in the manuscript.

## Reproduce the build

With [Elan](https://github.com/leanprover/elan) installed, run these commands from the repository root.

```sh
lake exe cache get
lake build
```

The Lean release is pinned in `lean-toolchain` and the mathlib commit is pinned in the Lake files. The build prints the axiom dependencies of both theorems. To regenerate the PDF, run `pdflatex pauli-sets.tex` twice.

The literature review identified related wide-band and finite-translation constructions. Publication priority remains unverified. OpenAI Codex contributed to the mathematical derivation, source review, manuscript, and Lean code.
