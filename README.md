# Near-linear cycles in vertex-transitive graphs

This Lean project formalizes the near-linear cycle theorem and its path inputs
from Bucić, Christoph, Pokrovskiy, and Steiner,
[*Lovász conjecture holds asymptotically*](https://sites.google.com/view/matija-bucic/research)
(working draft, 23 September 2026). The full proof development is in
`RequestProject/`.

The four declarations selected in `comparator.json` state that, for every
`ε > 0`, every sufficiently large connected vertex-transitive graph on `n`
vertices has a simple cycle with at least `n^(1−ε)` edges; this also holds
for connected Cayley graphs. The two companion declarations give near-linear
simple paths. `Challenge.lean` is the small statement surface; `Solution.lean`
proves the same statements from the substantive development. Its only
permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.

The path statements count edges rather than the paper's path vertices, giving
a slightly stronger bound. The Cayley graph definition symmetrizes the
generating relation and discards loops. The path-to-cycle proof formalizes a
Bondy–Locke comparison with coefficient `2/7`, weaker than the source's `2/5`
but sufficient for the same `n^(1−ε)` asymptotic cycle result. The proof
development also includes a reduced finite approximate-group consequence;
it does not establish the full general Breuillard–Green–Tao theorem.

The substantive Lean development was produced with Aristotle (Harmonic).
OpenAI Codex audited the earlier path development, prepared this Palomar 
statement pair, and ported the Lean source to 4.35.0-rc3 with matching Mathlib. 
Matija Bucic is the human author and responsible maintainer named for the package.
The mathematical paper's four authors are credited in `formalization.yaml`.
The repository snapshot is offered under Apache-2.0; cited papers and Mathlib
retain their own licences.

## Verification and submission status

The ported 152-module development built successfully under the pinned Lean
`v4.35.0-rc3` toolchain on 28 September 2026 with
`lake --old build RequestProject Challenge Solution` (9,115 jobs). Separate
`#print axioms` checks of four core cycle declarations and all four Solution
theorems found only `propext`, `Classical.choice`, and `Quot.sound`.
`leanchecker` replay passed for the Solution and BondyLockeMain modules. The
four `sorry` declarations in `Challenge.lean` are intentional statement holes;
`Solution.lean` and `RequestProject/` have none.
All 154 project Lean source files use the `module` header. The module-system
migration added public imports and exposed public sections without rewriting
the mathematical statements or proof bodies.

**Palomar submission gate:** as checked on 28 September 2026, Palomar's
minimum accepted Lean toolchain is `v4.35.0-rc2`. This package pins Lean and
Mathlib to `v4.35.0-rc3` in `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`. Palomar also requires every regular Lean source file in
the submitted repository to use the `module` header; this snapshot meets that
source-layout rule. Palomar's Comparator and NanoDa checks remain to be run on
a public GitHub commit; local Lean checks do not substitute for them.

Push the package to a public GitHub repository, include the Apache-2.0
`LICENSE`, and submit the full pushed commit SHA with
`comparator.json` at [Palomar's submission site](https://submit.palomar-registry.org/).
Registration is a separate step after verification and editorial review.
