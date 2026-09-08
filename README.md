# Finite time blowup for Navier–Stokes and Euler equations

This repository contains Lean 4 formalizations of the results presented in
“Finite time blowup for Navier–Stokes” and
“Finite time blowup for the Euler equation” by OpenAI.

## Navier Stokes

For every positive viscosity, we prove two results:

- **Whole space $\mathbb{R}^3$:** There exist smooth initial data and forcing for
  which no global smooth solution with uniformly bounded kinetic energy exists.
- **Periodic torus $\mathbb{R}^3/\mathbb{Z}^3$:** There exist smooth periodic
  initial data and forcing for which no global smooth solution exists.

In both cases the witnesses take the initial velocity to be identically zero and
place the whole construction in the forcing, which is smooth, satisfies the
required decay conditions, and vanishes after a finite time.

These are alternatives [**(C)**](https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf#page=2) “Breakdown of Navier–Stokes solutions on ℝ³”
and [**(D)**](https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf#page=2) “Breakdown of Navier–Stokes Solutions on ℝ³/ℤ³”
in the Clay Mathematics Institute’s [official problem description](https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf)
of the [Navier–Stokes existence and smoothness](https://www.claymath.org/millennium/navier-stokes-equation/)
[Millennium Prize Problem](https://www.claymath.org/millennium-problems/).

## Euler

We construct smooth, compactly supported, divergence-free initial velocity on
$\mathbb{R}^3$ whose solution to the unforced incompressible Euler equations
develops a singularity in finite time. The velocity’s $C^1$ norm becomes unbounded
near that time, and the time integral of the vorticity’s $L^\infty$ norm diverges.

## Where to start

- [`Euler/Solution.lean`](Euler/Solution.lean) — the two delivered Euler theorems,
  `Euler.euler_breakdown_R3` and `Euler.exists_compact_smooth_euler_singularity`.
- [`NavierStokes/ComparatorSolution.lean`](NavierStokes/ComparatorSolution.lean) — the two
  delivered Navier–Stokes theorems, `NavierStokes.Comparator.navier_stokes_breakdown_R3`
  (alternative (C)) and `NavierStokes.Comparator.navier_stokes_breakdown_periodic`
  (alternative (D)).
- The definitions those statements are written in are re-declared inside this repository, in
  [`Euler/SolutionDefinitions.lean`](Euler/SolutionDefinitions.lean) and
  [`NavierStokes/ComparatorDefinitions.lean`](NavierStokes/ComparatorDefinitions.lean), so that
  the proofs never import the challenge modules. The Comparator run is what checks that these
  copies agree with the independent reference statements in
  [`ComparatorChallenges/`](ComparatorChallenges).
- [`docs/PROOF-OUTLINE.md`](docs/PROOF-OUTLINE.md) — a reader's map of both developments: what
  the initial data and forcing are, which quantity diverges and why, how the modules are
  layered, the main intermediate theorems, and the naming vocabulary.
- [`formalization.yaml`](formalization.yaml) — machine-readable metadata: the four main results,
  their modules, their axioms, and the Comparator configurations that check them.

Each of the four theorems is followed in its module by a `#print axioms` command; the reported
axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Independent proof checking

The trust gate for this repository is Comparator, which rebuilds the solution inside a sandbox
and compares it against an independent statement of the problem. **Comparator's guarantee
depends on the solution never having been compiled outside that sandbox, so run it in a fresh
clone in which `lake build` has not been run.** For the full preconditions and the exact
commands, see the [ComparatorChallenges README](ComparatorChallenges/README.md).

## Building the formalizations

Use a clone separate from the one you check with Comparator. The project uses Lean 4.34.0-rc2,
Mathlib, and Lake. With [elan](https://github.com/leanprover/elan) installed, fetch the mathlib
cache and build the formalizations with:

```sh
lake exe cache get
lake build
```

`lake exe cache get` covers Mathlib only; everything in this repository is compiled locally.
A cold build of all three libraries is about 11,250 jobs and takes roughly 15 minutes of wall
clock on 20 cores. The only expected warnings are the four intentional `sorry` placeholders in
the `ComparatorChallenges` reference statements.
