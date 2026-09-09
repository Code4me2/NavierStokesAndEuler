# [Comparator](https://github.com/leanprover/comparator) challenges

Comparator is the trust gate for this repository. It rebuilds `Euler.Solution` and
`NavierStokes.ComparatorSolution` inside a sandbox, exports the resulting environment, and
checks that the theorems named in each JSON config prove exactly the statements given in the
challenge modules here, using no axioms beyond `propext`, `Quot.sound` and `Classical.choice`,
and that the Lean kernel — and, with `enable_nanoda`, the independent nanoda kernel — accepts
the proof terms.

The challenge modules `Euler.lean` and `NavierStokes.lean` in this directory contain the
reference statements with `sorry` placeholders. They are deliberate: a Comparator challenge is
a sorried statement, and the four `sorry` warnings printed by `lake build` come from these two
files and from nowhere else.

## Preconditions

Comparator's guarantee holds only under the assumptions listed in
[its own README](../.lake/packages/Comparator/README.md). The ones you have to arrange:

1. **Use a fresh clone in which the solution has never been compiled.** Do not run `lake build`
   (or `lake env lean` on any solution module) in the tree you intend to check. Comparator
   builds the solution itself inside the sandbox; if the artifacts already exist it replays
   them, and a solution compiled outside the sandbox could have compromised the challenge
   modules. `lake exe cache get` is fine — it fetches Mathlib only — as is
   `lake build lean4export comparator`, which builds tooling and not the solution.
2. **Do not run it as a privileged user.** Comparator's sandbox assumes an unprivileged
   process.
3. **Linux only.** The sandbox is [landrun](https://github.com/Zouuup/landrun), which uses the
   Landlock LSM; there is no supported macOS or Windows path.
4. **Trust the tooling below and the machine it runs on.** The trusted base includes the
   operating system, the hardware, landrun's sandboxing, and the Mathlib cache if you use one.

## External tools

Put these three binaries on `PATH`, or give their absolute paths in the environment variables
`COMPARATOR_LANDRUN`, `COMPARATOR_LEAN4EXPORT` and `COMPARATOR_NANODA`.

- **`landrun`** — <https://github.com/Zouuup/landrun>, built from `main`. Requires Go 1.24 or
  later; build the `./cmd/landrun` package, e.g. `go build -o landrun ./cmd/landrun`.
- **`lean4export`** — vendored as a Lake dependency of Comparator, so it does not need a
  separate checkout. From this repository's root, `lake build lean4export` produces
  `.lake/packages/lean4export/.lake/build/bin/lean4export`.
- **`nanoda_bin`** — <https://github.com/ammkrn/nanoda_lib>, built with a recent Rust toolchain:
  `cargo build --release` places `nanoda_bin` in `target/release`. Both configs here set
  `"enable_nanoda": true`, so this binary is required; the alternative is to remove that field
  and check with the Lean kernel alone.

## Running the checks

From the root of the fresh clone, fetch the Mathlib cache and build the tooling (neither step
compiles the solution):

```sh
lake exe cache get
lake build lean4export comparator
```

Then run each config under the `systemd-run` wrapper, which is part of the recommended
invocation: it guards against a landrun sandbox-escape vulnerability by denying `AF_UNIX`.

```sh
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" \
  --working-directory $(pwd) -- \
  bash -c 'lake exe comparator ComparatorChallenges/NavierStokes.json'

systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" \
  --working-directory $(pwd) -- \
  bash -c 'lake exe comparator ComparatorChallenges/Euler.json'
```

`lake exe comparator` builds and runs the binary; the equivalent explicit form is
`lake env .lake/packages/Comparator/.lake/build/bin/comparator <config>`.

If the external binaries are not on `PATH`, set the environment variables inside the wrapped
command, for example

```sh
bash -c 'COMPARATOR_LANDRUN=/abs/path/landrun \
         COMPARATOR_LEAN4EXPORT=$(pwd)/.lake/packages/lean4export/.lake/build/bin/lean4export \
         COMPARATOR_NANODA=/abs/path/nanoda_bin \
         lake exe comparator ComparatorChallenges/Euler.json'
```

Each run compiles the whole import closure of its solution module inside the sandbox, so expect
tens of minutes per config: on 20 cores the most recent runs took about 11 minutes for the
Navier–Stokes config (9,345 jobs) and about 20 minutes for the Euler config (10,557 jobs). A
successful run ends with `Your solution is okay!`.

## What each config checks

| Config | Challenge module | Solution module | Theorems |
|---|---|---|---|
| `NavierStokes.json` | `ComparatorChallenges.NavierStokes` | `NavierStokes.ComparatorSolution` | `NavierStokes.Comparator.navier_stokes_breakdown_R3`, `NavierStokes.Comparator.navier_stokes_breakdown_periodic` |
| `Euler.json` | `ComparatorChallenges.Euler` | `Euler.Solution` | `Euler.euler_breakdown_R3`, `Euler.exists_compact_smooth_euler_singularity` |

Thank you to the [Formal Conjectures](https://google-deepmind.github.io/formal-conjectures/) authors for their [Lean formalization of the Navier–Stokes problem statement](https://github.com/google-deepmind/formal-conjectures/blob/8bf45ed70d48b2b2a501de9c00b26bfa38c573ee/FormalConjectures/Millenium/NavierStokes.lean), which we adapted for these Comparator challenges.
