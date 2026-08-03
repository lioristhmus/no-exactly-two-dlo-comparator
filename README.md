# Comparator certificate for *No Set Carries Exactly Two DLOs*

This repository is the independent [Lean Comparator](https://github.com/leanprover/comparator)
certificate for the headline endpoint of:

> Lior Isthmus, *No Set Carries Exactly Two Dense Linear Orders without
> Endpoints: A Cut-Rotation Proof in a Weak Zermelo Theory without Choice or
> Replacement*.

The paper release package is in
[`no-exactly-two-dlo`](https://github.com/lioristhmus/no-exactly-two-dlo), with
reserved paper version DOI
[`10.5281/zenodo.21765207`](https://doi.org/10.5281/zenodo.21765207).
The full Lean development is in
[`no-exactly-two-dlo-lean`](https://github.com/lioristhmus/no-exactly-two-dlo-lean).

## What is checked

The checked proposition is

```lean
Nonempty (
  ExactThreeDLO.FO.Provable
    ExactThreeDLO.FO.Zsep
    (∼ ExactTwoDLO.FO.spec2Sentence)
)
```

Thus the solution must supply a kernel-accepted derivation object for

```text
Z_sep ⊢ ¬∃ X, Spec_=2(X).
```

`Provable` is a `Type` of derivation objects rather than a `Prop`. The
`Nonempty` wrapper exposes existence of exactly that object as a proposition
understood by the Lean 4.29 Comparator. It does not replace the object-language
calculus by a semantic proxy: the witness used in `Solution.lean` is the public
declaration `ExactTwoDLO.FO.zsep_proves_not_spec2Sentence`.

- [`Challenge.lean`](Challenge.lean) imports only Mathlib. It independently
  repeats the 54 definitions occurring transitively in the endpoint statement:
  50 shared or exact-three threshold definitions and four exact-two spectrum
  definitions. It contains one intentional `sorry`, the trusted challenge
  hole.
- [`Solution.lean`](Solution.lean) imports the formalization at a fixed Git
  commit and supplies the witness.
- [`config.json`](config.json) asks Comparator to check statement identity,
  restrict axiom dependencies to `propext`, `Classical.choice`, and
  `Quot.sound`, and replay the solution with Lean's kernel.

The Comparator certificate checks this headline proof-theoretic endpoint. The
larger 45-item paper-to-Lean correspondence, source-paper checksum, and release
ledger remain separate Level IV audit artifacts in the formalization and paper
repositories; this small repository does not claim to duplicate those audits.

## Reproducibility pins

| Component | Pin |
|---|---|
| Lean | `v4.29.1` |
| Mathlib | `5e932f97dd25535344f80f9dd8da3aab83df0fe6` |
| exact-two formalization | `bfa29d66e1850cc881ebdf191bd907bac8af1eda` |
| exact-three dependency | `ca5d9488552e68fd64ffb0da05912c3fa68d78c9` (`v1.0.0`) |
| Comparator source | `2a00b30df5e9173e70c4e4ec669fdf03da3163b9` (`v4.29.0`) |
| lean4export | `6f4e21dd70c3c11d7fbd07d39e3192792c657448` (`v4.29.1`) |
| Lean4Checker | `b7398199245524275543dec6113229c9bb4902e5` |
| Landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |

The Comparator release tag is `v4.29.0`; the small checked patch in
[`scripts/comparator-v4.29.1.patch`](scripts/comparator-v4.29.1.patch) updates
its Lean toolchain and lean4export pin to their `v4.29.1` counterparts. It also
adds the missing Landrun option terminator before the child command, preserving
the separate `--` that tells lean4export where declaration names begin.
The build script checks both the resolved manifest pin and the materialized Git
HEADs of lean4export and Lean4Checker before exposing their executables. The
project-side pin check independently verifies all 11 locked dependency entries
and their materialized Git HEADs, and fails closed if any package root is a
symbolic link.

## Ordinary build

With Lean installed through `elan`:

```bash
lake exe cache get
bash scripts/check-source.sh
```

The expected warning in `Challenge.lean` is its single trusted `sorry`.
`Solution.lean` contains no `sorry`.

## Sandboxed Comparator verification on Linux

Comparator's threat model requires a fresh, unprivileged Linux environment.
Landrun currently also needs the `systemd-run` `AF_UNIX` restriction documented
by Comparator upstream. Go 1.24 or later is needed to build Landrun from source.

Choose a new, nonexistent tools directory:

```bash
bash scripts/build-comparator-tools.sh /absolute/path/to/new-tools-directory
lake exe cache get
bash scripts/run-comparator-linux.sh /absolute/path/to/new-tools-directory/bin
```

`run-comparator-linux.sh` deliberately refuses macOS, root, a missing user
systemd manager, or missing binaries. Before invoking Comparator it also checks
that a transient service runs normally, can create an `AF_INET` socket, and is
specifically denied an `AF_UNIX` socket. On a noninteractive Linux host,
initialize the user manager first if necessary:

```bash
sudo loginctl enable-linger "$USER"
sudo systemctl start "user@$(id -u).service"
export XDG_RUNTIME_DIR="/run/user/$(id -u)"
export DBUS_SESSION_BUS_ADDRESS="unix:path=$XDG_RUNTIME_DIR/bus"
```

Success ends with:

```text
Lean default kernel accepts the solution
Your solution is okay!
```

The GitHub Actions workflow performs the ordinary build and the sandboxed
Comparator check in separate fresh jobs, so the security-sensitive job does not
compile `Solution.lean` before Comparator takes control. Pull requests receive
the ordinary build; the certificate job runs only for pushes and manual runs,
where the trusted challenge and verification scripts come from the repository.

## Trust boundary

Comparator treats `Challenge.lean`, its imports, the Lake configuration, its
own executable, lean4export, Landrun, the operating system, hardware, and the
Lean kernel as trusted. It treats `Solution.lean` and its imported proof as the
material being checked. See the upstream Comparator README for the complete
threat model and current Landrun caveat.

## License

Apache License 2.0. See [`LICENSE`](LICENSE).
