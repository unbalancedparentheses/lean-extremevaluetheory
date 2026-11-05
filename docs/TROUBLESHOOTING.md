# Troubleshooting

## `lake` or `elan` is not on `PATH`

`command not found: lake` after installing elan usually means the shell has not picked up its directory:

```sh
export PATH="$HOME/.elan/bin:$PATH"
```

Add the line to your shell profile to keep it, or call `~/.elan/bin/lake` directly.

## `lake build` starts compiling Mathlib

It should compile only `ExtremeValueTheory` files. If `Mathlib.*` files are being built, stop it and fetch the
cache:

```sh
lake exe cache get
```

If the cache seems corrupted, `lake exe cache get!` downloads all of it again.
Do not run `lake update`: it moves Mathlib away from the version pinned in `lake-manifest.json`, and the
prebuilt files no longer apply. To undo it, run `git checkout lake-manifest.json`, then `lake exe cache get`.

## "too many open files"

Retry the command; a build continues from where it stopped. "Too many open files in system" means the whole
machine has run out, usually because several builds or large copies of `.lake` are running at once, so wait for
them to finish. Otherwise the limit may be your shell's, and you can raise it and retry:

```sh
ulimit -n 65536
```

## Stale `.lake`

Errors about missing or outdated `.olean` files, or errors that make no sense after switching branches:

```sh
rm -rf .lake/build   # this library's build only; Mathlib is kept
lake build
```

If that does not help, start again from nothing:

```sh
rm -rf .lake
lake exe cache get
lake build
```

## Toolchain mismatch

Lean and Mathlib must be the versions this repository pins. Compare:

```sh
cat lean-toolchain
elan show
```

elan selects the toolchain from `lean-toolchain` by itself, so run `lake` from the repository root. In a project
that depends on this library, copy this repository's `lean-toolchain` for the tag you require.
