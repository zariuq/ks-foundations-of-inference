# KnuthSkilling Lean Library

This directory contains the K&S-specific modules.  For the standalone repository
overview, dependency pins, build commands, and paper links, see `../README.md`.

## Entry Points

- `FoundationsOfInference.lean`: reviewer-facing entrypoint for the K&S core
  described in the companion papers.
- `../KnuthSkilling.lean`: default repository entrypoint.
- `Additive/Main.lean`: Appendix A additive representation theorem.
- `Multiplicative/Main.lean`: Appendix B product theorem.
- `Variational/Main.lean`: Appendix C variational/Cauchy theorem.
- `Information/Main.lean`: K&S Section 6/8 divergence and entropy.

## Local Build

From the repository root:

```bash
lake build +KnuthSkilling.FoundationsOfInference
lake build +KnuthSkilling
```

## Status

The reviewer-facing entrypoint does not depend on the exploratory/scratch files.
Those files remain in the repository with explicit `sorry`s where work is
unfinished, rather than being hidden behind placeholder assumptions.
