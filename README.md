# Lean proofs for OEIS A027171

This project gives a machine-checked proof of R. J. Mathar’s recurrence for OEIS A027171 for every integer index `n ≥ 2`. Mathar recorded the conjecture on May 6, 2026. Christian Krause recorded a closed formula four days later. The proof derives the closed formula from the original binomial sum and uses a standard central-binomial identity from mathlib. Priority for the first proof or first formalization remains undetermined. [A027171](https://oeis.org/A027171) · [Defining triangle A027170](https://oeis.org/A027170)

## Theorems

| Lean declaration | What it proves |
| --- | --- |
| `Rec027171.mathar` | Mathar’s recurrence in its original indexing, for every `n ≥ 2`. |
| `Rec027171.homogeneous` | A homogeneous recurrence obtained by taking two forward differences. |
| `Egypt242.covered` | For every `n > 2` with `n % 24 ≠ 1`, the rational number `4/n` is a sum of three unit fractions with strictly increasing positive denominators. |

The third theorem formalizes a known partial result for the Erdős–Straus problem. The general conjecture remains open. [Catalogue statement](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/242.lean) · [Known modulo-24 reduction](https://arxiv.org/abs/2605.23601)

## Verify

With [Elan](https://lean-lang.org/install/) on your path, run these commands from the repository root.

```sh
lake update
lake exe cache get
lake build
lake env lean Audit.lean
```

The project pins Lean and a mathlib commit for replay. The audit checks the reported axioms of all three declarations against the reports from the original verification. GitHub Actions is configured to build the project and run the same audit on pushes and pull requests.

## Provenance

A coordinated AI-agent research session produced the proofs. The original source file was checked in Lean Web with Lean 4.37.0-rc1 and mathlib. All three declarations reported only `propext`, `Classical.choice`, and `Quot.sound`. The web editor did not report its exact mathlib commit in the session. This package uses mathlib’s matching release tag for reproducibility. [Pinned mathlib revision](https://github.com/leanprover-community/mathlib4/commit/31ce06eaadf4a200c0e1407c5f10953cf606b8f8)
