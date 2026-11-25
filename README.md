# Lean proofs for integer sequences and number theory

This repository collects machine-checked results about integer sequences, Egyptian fractions, and the Erdős–Moser equation. The general Erdős–Straus and Erdős–Moser conjectures remain open.

## Theorems

| Problem | What Lean proves | Lean declaration |
| --- | --- | --- |
| OEIS A027171 | R. J. Mathar’s recurrence in its original indexing, for every `n ≥ 2`. | [`Rec027171.mathar`](SwarmProofs.lean) |
| OEIS A027171 | A homogeneous recurrence obtained by taking two forward differences. | [`Rec027171.homogeneous`](SwarmProofs.lean) |
| OEIS A024220 | Mathar’s order-seven recurrence for every index `n ≥ 8`, derived from the defining floor of a quotient of elementary symmetric sums. | [`A024220.recurrence`](SwarmProofs/A024220.lean) |
| Erdős–Straus | For every `n > 2` with `n % 24 ≠ 1`, the rational number `4/n` is a sum of three unit fractions with strictly increasing positive denominators. | [`Egypt242.covered`](SwarmProofs.lean) |
| Erdős–Straus | For every `n = 120k + 97` with `k ≥ 0`, explicit strictly increasing positive denominators give the same unit-fraction identity. Every such `n` is 1 modulo 24. | [`ErdosStraus97.covered`](SwarmProofs/ErdosStraus97.lean) |
| Erdős–Moser | If positive `m` and even `k ≥ 2` satisfy `1^k + ⋯ + (m−1)^k = m^k`, then `m ≡ 3 (mod 8)`. | [`ErdosMoser.three_mod_eight`](SwarmProofs/ErdosMoser.lean) |
| Erdős–Moser | For positive `m` and even `k ≥ 2`, a solution of the power-sum equation satisfies `m % 3 ≠ 0`, as in Moree’s Theorem 2(2). [Moree](https://arxiv.org/abs/1011.2940) | [`ErdosMoser.not_zero_mod_three`](SwarmProofs/ErdosMoserThree.lean) |

## Sources

For A027171, Mathar recorded the conjecture on May 6, 2026. Christian Krause recorded a closed formula four days later. The proof derives the closed formula from the original binomial sum and uses a standard central-binomial identity from mathlib. Priority for the first proof or first formalization remains undetermined. [A027171](https://oeis.org/A027171) · [Defining triangle A027170](https://oeis.org/A027170)

For A024220, Clark Kimberling defined the sequence and Mathar proposed the recurrence in 2011. Sean A. Irvine recorded the quotient relation. The numerator’s closed form appears in A024213. [A024220](https://oeis.org/A024220) · [A024213](https://oeis.org/A024213)

Both Erdős–Straus results formalize known partial cases. The first uses the modulo-24 reduction. The second progression is contained in the family from Elsholtz and Tao’s Proposition 1.9 with `(a,c,f) = (1,5,3)`. [Catalogue statement](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/242.lean) · [Modulo-24 reduction](https://arxiv.org/abs/2605.23601) · [Elsholtz and Tao](https://doi.org/10.1017/S1446788712000468)

The Erdős–Moser proof formalizes the modulo-eight conclusion of Moree’s Theorem 2(2) under the assumption that the exponent is even. [Moree’s paper](https://arxiv.org/abs/1011.2940)

## Verify

With [Elan](https://lean-lang.org/install/) on your path, run these commands from the repository root.

```sh
lake update
lake exe cache get
lake build
lake env lean Audit.lean
```

The default build checks the proofs and the axiom reports embedded in the modules under `SwarmProofs/`. The final command checks the axiom reports for `Rec027171.mathar`, `Rec027171.homogeneous`, and `Egypt242.covered`. GitHub Actions runs the build and audit on pushes and pull requests. [Audit.lean](Audit.lean)

## Provenance

A coordinated AI-agent research session produced the original proofs. The original source file was checked in Lean Web with Lean 4.37.0-rc1 and mathlib. Its three audited declarations reported only `propext`, `Classical.choice`, and `Quot.sound`. The web editor did not report its exact mathlib commit in the session. This package uses mathlib’s matching release tag for reproducibility. [Pinned mathlib revision](https://github.com/leanprover-community/mathlib4/commit/31ce06eaadf4a200c0e1407c5f10953cf606b8f8)
