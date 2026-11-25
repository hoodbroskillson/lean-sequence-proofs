# Lean proofs for integer sequences and number theory

This repository collects machine-checked results about integer sequences, Egyptian fractions, and the Erdős–Moser equation. The general Erdős–Straus and Erdős–Moser conjectures remain open.

## Theorems

| Problem | What Lean proves | Lean declaration |
| --- | --- | --- |
| Base-`b` digit sums | For every base `b ≥ 2` and initial symbol `c`, the unique fixed word of the substitution sending `j` to `j,…,j+b−1` has symbol `c + digitSum_b(n)` at position `n`, starting at zero. [A173527](https://oeis.org/A173527) · [A053828](https://oeis.org/A053828) | [`DigitWord.fixed_iff`](SwarmProofs/DigitWord.lean) |
| OEIS A027171 | R. J. Mathar’s recurrence in its original indexing, for every `n ≥ 2`. | [`Rec027171.mathar`](SwarmProofs.lean) |
| OEIS A027171 | A homogeneous recurrence obtained by taking two forward differences. | [`Rec027171.homogeneous`](SwarmProofs.lean) |
| OEIS A024219 | Howroyd’s floor formula and Mathar’s order-five recurrence for every target index `n ≥ 6`, starting from the defining elementary symmetric sums. [A024219](https://oeis.org/A024219) | [`A024219.floorFormula`](SwarmProofs/A024219.lean) · [`A024219.recurrence`](SwarmProofs/A024219.lean) |
| OEIS A024220 | Mathar’s order-seven recurrence for every index `n ≥ 8`, derived from the defining floor of a quotient of elementary symmetric sums. | [`A024220.recurrence`](SwarmProofs/A024220.lean) |
| OEIS A208355 | For every `n ≥ 2`, Mathar’s recurrence holds for the published sequence `a(n) = Catalan(⌊(n+1)/2⌋)`. Following the literal triangle rule in the A208101 heading instead gives a counterexample at `n = 5`. [A208355](https://oeis.org/A208355) · [A208101](https://oeis.org/A208101) | [`A208355.recurrence`](SwarmProofs/A208355.lean) · [`A208355.header_counterexample`](SwarmProofs/A208355.lean) |
| OEIS A286282 | Both of Mathar’s recurrences for Knowlton’s elevator follow from Graham’s published characterization. The fourth-order recurrence holds for `n ≥ 5` and the third-order recurrence for `n ≥ 4`. [A286282](https://oeis.org/A286282) | [`A286282.orderFour`](SwarmProofs/A286282.lean) · [`A286282.orderThree`](SwarmProofs/A286282.lean) |
| Erdős–Straus | For every `n > 2` with `n % 24 ≠ 1`, the rational number `4/n` is a sum of three unit fractions with strictly increasing positive denominators. | [`Egypt242.covered`](SwarmProofs.lean) |
| Egyptian fractions | For `q ≡ 1 (mod 3)`, `3/q` is a sum of two positive unit fractions exactly when `q²` has a divisor congruent to 2 modulo 3. [Eppstein](https://ics.uci.edu/~eppstein/numth/egypt/smallnum.html) | [`EgyptianDivisor.three_over_iff`](SwarmProofs/EgyptianDivisor.lean) |
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
