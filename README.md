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
| OEIS A193649 | Mathar’s generating function holds in every degree for the program’s reversed Fibonacci coefficient rows. Applying the same Q-downstep to the ordinary polynomial gives a different generating function. At index 3 the program gives 5 and the ordinary order gives 6. [A193649](https://oeis.org/A193649) | [`A193649.generating_function`](SwarmProofs/A193649.lean) · [`A193649.ordinary_generating_function`](SwarmProofs/A193649.lean) · [`A193649.orientation`](SwarmProofs/A193649.lean) |
| OEIS A193651 | For every `n ≥ 0`, Kimberling’s Q-downstep on the reversed rising-factorial coefficient row gives Luschny’s formula `((2n+1)!! + 1)/2`. [A193651](https://oeis.org/A193651) | [`A193651.closed_form`](SwarmProofs/A193651.lean) |
| OEIS A193652 | Interleaving the repeated binary block `10` with the same values plus one gives `2(4^⌊n/2⌋−1)/3 + (n mod 2)`. Mathar’s generating function `(x+2x²−2x³)/((1−x²)(1−4x²))` holds in every degree. [Zumkeller’s entry](https://oeis.org/A193652) · [A020988](https://oeis.org/A020988) · [A007583](https://oeis.org/A007583) | [`A193652.closed_form`](SwarmProofs/A193652.lean) · [`A193652.generating_function`](SwarmProofs/A193652.lean) |
| OEIS A193654 | For Kimberling’s executable weighted row sums, Mathar’s proposed ordinary generating function holds at every coefficient from degree zero onward. The closed form accounts for the floor in each row. The division shown in the entry’s heading gives zero in every cell. [A193654](https://oeis.org/A193654) | [`A193654.coefficient_identity`](SwarmProofs/A193654.lean) · [`A193654.scaled`](SwarmProofs/A193654.lean) · [`A193654.heading_zero`](SwarmProofs/A193654.lean) |
| OEIS A193656 | For every `n ≥ 0`, the iterated all-ones Q-residue is `3·5ⁿ − 2·4ⁿ`, with generating function `(1−2x)/((1−5x)(1−4x))`. It equals term `2n` of A097111. For any integer polynomial row `p`, twice its residue is `p(0)+p(2)`. [A193656](https://oeis.org/A193656) · [A097111](https://oeis.org/A097111) | [`A193656.closed_form`](SwarmProofs/A193656.lean) · [`A193656.generating_function`](SwarmProofs/A193656.lean) · [`A193656.bisection`](SwarmProofs/A193656.lean) · [`A193656.twice_residue`](SwarmProofs/A193656.lean) |
| OEIS A208101 | At every row `n ≥ 0`, the right edge of the executable triangle rule equals `Catalan(⌊(n+1)/2⌋)`. Its diagonal therefore satisfies Mathar’s recurrence for every `n ≥ 2`. [A208101 program](https://oeis.org/A208101) · [A208355 diagonal](https://oeis.org/A208355) | [`A208101.diagonal`](SwarmProofs/A208101.lean) · [`A208101.recurrence`](SwarmProofs/A208101.lean) |
| OEIS A208355 | For every `n ≥ 2`, Mathar’s recurrence holds for the published sequence `a(n) = Catalan(⌊(n+1)/2⌋)`. Following the literal triangle rule in the A208101 heading instead gives a counterexample at `n = 5`. [A208355](https://oeis.org/A208355) · [A208101](https://oeis.org/A208101) | [`A208355.recurrence`](SwarmProofs/A208355.lean) · [`A208355.header_counterexample`](SwarmProofs/A208355.lean) |
| OEIS A286282 | Both of Mathar’s recurrences for Knowlton’s elevator follow from Graham’s published characterization. The fourth-order recurrence holds for `n ≥ 5` and the third-order recurrence for `n ≥ 4`. [A286282](https://oeis.org/A286282) | [`A286282.orderFour`](SwarmProofs/A286282.lean) · [`A286282.orderThree`](SwarmProofs/A286282.lean) |
| Stern’s diatomic sequence | For all `r,n ≥ 0` and `0 ≤ k ≤ 2ʳ`, Reznick’s block formula gives `s(2ʳn+k) = s(2ʳ−k)s(n) + s(k)s(n+1)`. [Reznick, Corollary 4](https://cs.uwaterloo.ca/journals/JIS/VOL11/Reznick/reznick4.pdf) · [A002487](https://oeis.org/A002487) | [`SternDyadic.block`](SwarmProofs/SternDyadic.lean) |
| Stern’s diatomic sequence | For every `r ≥ 0`, equally many indices `0 ≤ i < 2ʳ` have `s(i)` divisible by 22 as have `s(i)` divisible by 27. This proves the equality Reznick conjectured after equation (15). [Reznick’s paper, p. 3](https://cs.uwaterloo.ca/journals/JIS/VOL11/Reznick/reznick4.pdf) | [`SternResidues.reznick`](SwarmProofs/SternResidues.lean) |
| Stern’s diatomic sequence, moduli through 128 | For `1 ≤ d < e ≤ 128`, the first `2ʳ` terms, starting at index zero, contain equally many multiples of `d` and `e` for every `r ≥ 0` exactly when `(d,e)` is `(4,5)`, `(6,9)`, `(6,11)`, `(9,11)`, or `(22,27)`. Testing depths 10, 12, 13, and 14 distinguishes every other pair. [Reznick, p. 3](https://cs.uwaterloo.ca/journals/JIS/VOL11/Reznick/reznick4.pdf) | [`SternClassification.classification`](SwarmProofs/SternClassification.lean) · [`SternClassification.four_depths`](SwarmProofs/SternClassification.lean) |
| Erdős–Straus | For every `n > 2` with `n % 24 ≠ 1`, the rational number `4/n` is a sum of three unit fractions with strictly increasing positive denominators. | [`Egypt242.covered`](SwarmProofs.lean) |
| Egyptian fractions | For `q ≡ 1 (mod 3)`, `3/q` is a sum of two positive unit fractions exactly when `q²` has a divisor congruent to 2 modulo 3. [Eppstein](https://ics.uci.edu/~eppstein/numth/egypt/smallnum.html) | [`EgyptianDivisor.three_over_iff`](SwarmProofs/EgyptianDivisor.lean) |
| Erdős–Straus | For every `n = 120k + 97` with `k ≥ 0`, explicit strictly increasing positive denominators give the same unit-fraction identity. Every such `n` is 1 modulo 24. | [`ErdosStraus97.covered`](SwarmProofs/ErdosStraus97.lean) |
| Erdős–Straus, fixed first denominator | For positive `n` and a specified `x` with `4x > n`, positive `y,z` complete `4/n = 1/x + 1/y + 1/z` exactly when `(nx)²` has a factor pair `d,e` with both `nx+d` and `nx+e` divisible by `4x−n`. [Bhattacharjee, Theorem 3.1](https://www.researchgate.net/publication/405220221_Erdos--Straus_Decompositions) | [`ErdosStrausFixedFirst.fixedFirst_iff`](SwarmProofs/ErdosStrausFixedFirst.lean) |
| Erdős–Moser | If positive `m` and even `k ≥ 2` satisfy `1^k + ⋯ + (m−1)^k = m^k`, then `m ≡ 3 (mod 8)`. | [`ErdosMoser.three_mod_eight`](SwarmProofs/ErdosMoser.lean) |
| Erdős–Moser | For positive `m` and even `k ≥ 2`, a solution of the power-sum equation satisfies `m % 3 ≠ 0`, as in Moree’s Theorem 2(2). [Moree](https://arxiv.org/abs/1011.2940) | [`ErdosMoser.not_zero_mod_three`](SwarmProofs/ErdosMoserThree.lean) |
| Erdős–Moser, square divisors | For positive `m,k` satisfying `1ᵏ + ⋯ + (m−1)ᵏ = a·mᵏ`, each `d ≥ 2` with `d²` dividing `m−1` divides `a`. When `a=1`, this gives Moser’s squarefreeness of `m−1`. [Moree, Theorem 2(3)](https://arxiv.org/abs/1011.2940) · [Generalized equation](https://arxiv.org/abs/1010.2275) | [`ErdosMoser.square_divisor_forces_multiplier`](SwarmProofs/ErdosMoserSquarefree.lean) · [`ErdosMoser.predecessor_squarefree`](SwarmProofs/ErdosMoserSquarefree.lean) |

## Sources

For A027171, Mathar recorded the conjecture on May 6, 2026. Christian Krause recorded a closed formula four days later. The proof derives the closed formula from the original binomial sum and uses a standard central-binomial identity from mathlib. Priority for the first proof or first formalization remains undetermined. [A027171](https://oeis.org/A027171) · [Defining triangle A027170](https://oeis.org/A027170)

For A024220, Clark Kimberling defined the sequence and Mathar proposed the recurrence in 2011. Sean A. Irvine recorded the quotient relation. The numerator’s closed form appears in A024213. [A024220](https://oeis.org/A024220) · [A024213](https://oeis.org/A024213)

The A208101 proof follows the row update in Jean-François Alcover’s Mathematica program. It identifies the entries with differences of adjacent binomial coefficients to derive the published Catalan diagonal. Michael Somos recorded the ballot-number formula in 1999. Alois P. Heinz recorded its connection to A208355 in 2026. [A208101](https://oeis.org/A208101) · [A008315](https://oeis.org/A008315) · [A208355](https://oeis.org/A208355)

The modulo-24 and `120k + 97` Erdős–Straus results formalize known partial cases. The first uses the modulo-24 reduction. The second progression is contained in the family from Elsholtz and Tao’s Proposition 1.9 with `(a,c,f) = (1,5,3)`. [Catalogue statement](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/242.lean) · [Modulo-24 reduction](https://arxiv.org/abs/2605.23601) · [Elsholtz and Tao](https://doi.org/10.1017/S1446788712000468)

The first Erdős–Moser proof formalizes the modulo-eight conclusion of Moree’s Theorem 2(2) under the assumption that the exponent is even. [Moree’s paper](https://arxiv.org/abs/1011.2940)

Reznick reported the 22/27 equality through `r = 19`. The proof groups all 1,213 residue pairs for the two moduli into 29 classes. Lean checks that each class determines whether the first term is zero modulo its modulus and which classes its two children occupy, counting repetitions. The starting pair `(0,1)` has the same class for both moduli, so induction gives equal counts at every depth. Priority for the first proof remains undetermined. [2006 preprint](https://arxiv.org/abs/math/0610601) · [Published conjecture](https://cs.uwaterloo.ca/journals/JIS/VOL11/Reznick/reznick4.pdf)

Reznick also stated that these coincidences exhaust the distinct moduli from 2 through 128. The classification includes modulus 1 and checks all four comparison depths against the sequence itself. For a listed pair, the proof checks the two child transitions for every residue pair and obtains equality at every depth by induction. [Reznick, equation (15) and the following paragraph](https://cs.uwaterloo.ca/journals/JIS/VOL11/Reznick/reznick4.pdf)

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
