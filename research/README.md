# Fibonacci and Beatty proofs

These proofs use Lean 4.8.0 and mathlib at commit `b5eba595428809e96f3ed113bc7ba776c5f801ac`. The 78 Lean modules share a single source directory. The six [checker transcripts](verification/) include axiom reports for 148 distinct declarations. The results below make no claim of historical priority.

| Question | Verified result | Lean source |
| --- | --- | --- |
| How small can the limiting fraction of Fibonacci residues modulo powers of a prime be? | For every ε > 0 and every bound B, there is a prime p > B with 0 < dens(p) < ε. Here dens(p) is the limit, as k grows, of the fraction of residue classes modulo pᵏ attained by the entire Fibonacci sequence. | [Limit definition and convergence](lean/SmallFibonacciDensities.lean) · [Zero as an accumulation point](lean/PositiveFibonacciDensity.lean) |
| What does a small density look like at a specific prime? | For p = 433494437 = F₄₃, exactly 81 classes occur modulo p and dens(p) ≤ 81/p. The exact count concerns the first power. | [Prime certificate](lean/ExamplePrime.lean) · [Residue count and limiting upper bound](lean/SmallDensityWitness.lean) |
| Can invertible Fibonacci residues form a group for infinitely many moduli? | They fill the entire unit group modulo every positive power of 3 or 5. They also fill the unit group modulo 2ᵃ for a ≥ 3, where the class 4 is missing from the full Fibonacci image. | [Infinite subgroup family](lean/FibonacciUnitGroups.lean) · [Powers of two](lean/FibonacciTwoUnitGroups.lean) |
| What is the sharp discrepancy in the two-sequence construction of Artstein-Avidan, Fraenkel and Sós for t = 1? | For every integer s ≥ 2 the range is exactly {0,…,s+1}. For A₀=B₀=0, Aₙ the least nonnegative integer omitted by both previous columns, and Bₙ=sAₙ+n, the discrepancy is the absolute difference of Aₘ₊ⱼ−Aₘ and Aₙ₊ⱼ−Aₙ. Every value occurs with m,n,j positive. | [Definition and upper bound](lean/FamilyBalance.lean) · [Exact range](lean/FamilyRange.lean) |
| Is the 2008 paper's sufficient condition necessary for attaining its bound at t ≥ 2? | For (s,t) = (4,2) and (7,3), the sufficient condition fails and all five discrepancies 0 through 4 occur. Lean certifies the witnesses. The upper bound of four for these pairs follows from the paper's Theorem 2. | [Witnesses for both pairs](lean/FamilyCounterexamples.lean) |
| Which gaps occur between consecutive repeated or missing values of the Wythoff ceiling array? | The repeated values have gap set {3,5,10,13} (A341261). The missing values have gap set {2,3,5,10,13} (A341262). | [Both exact gap sets](lean/CeilingFinal.lean) |
| Which gaps occur between positions of each Wythoff–Stolarsky second-column difference? | In sequence order, the gap sets are {1,2,3} (A387349), {2,3,5} (A387350), and {3,5,8} (A387351). | [All three indexed proofs](lean/IndexedWythoffGaps.lean) |

## Sources and scope

Bragman and Rowland asked whether prime-power Fibonacci densities can be arbitrarily small. The proof settles that question. Classifying the other limit points is a separate question. An alternative deduction of smallness uses Stewart’s earlier bound for the largest prime factor of Fibonacci numbers. [Bragman and Rowland (2025), p. 4](https://ericrowland.github.io/papers/Limiting_density_of_the_Fibonacci_sequence_modulo_powers_of_a_prime.pdf) · [Stewart (2013)](https://doi.org/10.1007/s11511-013-0105-y)

The full unit-group examples contradict Conjecture 1.1 as printed by Luca, Stănică and Yalçiner. Burr’s complete residue-system classification already implies the examples at powers of 3 and 5. Jacobson treated powers of 2. The existence of an example forming a proper subgroup is a distinct question. [Conjecture 1.1 (2013)](https://ami.uni-eszterhazy.hu/uploads/papers/finalpdf/AMI_41_from265to270.pdf) · [Burr (1971)](https://www.fq.math.ca/Scanned/9-5/burr.pdf) · [Jacobson (1992)](https://www.fq.math.ca/Scanned/30-3/jacobson.pdf) · [Cadeliña and Dimabayao (2026)](https://doi.org/10.1080/00150517.2025.2540630)

The Beatty results address the questions at the end of §3 of the 2008 paper. Turek previously established the balance bound for the associated substitution word. The Lean proofs connect the relevant word counts to the original recursively defined sequences and construct witnesses. [Artstein-Avidan, Fraenkel and Sós (2008)](https://www.wisdom.weizmann.ac.il/~fraenkel/Papers/ArtsteinFrSos.pdf) · [Turek (2007)](https://doi.org/10.1051/ita:2007009)

Kimberling stated the five Wythoff gap conjectures in the corresponding OEIS entries. [A341261](https://oeis.org/A341261) · [A341262](https://oeis.org/A341262) · [A387349](https://oeis.org/A387349) · [A387350](https://oeis.org/A387350) · [A387351](https://oeis.org/A387351)

## Replay

With Git, Bash, Python 3 and elan installed, run these commands from this repository's root. The dedicated mathlib checkout selects the Lean version for these proofs.

```bash
git clone https://github.com/leanprover-community/mathlib4.git ../mathlib4-fib-beatty
git -C ../mathlib4-fib-beatty checkout b5eba595428809e96f3ed113bc7ba776c5f801ac
(cd ../mathlib4-fib-beatty && lake exe cache get)
bash research/verify.sh ../mathlib4-fib-beatty
```

The script checks the pinned versions, compiles each module in [dependency order](lean/modules.txt) into a fresh directory, and compares every printed axiom report with the archived reports. The allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.
