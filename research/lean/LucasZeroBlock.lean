import LucasZeroShape
import LocalCut
namespace LucasZeroBlock
open GreedyPrefix LucasZeros

/-- The exact zero positions in a Lucas block reduce to zero positions in
the smaller block, subject to a sharp parity-dependent lower bound on the remainder. -/
theorem zero_iff (j r : ℕ) (hr : r≤luc (j+3)) :
    (total fib (luc (j+4)+r)=total luc (luc (j+4)+r)) ↔
      (total fib r=total luc r ∧ (r=0 ∨ fib (j+2)-(if j%2=0 then 1 else 0)≤r)) := by
  rw [←LocalCut.first_formula]
  exact LucasZeroShape.zero_of_cut j _ r (LocalCut.last_lt j) (LocalCut.last j) (LocalCut.flat j) hr

end LucasZeroBlock
#print axioms LucasZeroBlock.zero_iff
