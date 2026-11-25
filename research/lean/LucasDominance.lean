import LucasPrefixes
import LocalZeck

namespace LucasDominance
open LucasZeros

/-- The cumulative number of Fibonacci summands always bounds the cumulative
number of Lucas summands, for the greedy representations of 1 through n. -/
theorem dominance (n : ℕ) : U n≤V n :=
  LucasPrefixes.bound_of_local LocalZeck.local_add (n+1)

/-- Both assertions of Conjecture 1 in section 6 of Kimberling (2020). -/
theorem conjecture_one :
    (∀ n, U n≤V n) ∧ (∀ B, ∃ n, B<n ∧ V n=U n) :=
  ⟨dominance,unbounded_equalities⟩

end LucasDominance
#print axioms LucasDominance.dominance
#print axioms LucasDominance.conjecture_one
