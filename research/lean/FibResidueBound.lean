import FibResidueLifts
import FibonacciLargeFactor

namespace FibResidueBound

/-- At a prime dividing F_n, at most 4n p^k residues occur modulo p^(k+1). -/
theorem count {p n : ℕ} (hp : p.Prime) (hn : 1≤n) (hd : p∣Nat.fib n) (k : ℕ) :
    Nat.card (attained (p^(k+1))) ≤ 4*n*p^k := by
  have base : Nat.card (attained p)≤4*n :=
    of_period (by omega) (FibonacciLargeFactor.period p n hd)
  calc Nat.card (attained (p^(k+1))) = Nat.card (attained (p*p^k)) := by rw [pow_succ,mul_comm]
       _ ≤ Nat.card (attained p)*p^k := lifts _ _ hp.pos (pow_pos hp.pos _)
       _ ≤ 4*n*p^k := Nat.mul_le_mul_right _ base

end FibResidueBound
#print axioms FibResidueBound.count
