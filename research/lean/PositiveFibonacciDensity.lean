import SmallFibonacciDensities
import FibIdentityFiber
namespace PositiveFibonacciDensity
noncomputable section
open SmallFibonacciDensities FibResidueBound

/-- Uniform positive lower estimate, with the Wall–Sun–Sun valuation included. -/
theorem estimate {p:ℕ} (pr:p.Prime) (hp:5<p) :
    1/(p:ℝ)^WallValuation.wallExponent p ≤ dens p := by
  apply le_ciInf
  intro a
  let w:=WallValuation.wallExponent p
  have lower:p^(a-w)≤Nat.card (attained (p^a)):=by
    cases a with
    | succ k => exact FibIdentityFiber.lower pr hp (by omega)
    | zero =>
      simp only [Nat.zero_sub,pow_zero]
      letI : Nonempty (attained 1):=⟨⟨_,0,rfl⟩⟩
      letI : Finite (attained 1):=(finite 1 (by decide)).to_subtype
      exact Nat.card_pos
  have sub : p^a ≤ p^(a-w)*p^w := by
    rw [←pow_add]
    exact Nat.pow_le_pow_right pr.pos (by omega)
  have eq:=sub.trans (Nat.mul_le_mul_right (p^w) lower)
  change (1:ℝ)/(p:ℝ)^w ≤ (Nat.card (attained (p^a)):ℝ)/(p:ℝ)^a
  rw [div_le_div_iff (by positivity) (by positivity),one_mul]
  exact_mod_cast eq

theorem positive {p:ℕ} (pr:p.Prime) (hp:5<p) : 0<dens p := by
  exact lt_of_lt_of_le (by positivity) (estimate pr hp)

/-- Every positive neighborhood above zero contains a strictly positive prime
density, even after an arbitrary finite set of primes is omitted. -/
theorem zero_accumulation (ε:ℝ) (he:0<ε) (B:ℕ) :
    ∃p:ℕ, p.Prime ∧ B<p ∧ 0<dens p ∧ dens p<ε := by
  obtain ⟨p,pr,h,_,lt,_⟩:=arbitrarily_small ε he (max B 5)
  exact ⟨p,pr,(le_max_left _ _).trans_lt h,positive pr ((le_max_right _ _).trans_lt h),lt⟩

end
end PositiveFibonacciDensity
#print axioms PositiveFibonacciDensity.estimate
#print axioms PositiveFibonacciDensity.zero_accumulation
