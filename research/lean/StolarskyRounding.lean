import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
namespace StolarskyRounding

/-- No tie is possible in the nearest-integer operation of the Stolarsky array. -/
theorem no_half (a k : ℤ) : (a:ℝ)*((1+Real.sqrt 5)/2) ≠ (k:ℝ)+1/2 := by
  intro h
  have v : (a:ℝ)*Real.sqrt 5 = 2*(k:ℝ)+1-a := by linarith
  have e : (2*(k:ℝ)+1-a)^2=5*(a:ℝ)^2 := by
    rw [←v,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤5)]
    ring
  have z : (2*k+1-a)^2=5*a^2 := by exact_mod_cast e
  have odd : 2*(2*k^2+2*k-2*k*a-a-2*a^2)+1=0 := by linear_combination z
  omega
end StolarskyRounding
#print axioms StolarskyRounding.no_half
