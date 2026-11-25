import FamilyBalance
import FamilySharpness
namespace MexFamily

/-- The exact discrepancy spectrum of positive equal-length windows is the whole interval
from zero through s+1, for every s≥2 at t=1 in the original mex construction. -/
theorem exact_range (q : Params) (v : ℕ) : v≤q.s+1 ↔
    ∃m n j : ℕ, 0<m ∧ 0<n ∧ 0<j ∧ D q m n j=v := by
  constructor
  · intro hv
    cases v with
    | zero => exact ⟨1,1,1,by decide,by decide,by decide,by simp [D]⟩
    | succ h =>
      obtain ⟨m,n,j,hm,hn,hj,eq⟩:=Extremal.range_attained q h (by omega)
      refine ⟨m,n,j,hm,hn,hj,?_⟩
      have am:=(strictA q).monotone (show m≤m+j by omega)
      have an:=(strictA q).monotone (show n≤n+j by omega)
      have e : (A q (m+j):ℤ)-A q m=((A q (n+j):ℤ)-A q n)+(h+1) := by
        omega
      unfold D
      rw [e]
      have y : (A q (n+j):ℤ)-A q n+(h+1)-((A q (n+j):ℤ)-A q n)=(h:ℤ)+1 := by ring
      rw [y,abs_of_nonneg (by positivity)];rfl
  · rintro ⟨m,n,j,_,_,_,e⟩
    have b:=improved q m n j
    rw [e] at b
    exact_mod_cast b
end MexFamily
#print axioms MexFamily.exact_range
