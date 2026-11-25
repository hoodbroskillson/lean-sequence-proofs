import FamilyForward
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace MexFamily
namespace Extremal

private def difference (a b c d : ℕ) : ℤ := (a:ℤ)+b-c-d
private def len (q : Params) (a b c d i j k l : ℕ) :
    difference (W q a+i) (W q b+j) (W q c+k) (W q d+l) =
    (q.s:ℤ)*difference a b c d +difference (C q a) (C q b) (C q c) (C q d)
      + difference i j k l := by
  unfold W difference
  push_cast;ring

private theorem counts (q : Params) (a b c d i j k l : ℕ)
    (hi : i≤q.s) (hj : j≤q.s) (hk : k≤q.s) (hl : l≤q.s) :
    difference (C q (W q a+i)) (C q (W q b+j)) (C q (W q c+k)) (C q (W q d+l)) =
     (q.s:ℤ)*difference a b c d +difference i j k l := by
  rw [forward q _ _ hi,forward q _ _ hj,forward q _ _ hk,forward q _ _ hl]
  unfold difference
  push_cast;ring

private theorem ordered (q : Params) {a b : ℕ} (h : a<b) : W q a+q.s≤W q b := by
  have mul:=Nat.mul_le_mul_left q.s (show a+1≤b by omega)
  have c:=C_mono q h.le
  unfold W
  rw [Nat.mul_add,Nat.mul_one] at mul
  omega

/-- A pair of factors with lengths differing by one and lower-column letter
counts differing by k. Each step of the induction uses the substitution twice. -/
private theorem ext_windows (q : Params) (j:ℕ) (hj:j≤q.s) :
    ∃ a b c d : ℕ, d<a ∧ b≤c ∧ difference a b c d=1 ∧
       difference (C q a) (C q b) (C q c) (C q d)=(j+1:ℕ) := by
  induction j with
  | zero =>
    have cz : C q 0=0 := by have := C_le q 0;omega
    have co : C q 1=1 := by
      have z:=C_le q 1
      by_contra! h
      have zero : C q 1=0 := by omega
      have u:=(C_spec q 1).2
      rw [zero] at u
      norm_num [(starts q).2.2] at u
    exact ⟨1,0,0,0,by decide,by decide,by decide,by simp [difference,co,cz]⟩
  | succ j ih =>
    obtain ⟨a,b,c,d,ord₁,ord₂,L,P⟩:=ih (by omega)
    let k:=j+1
    have hk : k≤q.s := hj
    have h₁ : 1≤q.s := by have:=q.ge;omega
    let a':=W q a+0
    let b':=W q b+0
    let c':=W q c+q.s
    let d':=W q d+k
    have L₁ : difference a' b' c' d'=0 := by
      rw [show difference a' b' c' d'=_ from len q a b c d 0 0 q.s k,L,P]
      simp [difference,k]
    have P₁ : difference (C q a') (C q b') (C q c') (C q d')= -(k:ℤ) := by
      rw [show difference (C q a') (C q b') (C q c') (C q d')=_ from
        counts q a b c d 0 0 q.s k (by omega) (by omega) le_rfl hk,L]
      simp [difference]; ring
    have od' : d'≤a' := by
      have := ordered q ord₁
      dsimp [d',a'];omega
    have ob' : b'<c' := by
      have le:=Nat.mul_le_mul_left q.s ord₂
      have cb:=C_mono q ord₂
      dsimp [b',c',W];omega
    refine ⟨W q a'+k,W q b'+1,W q c'+0,W q d'+0,?_,?_,?_,?_⟩
    · have le:=Nat.mul_le_mul_left q.s od'
      have cd:=C_mono q od'
      dsimp [W,k];omega
    · have := ordered q ob';omega
    · rw [len,L₁,P₁]
      simp [difference]
    · rw [counts q _ _ _ _ _ _ _ _ hk h₁ (by omega) (by omega),L₁]
      simp [difference,k]

private theorem windows_arithmetic (m n j a b c d h : ℕ) (da:d≤a) (bc:b≤c)
    (diff : difference a b c d=(h+1:ℕ)) :
    (m+j+a)-(m+d)=((n+j+c)-(n+b))+(h+1) := by
  unfold difference at diff
  omega

/-- For every s≥2, some two source gap windows of the same positive length
attain the discrepancy s+1. All initial indices are positive. -/
theorem range_attained (q : Params) (h : ℕ) (hh : h≤q.s) : ∃m n j : ℕ, 0<m ∧ 0<n ∧ 0<j ∧
    A q (m+j)-A q m = (A q (n+j)-A q n)+(h+1) := by
  obtain ⟨a,b,c,d,da,bc,L,P⟩:=ext_windows q h hh
  let t:=c-b
  have left : a=d+t+1 := by unfold difference at L;dsimp [t];omega
  have right : c=b+t := by dsimp [t];omega
  let m:=q.s*(d+1)
  let n:=q.s*b+1
  let j:=q.s*t+1
  have sge:=q.ge
  have sp : 0<q.s := by omega
  have mm : (m-1)/q.s=d := by
    apply Nat.div_eq_of_lt_le ?_ ?_
    · dsimp [m];rw [Nat.mul_add,Nat.mul_one];simpa [Nat.mul_comm] using
        (show q.s*d≤q.s*d+q.s-1 by omega)
    · dsimp [m];rw [Nat.mul_comm (d+1)];have := Nat.mul_pos sp (show 0<d+1 by omega);omega
  have nn : (n-1)/q.s=b := by dsimp [n];simp [Nat.mul_div_cancel_left _ sp]
  have me : (m+j-1)/q.s=a := by
    have e : m+j-1=q.s*a := by dsimp [m,j];rw [left];simp [Nat.mul_add];omega
    rw [e,Nat.mul_div_cancel_left _ sp]
  have ne : (n+j-1)/q.s=c := by
    have e : n+j-1=q.s*c+1 := by dsimp [n,j];rw [right,Nat.mul_add];omega
    rw [e,Nat.mul_add_div sp,Nat.div_eq_of_lt (show 1<q.s by omega)];omega
  refine ⟨m,n,j,by dsimp [m]; exact Nat.mul_pos sp (by omega),Nat.zero_lt_succ _,Nat.zero_lt_succ _,?_⟩
  rw [compress q (m+j),compress q m,compress q (n+j),compress q n,me,mm,ne,nn]
  have ainc:=C_mono q da.le
  have binc:=C_mono q bc
  exact windows_arithmetic m n j _ _ _ _ h ainc binc P

theorem attained (q : Params) : ∃m n j : ℕ, 0<m ∧ 0<n ∧ 0<j ∧
    A q (m+j)-A q m = (A q (n+j)-A q n)+(q.s+1) := range_attained q q.s le_rfl

end Extremal
end MexFamily
#print axioms MexFamily.Extremal.range_attained
#print axioms MexFamily.Extremal.attained
