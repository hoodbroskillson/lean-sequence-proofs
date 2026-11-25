import LucasParity
import Mathlib.FieldTheory.Finite.Basic
namespace RootOrders
open LucasPeriods LucasZeros

variable {K : Type*} [Field K]
private def u (r : K) (n : ℕ) := r^n+(1-r)^n
private theorem recU (r : K) (hr : r^2=r+1) (n : ℕ) :
    u r (n+2)=u r (n+1)+u r n := by
  have hc : (1-r)^2=(1-r)+1 := by linear_combination hr
  simp only [u,pow_add,hr,hc,pow_one]
  ring

private theorem bridge (r : K) (hr : r^2=r+1) (n : ℕ) : (luc (n+2):K)=u r (n+2) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => change (3:K)=u r 2;rw [recU r hr 0];simp [u];ring
    | 1 =>
      change (4:K)=u r 3
      rw [recU r hr 1,recU r hr 0]
      simp [u];ring
    | d+2 =>
      change ((luc (d+3)+luc (d+2):ℕ):K)=u r ((d+2)+2)
      rw [Nat.cast_add,recU r hr,ih (d+1) (by omega),ih d (by omega)]

theorem character {p : ℕ} [Fact p.Prime] (hp : 2<p) (f : ZMod p →+* K)
    (r : K) (hr:r^2=r+1) (t : ℕ) :
    Lucas p t ↔ Nat.lcm 2 (orderOf r) ∣ t := by
  have rs : r*(1-r)= -1 := by linear_combination -hr
  have rule (n : ℕ) (hn : 2≤n) : (luc n:K)=u r n := by
    simpa only [show n-2+2=n by omega] using bridge r hr (n-2)
  constructor
  · intro h
    have even := LucasParity.even_period hp h
    have vals (i:ℕ) (hi:2≤i) : u r (t+i)=u r i := by
      have e := congrArg f (h i hi : (luc (i+t):ZMod p)=luc i)
      simpa only [map_natCast,Nat.add_comm i t,rule _ (by omega : 2≤t+i),rule _ hi] using e
    have base : u r t=2 := by
      have e:=recU r hr t; have d:=recU r hr (t+1)
      rw [show t+1+2=t+3 by omega,show t+1+1=t+2 by omega,vals 2 (by decide), vals 3 (by decide)] at d
      rw [vals 2 (by decide)] at e
      rw [←rule 2 (by decide)] at d e
      rw [←rule 3 (by decide)] at d
      change (3:K)=u r (t+1)+u r t at e
      change (4:K)=3+u r (t+1) at d
      linear_combination -e+d
    have prod : r^t*(1-r)^t=1 := by
      rw [←mul_pow,rs]
      obtain ⟨k,rfl⟩:=even
      rw [pow_mul];norm_num
    have sq : (r^t-1)^2=0 := by
      change r^t+(1-r)^t=2 at base
      linear_combination r^t*base-prod
    exact Nat.lcm_dvd even (orderOf_dvd_iff_pow_eq_one.mpr (sub_eq_zero.mp (sq_eq_zero_iff.mp sq)))
  · intro h
    have even:=dvd_trans (Nat.dvd_lcm_left _ _) h
    have root : r^t=1 := orderOf_dvd_iff_pow_eq_one.mp (dvd_trans (Nat.dvd_lcm_right _ _) h)
    have other : (1-r)^t=1 := by
      have prod : r^t*(1-r)^t=1 := by
        rw [←mul_pow,rs]
        obtain ⟨k,rfl⟩:=even
        rw [pow_mul];norm_num
      simpa only [root,one_mul] using prod
    intro n hn
    apply f.injective
    change f (luc (n+t):ZMod p)=f (luc n:ZMod p)
    rw [map_natCast,map_natCast,rule _ (by omega),rule _ hn]
    simp [u,pow_add,root,other]

theorem least {p : ℕ} [Fact p.Prime] (hp : 2<p) (f : ZMod p →+* K)
    (r : K) (hr:r^2=r+1) : LucasLeast.L (by omega : 1<p)=Nat.lcm 2 (orderOf r) := by
  apply Nat.dvd_antisymm
  · rw [←LucasLeast.lucas_iff,character hp f r hr]
  · rw [←character hp f r hr]
    exact (LucasLeast.least_spec _).2

theorem source {p : ℕ} [Fact p.Prime] (hp : 2<p) (f : ZMod p →+* K)
    (r : K) (hr:r^2=r+1) (N t : ℕ) :
    FinitePeriod.Tail p N t ↔ t=0 ∨ (5≤N ∧ 3*Nat.lcm 2 (orderOf r)∣t) := by
  simpa only [least hp f r hr] using LucasParity.source hp N t

end RootOrders
#print axioms RootOrders.character
#print axioms RootOrders.source
