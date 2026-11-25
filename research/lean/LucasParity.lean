import PisanoSource
namespace LucasParity
open LucasZeros LucasPeriods LucasLeast

private theorem recL (m n : ℕ) : (luc (n+4):ZMod m)=luc (n+3)+luc (n+2) := by
  change ((luc (n+3)+luc (n+2):ℕ):ZMod m)=_
  push_cast
  rfl

private theorem norm (m n : ℕ) :
    (luc (n+2):ZMod m)^2+luc (n+2)*luc (n+3)-(luc (n+3):ZMod m)^2=5*(-1)^n := by
  induction n with
  | zero => norm_num [luc]
  | succ i ih =>
    change (luc (i+3):ZMod m)^2+luc (i+3)*luc (i+4)-(luc (i+4):ZMod m)^2=5*(-1)^(i+1)
    rw [recL,pow_succ]
    linear_combination -ih

private theorem mod5 (n : ℕ) : (luc (n+3):ZMod 5)=3*luc (n+2) := by
  induction n with
  | zero => decide
  | succ i ih =>
    change (luc (i+4):ZMod 5)=3*luc (i+3)
    rw [recL,ih]
    have f : (5:ZMod 5)=0 := by decide
    linear_combination -(luc (i+2):ZMod 5)*f

private theorem sq5 (n : ℕ) : (luc (n+2):ZMod 5)^2=4*(-1)^n := by
  induction n with
  | zero => decide
  | succ i ih =>
    change (luc (i+3):ZMod 5)^2=4*(-1)^(i+1)
    rw [mod5,mul_pow,show (3:ZMod 5)^2= -1 by decide,ih,pow_succ]
    ring

theorem even_period {m t : ℕ} (hm : 2<m) (h : Lucas m t) : 2∣t := by
  by_contra bad
  have odd : Odd t := Nat.odd_iff_not_even.mpr (fun he => bad (even_iff_two_dvd.mp he))
  have ht (i:ℕ) (hi:2≤i) : (luc (t+i):ZMod m)=luc i := by
    simpa only [Nat.add_comm t i] using (h i hi : (luc (i+t):ZMod m)=luc i)
  have nn:=norm m t
  rw [ht 2 (by decide),ht 3 (by decide),odd.neg_one_pow] at nn
  change (3:ZMod m)^2+3*4-4^2=5*(-1) at nn
  have z : (10:ZMod m)=0 := by linear_combination nn
  have dvd : m∣10 := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp (by simpa using z)
  have sm:=Nat.le_of_dvd (by decide : 0<10) dvd
  have to5 : 5∣m := by interval_cases m <;> first | decide | contradiction
  have cong := congrArg (ZMod.castHom to5 (ZMod 5)) (ht 2 (by decide))
  simp only [map_natCast] at cong
  have sq:=sq5 t
  rw [cong,odd.neg_one_pow] at sq
  exact (by decide : ¬(luc 2:ZMod 5)^2=4 * -1) sq

theorem source {m : ℕ} (hm : 2<m) (N t : ℕ) :
    FinitePeriod.Tail m N t ↔ t=0 ∨ (5≤N ∧ 3*L (by omega : 1<m)∣t) := by
  have hl:=least_spec (by omega : 1<m)
  have dvd := even_period hm hl.2
  have eq : Nat.lcm 2 (L (by omega : 1<m)) = L (by omega : 1<m) :=
    Nat.dvd_antisymm (Nat.lcm_dvd dvd dvd_rfl) (Nat.dvd_lcm_right _ _)
  simpa only [eq] using LucasLeast.source (by omega : 1<m) N t
end LucasParity
#print axioms LucasParity.even_period
#print axioms LucasParity.source
