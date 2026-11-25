import Apparition
import Mathlib.RingTheory.Coprime.Lemmas
namespace FivePowers
open Apparition
private abbrev F (n : ℕ) : ℤ := Nat.fib n
private theorem recF (n : ℕ) : F (n+2)=F n+F (n+1) := by
  simp only [F,Nat.fib_add_two,Nat.cast_add]

private theorem addF (a b : ℕ) :
    F (a+b)=F a*F (b+1)+(F (a+1)-F a)*F b ∧
    F (a+b+1)=F a*F b+F (a+1)*F (b+1) := by
  induction b with
  | zero => norm_num [F]
  | succ b ih =>
    change F (a+b+1)=F a*F (b+2)+(F (a+1)-F a)*F (b+1) ∧
      F (a+b+2)=F a*F (b+1)+F (a+1)*F (b+2)
    rw [recF (a+b),recF b,ih.1,ih.2]
    constructor <;> ring

private theorem square (n : ℕ) :
    ((F (n+1))^2-F n*F (n+1)-(F n)^2)^2=1 := by
  induction n with
  | zero => norm_num [F]
  | succ n ih =>
    change ((F (n+2))^2-F (n+1)*F (n+2)-(F (n+1))^2)^2=1
    rw [recF,←ih]
    ring

theorem quint (n : ℕ) : ∃c:ℤ, F (5*n)=5*F n*(5*c+1) := by
  let e:ℤ := (F (n+1))^2-F n*F (n+1)-(F n)^2
  refine ⟨(F n)^4+e*(F n)^2,?_⟩
  rw [show 5*n=((n+n)+(n+n))+n by omega,(addF _ _).1,
    (addF (n+n) (n+n)).1,(addF (n+n) (n+n)).2,(addF n n).1,(addF n n).2]
  conv_rhs => rw [←square n]
  dsimp only [e]
  ring

private theorem base : rank (by decide : 0<5)=5 := by
  let r:=rank (by decide : 0<5)
  have h : 0<r ∧ 5∣Nat.fib r := Nat.find_spec (exists_rank (by decide : 0<5))
  have upper : r≤5 := Nat.find_min' (exists_rank (by decide : 0<5)) ⟨by decide,by decide⟩
  change r=5
  have pos:=h.1; have dvd:=h.2
  interval_cases r <;> first | rfl | contradiction

theorem div_iff (k n : ℕ) : 5^k∣Nat.fib n ↔ 5^k∣n := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    by_cases five : 5∣n
    · obtain ⟨v,rfl⟩:=five
      obtain ⟨c,coeff⟩:=quint v
      have cpr : IsCoprime (5:ℤ) (5*c+1) := ⟨-c,1,by ring⟩
      have ip : ((5:ℤ)^(k+1)∣F (5*v)) ↔ (5:ℤ)^k∣F v := by
        rw [coeff,pow_succ',mul_assoc,mul_dvd_mul_iff_left (by decide : (5:ℤ)≠0)]
        exact ⟨(cpr.pow_left).dvd_of_dvd_mul_right,fun d => dvd_mul_of_dvd_left d _⟩
      have natp : 5^(k+1)∣Nat.fib (5*v) ↔ 5^k∣Nat.fib v := by exact_mod_cast ip
      rw [natp,ih,pow_succ',Nat.mul_dvd_mul_iff_left (by decide : 0<5)]
    · have no : ¬5∣Nat.fib n := by
        rw [rank_spec (by decide : 0<5),base]
        exact five
      have d : 5∣5^(k+1) := by rw [pow_succ'];exact dvd_mul_right _ _
      exact ⟨fun h => (no (dvd_trans d h)).elim,fun h => (five (dvd_trans d h)).elim⟩

theorem rank_five (k : ℕ) : rank (b:=5^k) (by positivity)=5^k := by
  refine Nat.dvd_antisymm ?_ ?_
  · rw [←rank_spec _ _,div_iff]
  · have d:= (rank_spec (b:=5^k) (by positivity) _).mpr (dvd_refl _)
    exact (div_iff _ _).mp d

theorem source (k N t : ℕ) :
    FinitePeriod.Tail (5^(k+1)) N t ↔ t=0 ∨ (5≤N ∧ 12*5^k∣t) := by
  have cop : Nat.Coprime 2 (5^k) := Nat.Coprime.pow_right _ (by decide)
  have eq : Nat.lcm 2 (5^k)=2*5^k := cop.lcm_eq_mul
  rw [pow_succ' 5 k,Apparition.source (by positivity),rank_five,eq,←Nat.mul_assoc]
end FivePowers
#print axioms FivePowers.div_iff
#print axioms FivePowers.source
