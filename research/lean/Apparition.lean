import LucasParity
import PeriodDivisor
import Mathlib.Data.Nat.Fib.Basic
namespace Apparition
open PeriodDivisor

theorem standard (n : ℕ) : fib n=Nat.fib n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | k+2 => rw [fib,Nat.fib_add_two,ih k (by omega),ih (k+1) (by omega)]

private theorem nofive (n : ℕ) : ¬5∣L n := by
  have ratio (i : ℕ) : (L (i+1):ZMod 5)=3*L i := by
    induction i with
    | zero => decide
    | succ k ih =>
      change ((L k+L (k+1):ℕ):ZMod 5)=3*L (k+1)
      rw [Nat.cast_add,ih]
      have co:(5:ZMod 5)=0:=by decide
      linear_combination -(L k:ZMod 5)*co
  have nz (i : ℕ) : (L i:ZMod 5)≠0 := by
    induction i with
    | zero => decide
    | succ k ih =>
      rw [ratio];intro hz;apply ih
      have five : (5:ZMod 5)=0 := by decide
      linear_combination 2*hz-(L k:ZMod 5)*five
  exact fun d => nz n ((ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr d)

theorem multiple {b : ℕ} (hb : 0<b) (t : ℕ) :
    (∃N, FinitePeriod.Tail (5*b) N t) ↔ ∃s,t=12*s ∧ b∣Nat.fib (2*s) := by
  change (∃N, PhaseSix.Tail (5*b) N t) ↔ _
  rw [all_periods (by omega : 2≤5*b)]
  constructor
  · rintro ⟨q,hq,d⟩
    by_cases h:q%2=0
    · rw [periodDivisor,if_pos h] at d
      have dd : b∣fib q := (Nat.dvd_of_mul_dvd_mul_left (by decide : 0<5) d)
      refine ⟨q/2,by omega,?_⟩
      simpa only [show 2*(q/2)=q by omega,←standard] using dd
    · rw [periodDivisor,if_neg h] at d
      exact False.elim (nofive q (dvd_trans (dvd_mul_right 5 b) d))
  · rintro ⟨s,hs,d⟩
    refine ⟨2*s,by omega,?_⟩
    rw [periodDivisor,if_pos (by omega : 2*s%2=0),standard]
    exact Nat.mul_dvd_mul_left _ d

theorem exists_rank {b : ℕ} (hb : 0<b) : ∃n,0<n ∧ b∣Nat.fib n := by
  have hm : 1<5*b:=by omega
  let T:=3*Nat.lcm 2 (LucasLeast.L hm)
  have pos : 0<T := LucasLeast.positive hm
  have ht:= (LucasLeast.source hm 5 T).mpr (Or.inr ⟨le_rfl,dvd_rfl⟩)
  obtain ⟨s,e,ds⟩ := (multiple hb T).mp ⟨5,ht⟩
  exact ⟨2*s,by omega,ds⟩

noncomputable def rank {b : ℕ} (hb : 0<b) := Nat.find (exists_rank hb)

theorem rank_spec {b : ℕ} (hb : 0<b) (n : ℕ) : b∣Nat.fib n ↔ rank hb∣n := by
  have s : 0<rank hb ∧ b∣Nat.fib (rank hb) := Nat.find_spec (exists_rank hb)
  constructor
  · intro d
    let g:=Nat.gcd (rank hb) n
    have ds : b∣Nat.fib g := by rw [Nat.fib_gcd];exact Nat.dvd_gcd s.2 d
    have low : rank hb≤g := Nat.find_min' (exists_rank hb) ⟨Nat.gcd_pos_of_pos_left n s.1,ds⟩
    have high : g≤rank hb := Nat.le_of_dvd s.1 (Nat.gcd_dvd_left _ _)
    have eg : g=rank hb := by omega
    exact eg ▸ (Nat.gcd_dvd_right (rank hb) n : g∣n)
  · exact fun h => dvd_trans s.2 (Nat.fib_dvd _ _ h)

theorem source {b : ℕ} (hb : 0<b) (N t : ℕ) :
    FinitePeriod.Tail (5*b) N t ↔ t=0 ∨ (5≤N ∧ 6*Nat.lcm 2 (rank hb)∣t) := by
  have hm : 1<5*b:=by omega
  have equiv : (∃N, FinitePeriod.Tail (5*b) N t) ↔ 6*Nat.lcm 2 (rank hb)∣t := by
    rw [multiple hb]
    constructor
    · rintro ⟨s,rfl,d⟩
      simpa only [←Nat.mul_assoc] using Nat.mul_dvd_mul_left 6
        (Nat.lcm_dvd (dvd_mul_right 2 s) ((rank_spec hb _).mp d))
    · rintro ⟨k,hk⟩
      let z:=Nat.lcm 2 (rank hb)*k
      have hz : 2∣z := dvd_trans (Nat.dvd_lcm_left _ _) (dvd_mul_right _ _)
      obtain ⟨s,hs⟩:=hz
      refine ⟨s,?_,(rank_spec hb _).mpr ?_⟩
      · rw [Nat.mul_assoc] at hk
        change t=6*z at hk
        omega
      · rw [←hs]
        exact dvd_trans (Nat.dvd_lcm_right _ _) (dvd_mul_right _ _)
  by_cases zero : t=0
  · subst t;simp [FinitePeriod.Tail,TailGcd.From]
  rw [or_iff_right zero]
  constructor
  · intro h
    have le:=((LucasLeast.source hm N t).mp h).resolve_left zero
    exact ⟨le.1,equiv.mp ⟨N,h⟩⟩
  · rintro ⟨lt,d⟩
    obtain ⟨K,hK⟩:=equiv.mpr d
    have val:=((LucasLeast.source hm K t).mp hK).resolve_left zero
    exact (LucasLeast.source hm N t).mpr (Or.inr ⟨lt,val.2⟩)

end Apparition
#print axioms Apparition.source
#print axioms Apparition.rank_spec
