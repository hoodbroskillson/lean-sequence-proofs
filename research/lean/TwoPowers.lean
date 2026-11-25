import PeriodDivisor
import Mathlib.RingTheory.Coprime.Lemmas
namespace TwoPowers
open PeriodDivisor PhaseSix
open private PeriodDivisor.lv from PeriodDivisor

private abbrev A (n : ℕ) : ℤ := fib n
private theorem rec (n : ℕ) : A (n+2)=A n+A (n+1) := by
  change ((fib n+fib (n+1):ℕ):ℤ)=_
  exact Nat.cast_add _ _

private theorem double (n : ℕ) : fib (2*n)=fib n*L n := by
  have b (n : ℕ) : A (2*n)=A n*(2*A (n+1)-A n) ∧
      A (2*n+1)=(A n)^2+(A (n+1))^2 := by
    induction n with
    | zero => decide
    | succ n ih =>
      rw [show 2*(n+1)=2*n+2 by omega,show 2*n+2+1=(2*n+1)+2 by omega,rec (2*n+1),rec (2*n),ih.1,ih.2,rec n]
      constructor <;> ring
  have l : (L n:ℤ)=2*A (n+1)-A n := (PeriodDivisor.lv 0 n).1
  exact_mod_cast (show A (2*n)=A n*L n by rw [(b n).1,l])

private theorem periodic (f : ℕ→ℕ) (rec : ∀n, f (n+2)=f n+f (n+1))
    (b : f 24%16=f 0%16 ∧ f 25%16=f 1%16) (n : ℕ) :
    f (n+24)%16=f n%16 ∧ f (n+25)%16=f (n+1)%16 := by
  induction n with
  | zero => exact b
  | succ n ih =>
    refine ⟨ih.2,?_⟩
    change f ((n+24)+2)%16 = f (n+2)%16
    rw [rec (n+24),rec n,Nat.add_mod,Nat.add_mod (f n),ih.1,ih.2]

private theorem small (n : ℕ) : (8∣fib n ↔ 6∣n) ∧ (16∣fib n ↔ 12∣n) ∧
    ¬8∣L n ∧ (6∣n → L n%4=2) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases w : n<24
    · interval_cases n <;> decide
    · obtain ⟨h1,h2,h3,h4⟩:=ih (n-24) (by omega)
      have f := (periodic fib (fun _=>rfl) (by decide) (n-24)).1
      have l := (periodic L (fun _=>rfl) (by decide) (n-24)).1
      rw [show n-24+24=n by omega] at f l
      omega

private theorem lift (k n : ℕ) (hn : 6∣n) : 2^(k+1)∣fib (2*n) ↔ 2^k∣fib n := by
  let s:=L n/4
  have l : L n=2*(2*s+1) := by have h:=(small n).2.2.2 hn; dsimp only [s]; omega
  have cop : IsCoprime (2:ℤ) (2*(s:ℤ)+1) := ⟨-(s:ℤ),1,by ring⟩
  have cp : IsCoprime ((2:ℤ)^k) (2*(s:ℤ)+1) := cop.pow_left
  have h : ((2:ℤ)^(k+1)∣(fib n:ℤ)*(2*(2*(s:ℤ)+1))) ↔ (2:ℤ)^k∣(fib n:ℤ) := by
    rw [pow_succ,mul_comm ((2:ℤ)^k) 2,show (fib n:ℤ)*(2*(2*(s:ℤ)+1))=2*((fib n:ℤ)*(2*(s:ℤ)+1)) by ring,
        mul_dvd_mul_iff_left (by decide : (2:ℤ)≠0)]
    exact ⟨cp.dvd_of_dvd_mul_right,fun a=>dvd_mul_of_dvd_left a _⟩
  rw [double,l]
  exact_mod_cast h

theorem power_fib (k n : ℕ) : 2^(k+3)∣fib n ↔ 6*2^k∣n := by
  induction k generalizing n with
  | zero => simpa using (small n).1
  | succ k ih =>
    by_cases h : 12∣n
    · obtain ⟨r,rfl⟩:=h
      rw [show 12*r=2*(6*r) by ring,show k+1+3=(k+3)+1 by omega,
        lift _ _ (dvd_mul_right 6 r),ih,show 6*2^(k+1)=2*(6*2^k) by rw [pow_succ]; ring,
        Nat.mul_dvd_mul_iff_left (by decide : 0<2)]
    · have d : 16∣2^(k+1+3) := by rw [show k+1+3=k+4 by omega,pow_add]; exact dvd_mul_left _ _
      have e : (12:ℕ)∣6*2^(k+1) := ⟨2^k,by rw [pow_succ]; ring⟩
      exact ⟨fun x=>False.elim (h ((small n).2.1.mp (d.trans x))),fun x=>False.elim (h (e.trans x))⟩

theorem periods (k t : ℕ) : (∃N,Tail (2^(k+3)) N t) ↔ 36*2^k∣t := by
  have e : 8∣2^(k+3) := by rw [pow_add]; exact dvd_mul_left _ _
  have hm : 2≤2^(k+3) := by have := Nat.le_of_dvd (by positivity) e; omega
  have cc (n : ℕ) : (2^(k+3)∣5*fib n) ↔ 2^(k+3)∣fib n := by
    have h : IsCoprime (2:ℤ) 5 := ⟨-2,1,by decide⟩
    have hh : IsCoprime ((2:ℤ)^(k+3)) 5 := h.pow_left
    have z : ((2:ℤ)^(k+3)∣5*(fib n:ℤ)) ↔ (2:ℤ)^(k+3)∣(fib n:ℤ) :=
      ⟨hh.dvd_of_dvd_mul_left,fun x=>dvd_mul_of_dvd_right x _⟩
    exact_mod_cast z
  rw [all_periods hm]
  constructor
  · rintro ⟨q,rfl,h⟩
    rw [periodDivisor] at h
    split_ifs at h with v
    · rw [cc,power_fib] at h
      obtain ⟨s,rfl⟩:=h
      exact ⟨s,by ring⟩
    · exact False.elim ((small q).2.2.1 (e.trans h))
  · rintro ⟨s,rfl⟩
    refine ⟨(6*2^k)*s,by ring,?_⟩
    rw [periodDivisor,if_pos (by rw [Nat.mul_assoc]; omega),cc,power_fib]
    exact dvd_mul_right _ _

private theorem smallDivisor (n : ℕ) :
    (2∣periodDivisor n ↔ 3∣n) ∧ (4∣periodDivisor n ↔ 3∣n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases w : n<24
    · interval_cases n <;> decide
    · obtain ⟨a,b⟩:=ih (n-24) (by omega)
      have f := (periodic fib (fun _=>rfl) (by decide) (n-24)).1
      have l := (periodic L (fun _=>rfl) (by decide) (n-24)).1
      rw [show n-24+24=n by omega] at f l
      simp only [periodDivisor] at a b ⊢
      split_ifs at * <;> omega

theorem small_periods (m t : ℕ) (hm : m=2 ∨ m=4) :
    (∃N,Tail m N t) ↔ 18∣t := by
  rw [all_periods (by omega : 2≤m)]
  have c (q : ℕ) : m∣periodDivisor q ↔ 3∣q := by
    rcases hm with rfl|rfl
    · exact (smallDivisor q).1
    · exact (smallDivisor q).2
  constructor
  · rintro ⟨q,rfl,h⟩
    obtain ⟨r,rfl⟩:=(c q).mp h
    exact ⟨r,by ring⟩
  · rintro ⟨r,rfl⟩
    exact ⟨3*r,by ring,(c _).mpr (dvd_mul_right _ _)⟩

end TwoPowers
#print axioms TwoPowers.power_fib
#print axioms TwoPowers.periods
#print axioms TwoPowers.small_periods
