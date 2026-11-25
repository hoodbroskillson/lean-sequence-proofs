import SixPair


namespace PeriodDivisor
open PhaseSix SixPair
/-- Classical Lucas numbers in the usual (2,1,3,4,...) indexing. -/
def L : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n+2 => L n + L (n+1)

/-- Classical Fibonacci numbers in the usual (0,1,1,2,...) indexing. -/
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n+2 => fib n + fib (n+1)

private theorem sorted (i : ℕ) : LucasZeros.luc (i+2)=L (i+2) := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    match i with
    | 0 => decide
    | 1 => decide
    | n+2 =>
      have a := ih n (by omega)
      have b := ih (n+1) (by omega)
      change LucasZeros.luc (n+3)+LucasZeros.luc (n+2)=L (n+2)+L (n+3)
      change LucasZeros.luc (n+3)=L (n+3) at b
      rw [a,b,add_comm]

variable (m : ℕ)
private abbrev F (n : ℕ) : ZMod m := fib n
private abbrev V (n : ℕ) : ZMod m := L n
private theorem frec (i : ℕ) : F m (i+2)=F m i+F m (i+1) := by
  simp only [F,show fib (i+2)=fib i+fib (i+1) by rfl,Nat.cast_add]
private theorem vrec (i : ℕ) : V m (i+2)=V m i+V m (i+1) := by
  change ((L i+L (i+1):ℕ):ZMod m)=_
  exact Nat.cast_add _ _

private theorem lv (i : ℕ) : V m i=2*F m (i+1)-F m i ∧
    V m (i+1)=2*F m i+F m (i+1) := by
  induction i with
  | zero => norm_num [F,V,L,fib]
  | succ i ih =>
    change V m (i+1)=2*F m (i+2)-F m (i+1) ∧ V m (i+2)=2*F m (i+1)+F m (i+2)
    rw [vrec,frec,ih.1,ih.2]
    constructor <;> ring

private theorem dbl (q : ℕ) :
    V m (2*q)=2*(F m (q+1))^2-2*F m (q+1)*F m q+3*(F m q)^2 ∧
    V m (2*q+1)=(F m (q+1))^2+4*F m (q+1)*F m q-(F m q)^2 := by
  induction q with
  | zero => norm_num [F,V,L,fib]
  | succ q ih =>
    rw [show 2*(q+1)=2*q+2 by omega]
    change V m (2*q+2)=2*(F m (q+2))^2-2*F m (q+2)*F m (q+1)+3*(F m (q+1))^2 ∧
      V m ((2*q+1)+2)=(F m (q+2))^2+4*F m (q+2)*F m (q+1)-(F m (q+1))^2
    rw [vrec m (2*q+1),vrec m (2*q),ih.1,ih.2,frec]
    constructor <;> ring

private theorem cassini (q : ℕ) : (F m (q+1))^2-F m (q+1)*F m q-(F m q)^2=(-1)^q := by
  induction q with
  | zero => norm_num [F,fib]
  | succ q ih =>
    change (F m (q+2))^2-F m (q+2)*F m (q+1)-(F m (q+1))^2=(-1)^(q+1)
    rw [frec,pow_succ (-1:ZMod m) q,←ih]
    ring

private theorem shift {f : ℕ → ZMod m} (rec : ∀i,f (i+2)=f i+f (i+1)) (i : ℕ) :
    (f i=0 ∧ f (i+1)=0) ↔ (f 0=0 ∧ f 1=0) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [←ih,rec]
    constructor
    · rintro ⟨a,b⟩
      exact ⟨by simpa [a] using b,a⟩
    · rintro ⟨a,b⟩
      exact ⟨b,by simp [a,b]⟩

private theorem atZero (q : ℕ) : (∃N, Tail m N (6*q)) ↔
    (V m (2*q)-2=0 ∧ V m (2*q+1)-1=0) := by
  let f (i : ℕ) := V m (i+2*q)-V m i
  have rc (i : ℕ) : f (i+2)=f i+f (i+1) := by
    dsimp only [f]
    rw [show i+2+2*q=(i+2*q)+2 by omega,show i+1+2*q=(i+2*q)+1 by omega,vrec,vrec]
    ring
  rw [six_iff]
  have zz (i : ℕ) : difference m q i=f (i+4) := by
    dsimp only [difference,f,V]
    rw [show i+4+2*q=(i+2+2*q)+2 by omega,sorted,sorted]
  rw [zz,zz]
  change (f 4=0 ∧ f (4+1)=0) ↔ _
  rw [shift m rc]
  simp only [f,V,Nat.zero_add,Nat.add_comm 1 (2*q),show L 0=2 by rfl,
    show L 1=1 by rfl,Nat.cast_ofNat,Nat.cast_one]

private theorem scalarPair {w : ℕ→ZMod m} (rec : ∀i,w (i+2)=w i+w (i+1))
    (h : w 1=1) (c : ZMod m) (q : ℕ) :
    (c*w q=0 ∧ c*w (q+1)=0) ↔ c=0 := by
  have hh (i : ℕ) : c*w (i+2)=c*w i+c*w (i+1) := by rw [rec,mul_add]
  have hs := @shift m (fun i=>c*w i) hh q
  rw [hs]
  simp only [h,mul_one]
  exact ⟨And.right,by rintro rfl; simp⟩

/-- Divisor whose multiples of six give an eventual period when the modulus divides it. -/
def periodDivisor (q : ℕ) := if q%2=0 then 5*fib q else L q

theorem six_divisor (q : ℕ) : (∃N, Tail m N (6*q)) ↔ m∣periodDivisor q := by
  rw [atZero,←ZMod.natCast_zmod_eq_zero_iff_dvd]
  by_cases h : q%2=0
  · have s : (-1:ZMod m)^q=1 := by
      rw [show q=2*(q/2) by omega,pow_mul]; norm_num
    have a := cassini m q
    rw [s] at a
    have e : V m (2*q)-2=(5*F m q)*F m q := by
      rw [(dbl m q).1]; linear_combination 2*a
    have f : V m (2*q+1)-1=(5*F m q)*F m (q+1) := by
      rw [(dbl m q).2]; linear_combination a
    rw [e,f,scalarPair m (frec m) (by norm_num [F,fib]),periodDivisor,if_pos h,Nat.cast_mul,Nat.cast_ofNat]
  · have s : (-1:ZMod m)^q= -1 := by
      rw [show q=2*(q/2)+1 by omega,pow_succ,pow_mul]; norm_num
    have a := cassini m q
    rw [s] at a
    have e : V m (2*q)-2=V m q*V m q := by
      rw [(dbl m q).1,(lv m q).1]; linear_combination -2*a
    have f : V m (2*q+1)-1=V m q*V m (q+1) := by
      rw [(dbl m q).2,(lv m q).1,(lv m q).2]; linear_combination -a
    rw [e,f,scalarPair m (vrec m) (by norm_num [V,L]),periodDivisor,if_neg h]

theorem all_periods {m t : ℕ} (hm : 2≤m) :
    (∃N, Tail m N t) ↔ ∃q,t=6*q ∧ m∣periodDivisor q := by
  constructor
  · rintro ⟨N,h⟩
    obtain ⟨q,rfl⟩ := PhaseSix.divisible hm h
    exact ⟨q,rfl,(six_divisor _ _).mp ⟨N,h⟩⟩
  · rintro ⟨q,rfl,h⟩
    exact (six_divisor _ _).mpr h

end PeriodDivisor
#print axioms PeriodDivisor.six_divisor
#print axioms PeriodDivisor.all_periods
