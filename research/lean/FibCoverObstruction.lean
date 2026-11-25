import FibonacciLargeFactor
import Batteries.Tactic.OpenPrivate
open private FibonacciLargeFactor.F_standard from FibonacciLargeFactor
open private WallValuation.stationary from WallValuation
open private WallLift.U from WallLift
namespace FibCoverObstruction
open WallTransfer PisanoSource

def shift (p t:ℕ):Prop:=∀n,Nat.fib (n+t)%p=Nat.fib n%p

/-- One zero in a full period, counting indices from zero. A period with this
property is necessarily the least period. -/
def oneZero (p:ℕ):Prop:=∃t,0<t ∧ shift p t ∧ ∀i<t,Nat.fib i%p=0 → i=0

def covers (p k:ℕ):Prop:=∀n,∃j<k,Nat.fib j%p=Nat.fib n%p
def least (p k:ℕ):Prop:=covers p k ∧ ∀i<k,¬covers p i

private theorem bridge (p t:ℕ) : shift p t ↔ Fibonacci p t := by
  constructor
  · intro h n _
    change (F (n+t):ZMod p)=F n
    rw [FibonacciLargeFactor.F_standard,FibonacciLargeFactor.F_standard]
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (h n)
  · intro h n
    have e:=h n (Nat.zero_le _)
    change (F (n+t):ZMod p)=F n at e
    rw [FibonacciLargeFactor.F_standard,FibonacciLargeFactor.F_standard] at e
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp e

private theorem mult {p t:ℕ} (h:shift p t) (k n:ℕ) : Nat.fib (n+k*t)%p=Nat.fib n%p := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.succ_mul,←Nat.add_assoc,h _,ih]

private theorem reduce {p t:ℕ} (h:shift p t) (n:ℕ): Nat.fib n%p=Nat.fib (n%t)%p := by
  have a:=mult h (n/t) (n%t)
  rwa [Nat.mul_comm (n/t) t,Nat.mod_add_div] at a

private theorem zero_index {p t n:ℕ} (h:shift p t) (ht:0<t)
    (zero:∀i<t,Nat.fib i%p=0 → i=0) (hd:p∣Nat.fib n) : t∣n :=
  Nat.dvd_of_mod_eq_zero <| zero _ (Nat.mod_lt _ ht) ((reduce h n).symm.trans (Nat.mod_eq_zero_of_dvd hd))

private theorem cover_short {p t:ℕ} (h:shift p t) (gt:2<t) : covers p (t-1):=by
  have z:=h 0;have o:=h 1
  simp only [Nat.zero_add,Nat.fib_zero,Nat.zero_mod] at z
  rw [show 1+t=(t-1)+2 by omega,Nat.fib_add_two,show t-1+1=t by omega,Nat.add_mod,z,Nat.add_zero,Nat.mod_mod] at o
  intro n
  have v:=reduce h n
  have bound:=Nat.mod_lt n (show 0<t by omega)
  by_cases low:n%t<t-1
  · exact ⟨n%t,low,v.symm⟩
  · exact ⟨1,by omega,by rw [v,show n%t=t-1 by omega];exact o.symm⟩

theorem strict {p:ℕ} (pr:p.Prime) (hp:5<p) (single:oneZero p) : covers p (p-2) := by
  letI : Fact p.Prime:=⟨pr⟩
  obtain ⟨t,tp,h,zero⟩:=single
  have fib0:=h 0
  simp only [Nat.zero_add,Nat.fib_zero,Nat.zero_mod] at fib0
  have one:1%p=1:=Nat.mod_eq_of_lt (by omega)
  have pos:2<t:=by
    by_contra! le
    interval_cases t <;> simp_all
  have s:=pi_spec (m:=p) (by omega) (cop pr hp)
  have fs:p∣Nat.fib (WallResidue.index p):=by simpa using
    (WallValuation.stationary (a:=1) pr hp (by decide)).mp (by simpa using (s.2 _).mpr dvd_rfl)
  have dx:=zero_index h tp zero fs
  have split:p%5=1 ∨ p%5=4:=by
    by_contra bad
    rw [WallResidue.index,if_neg bad] at dx
    obtain ⟨k,e⟩:=dx
    have period:shift p (p+1):=by
      intro n;rw [e,Nat.mul_comm t k];exact mult h _ _
    have pd:LucasLeast.L (m:=p) (by omega)∣p+1 :=
      ((PisanoSource.pisano (by omega) (cop pr hp)).2 _).mp ((bridge _ _).mp period)
    have source:FinitePeriod.Tail p 5 (3*(p+1)):=(LucasParity.source (by omega : 2<p) _ _).mpr
      (Or.inr ⟨le_rfl,Nat.mul_dvd_mul_left _ pd⟩)
    have non:p%5≠0:=fun z=>by have:= (Nat.dvd_prime pr).mp (Nat.dvd_of_mod_eq_zero z : 5∣p);omega
    exact ((ResidueBounds.residues (by omega : 2<p)).2 (by omega)).2 5 source
  rw [WallResidue.index,if_pos split] at dx
  have le:=Nat.le_of_dvd (by omega : 0<p-1) dx
  intro n
  obtain ⟨j,lo,e⟩:=cover_short h pos n
  exact ⟨j,by omega,e⟩

theorem contradicts {p:ℕ} (pr:p.Prime) (hp:5<p) (h:oneZero p) : ¬least p (p-1) :=
  fun claim=>claim.2 (p-2) (by omega) (strict pr hp h)

private theorem period11:shift 11 10:=(bridge _ _).mpr ((PowerLift.state _ _).mpr ⟨by decide,by decide⟩)

theorem eleven : Nat.Prime 11 ∧ oneZero 11 ∧ least 11 9 := by
  refine ⟨by decide,⟨10,by decide,period11,?_⟩,?_,?_⟩
  · intro i hi
    interval_cases i <;> decide
  · intro n
    let r:Fin 10:=⟨n%10,Nat.mod_lt _ (by decide)⟩
    have finite:∀r:Fin 10, ∃j:Fin 9, Nat.fib j.val%11=Nat.fib r.val%11:=by decide
    obtain ⟨j,h⟩:=finite r
    exact ⟨j.val,j.isLt,h.trans (reduce period11 n).symm⟩
  · intro i small covers
    obtain ⟨j,lo,bad⟩:=covers 8
    have max:j<8:=by omega
    interval_cases j <;> contradiction
end FibCoverObstruction
#print axioms FibCoverObstruction.strict
#print axioms FibCoverObstruction.contradicts
#print axioms FibCoverObstruction.eleven
