import FibIdentityFiber
import Batteries.Tactic.OpenPrivate
open private WallLift.U WallLift.recF from WallLift
open private WallValuation.big from WallValuation
open private FibonacciLargeFactor.F_standard from FibonacciLargeFactor
open private FibIdentityFiber.unit_of_reduction FibIdentityFiber.back FibIdentityFiber.fib_period_tower from FibIdentityFiber
namespace FibRegularLifts
open WallTransfer PisanoSource

def regular (p s:ℕ) : Prop :=
  2*(Nat.fib (s+1):ZMod p)-(Nat.fib s:ZMod p)≠0

private def D (m n:ℕ) := (WallLift.U m (n+1))^2-WallLift.U m n*WallLift.U m (n+1)-(WallLift.U m n)^2

private theorem shift_norm (m s i:ℕ) (even:2∣i) : D m (s+i)=D m s := by
  obtain ⟨k,rfl⟩:=even
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show s+2*(k+1)=(s+2*k)+2 by omega,←ih]
    unfold D
    rw [WallLift.recF m ((s+2*k)+1),WallLift.recF m (s+2*k)];ring

private theorem second {p a s i j:ℕ} (pr:p.Prime) (ha:0<a) (reg:regular p s)
    (ei:2∣i) (ej:2∣j) (pi:Fibonacci p i) (pj:Fibonacci p j)
    (eq:WallLift.U (p^a) (s+i)=WallLift.U (p^a) (s+j)) :
    WallLift.U (p^a) (s+i+1)=WallLift.U (p^a) (s+j+1) := by
  let M:=p^a
  let x:=WallLift.U M (s+j)
  let y:=WallLift.U M (s+i+1)
  let z:=WallLift.U M (s+j+1)
  have norm: D M (s+i)=D M (s+j) := (shift_norm M s i ei).trans (shift_norm M s j ej).symm
  unfold D at norm
  rw [eq] at norm
  change y^2-x*y-x^2=z^2-x*z-x^2 at norm
  have unit:IsUnit (y+z-x):=by
    apply FibIdentityFiber.unit_of_reduction pr ha
    have y1:= pi (s+1) (Nat.zero_le _)
    have z1:= pj (s+1) (Nat.zero_le _)
    have x1:= pj s (Nat.zero_le _)
    change (F (s+1+i):ZMod p)=F (s+1) at y1
    change (F (s+1+j):ZMod p)=F (s+1) at z1
    change (F (s+j):ZMod p)=F s at x1
    simp only [x,y,z,WallLift.U,map_add,map_sub,map_natCast]
    rw [show s+i+1=s+1+i by omega,show s+j+1=s+1+j by omega,y1,z1,x1,
      FibonacciLargeFactor.F_standard,FibonacciLargeFactor.F_standard,←two_mul]
    exact reg
  exact unit.mul_right_cancel (a:=y) (c:=z) (by linear_combination norm)

theorem all {p s:ℕ} (pr:p.Prime) (hp:5<p) (ordinary:WallValuation.wallExponent p=1)
    (reg:regular p s) (a r:ℕ) (small:r<p^(a+1)) (same:r%p=Nat.fib s%p) :
    r∈FibResidueBound.attained (p^(a+1)) := by
  let M:=p^(a+1)
  let T:=p^a
  let d:=pi (m:=p) (by omega) (cop pr hp)
  have spec:=pi_spec (m:=p) (by omega) (cop pr hp)
  have modeq (i:ℕ):Fibonacci p (i*d):=(spec.2 _).mpr (dvd_mul_left d i)
  have even:2∣d:=LucasParity.even_period (by omega : 2<p) ((PisanoSource.iff_fib (cop pr hp) _).mpr
    ((spec.2 _).mpr dvd_rfl))
  let f (i:Fin T):ℕ:=Nat.fib (s+i.val*d)%M
  have bound (i:Fin T):f i<M:=Nat.mod_lt _ (pow_pos pr.pos _)
  have same_seed (i:Fin T):f i%p=Nat.fib s%p:=by
    have eq:= modeq i.val s (Nat.zero_le _)
    change (F (s+i.val*d):ZMod p)=F s at eq
    rw [FibonacciLargeFactor.F_standard,FibonacciLargeFactor.F_standard] at eq
    dsimp [f,M]
    rw [Nat.mod_mod_of_dvd _ (by rw [pow_succ];exact dvd_mul_left _ _)]
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp eq
  have ordered (i j:Fin T) (ord:i.val≤j.val) (h:f i=f j) : i.val=j.val := by
    have one:WallLift.U M (s+i.val*d)=WallLift.U M (s+j.val*d):=by
      unfold WallLift.U;rw [FibonacciLargeFactor.F_standard,FibonacciLargeFactor.F_standard]
      exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h
    have two:=second pr (by omega : 0<a+1) reg (dvd_trans even (dvd_mul_left d i.val))
      (dvd_trans even (dvd_mul_left d j.val)) (modeq _) (modeq _) one
    have dt:s+i.val*d+(j.val-i.val)*d=s+j.val*d:=by rw [Nat.add_assoc,←Nat.add_mul];congr 2;omega
    have shift:=FibIdentityFiber.back M (s+i.val*d) ((j.val-i.val)*d)
      (by rw [dt];exact one.symm) (by rw [dt];exact two.symm)
    have dv:=((pi_spec (WallValuation.big hp (by omega : 0<a+1)) ((cop pr hp).pow_right _)).2 _).mp shift
    rw [FibIdentityFiber.fib_period_tower pr hp (by omega),ordinary,show a+1-1=a by omega] at dv
    have div:T∣j.val-i.val:=Nat.dvd_of_mul_dvd_mul_right spec.1 dv
    by_contra ne
    have:=Nat.le_of_dvd (by omega : 0<j.val-i.val) div
    omega
  have quot {v:ℕ} (hv:v<M):v/p<T:=by
    apply (Nat.div_lt_iff_lt_mul pr.pos).mpr
    simpa only [M,T,pow_succ] using hv
  let g (i:Fin T):Fin T:=⟨f i/p,quot (bound i)⟩
  have inj:Function.Injective g:=by
    intro i j e
    have u:=congrArg Fin.val e
    change f i/p=f j/p at u
    have v:f i=f j:=by
      calc f i = f i%p+p*(f i/p) := (Nat.mod_add_div _ _).symm
           _ = f j := by rw [same_seed i,←same_seed j,u,Nat.mod_add_div]
    apply Fin.ext
    rcases Nat.le_total i.val j.val with o|o
    · exact ordered _ _ o v
    · exact (ordered _ _ o v.symm).symm
  obtain ⟨i,hg⟩:=(Finite.surjective_of_injective inj) (⟨r/p,quot small⟩:Fin T)
  have u:=congrArg Fin.val hg
  change f i/p=r/p at u
  refine ⟨s+i.val*d,?_⟩
  calc f i = f i%p+p*(f i/p):=(Nat.mod_add_div _ _).symm
       _=r:=by rw [same_seed i,←same,u,Nat.mod_add_div]

end FibRegularLifts
#print axioms FibRegularLifts.all
