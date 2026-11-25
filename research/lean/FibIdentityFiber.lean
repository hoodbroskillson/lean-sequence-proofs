import FibonacciLargeFactor
import FibResidueLifts
import Batteries.Tactic.OpenPrivate
open private WallLift.U WallLift.addF WallLift.recF from WallLift
open private WallValuation.big from WallValuation
open private FibonacciLargeFactor.F_standard from FibonacciLargeFactor
namespace FibIdentityFiber
open PisanoSource WallTransfer

private theorem even_cassini (m r:ℕ) :
    (WallLift.U m (2*r+1))^2-WallLift.U m (2*r)*WallLift.U m (2*r+1)-(WallLift.U m (2*r))^2=1 := by
  induction r with
  | zero => norm_num [WallLift.U,F]
  | succ k ih =>
    rw [show 2*(k+1)=2*k+2 by omega,WallLift.recF m (2*k+1),WallLift.recF m (2*k)]
    linear_combination ih

private theorem unit_of_reduction {p a:ℕ} (hp:p.Prime) (ha:0<a) (x:ZMod (p^a))
    (nz:ZMod.castHom (by simpa using pow_dvd_pow p (show 1≤a by omega)) (ZMod p) x≠0) :
    IsUnit x := by
  letI : NeZero (p^a):=⟨pow_ne_zero _ hp.ne_zero⟩
  have cp:=hp.coprime_iff_not_dvd.mpr (show ¬p∣x.val from by
    intro h
    apply nz
    rw [←ZMod.natCast_zmod_val x,map_natCast]
    exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr h)
  rw [←ZMod.natCast_zmod_val x,ZMod.isUnit_iff_coprime] 
  exact cp.symm.pow_right _

private theorem back (m s t:ℕ) :
    WallLift.U m (s+t)=WallLift.U m s → WallLift.U m (s+t+1)=WallLift.U m (s+1) →
    Fibonacci m t := by
  induction s with
  | zero =>
    simp only [Nat.zero_add]
    exact fun u v=>(PowerLift.state _ _).mpr ⟨by simpa [WallLift.U,F] using u,by simpa [WallLift.U,F] using v⟩
  | succ s ih =>
    intro u v
    rw [show s+1+t=s+t+1 by omega] at u v
    rw [WallLift.recF m (s+t),WallLift.recF m s,u] at v
    exact ih (add_left_cancel v) u

private theorem same_second {p a i j:ℕ} (prime:p.Prime) (hp:5<p) (ha:0<a)
    (hi:2∣i) (hj:2∣j) (state_i:Fibonacci p i) (state_j:Fibonacci p j)
    (eq:WallLift.U (p^a) i=WallLift.U (p^a) j) :
    WallLift.U (p^a) (i+1)=WallLift.U (p^a) (j+1) := by
  obtain ⟨u,rfl⟩:=hi
  obtain ⟨v,rfl⟩:=hj
  let M:=p^a
  let x:=WallLift.U M (2*v)
  let y:=WallLift.U M (2*u+1)
  let z:=WallLift.U M (2*v+1)
  have ci:=even_cassini M u
  have cj:=even_cassini M v
  rw [eq] at ci
  change y^2-x*y-x^2=1 at ci
  change z^2-x*z-x^2=1 at cj
  have unit:IsUnit (y+z-x):=by
    apply unit_of_reduction prime ha
    obtain ⟨_,y1⟩:=(PowerLift.state _ _).mp state_i
    obtain ⟨x0,z1⟩:=(PowerLift.state _ _).mp state_j
    simp only [x,y,z,WallLift.U,map_add,map_sub,map_natCast] at *
    rw [y1,z1,x0,sub_zero]
    have nonzero:(2:ZMod p)≠0:=by
      have nd:¬p∣2:=by intro h;have:=Nat.le_of_dvd (by decide : 0<2) h;omega
      simpa only [Nat.cast_ofNat] using (ZMod.natCast_zmod_eq_zero_iff_dvd 2 p).not.mpr nd
    convert nonzero using 1; ring
  exact unit.mul_right_cancel (a:=y) (c:=z) (by linear_combination ci-cj)

private theorem fib_period_tower {p a:ℕ} (pr:p.Prime) (hp:5<p) (ha:0<a) :
    pi (WallValuation.big hp ha) ((cop pr hp).pow_right _)
      =p^(a-WallValuation.wallExponent p)*pi (m:=p) (by omega) (cop pr hp) := by
  have tower:=WallValuation.all_powers pr hp ha
  rw [periods (WallValuation.big hp ha) ((cop pr hp).pow_right a),periods (by omega : 2<p) (cop pr hp)] at tower
  nlinarith only [tower]

/-- At precision p^a the identity state modulo p gives at least p^(a-w)
distinct attained first coordinates, even if the first lifting step is stationary. -/
theorem lower {p a:ℕ} (pr:p.Prime) (hp:5<p) (ha:0<a) :
    p^(a-WallValuation.wallExponent p) ≤ Nat.card (FibResidueBound.attained (p^a)) := by
  let T:=p^(a-WallValuation.wallExponent p)
  let d:=pi (m:=p) (by omega) (cop pr hp)
  let M:=p^a
  let f (i:Fin T) : FibResidueBound.attained M := ⟨Nat.fib (i.val*d)%M,⟨i.val*d,rfl⟩⟩
  have modeq (i:ℕ): Fibonacci p (i*d) := (pi_spec (by omega) (cop pr hp)).2 _ |>.mpr (dvd_mul_left d i)
  have even:2∣d := LucasParity.even_period (by omega : 2<p) ((PisanoSource.iff_fib (cop pr hp) _).mpr
    ((pi_spec (by omega) (cop pr hp)).2 _ |>.mpr dvd_rfl))
  have ordered (i j : Fin T) (ord:i.val≤j.val) (z:f i=f j) : i.val=j.val := by
    have e:=congrArg Subtype.val z
    change Nat.fib (i.val*d)%M=Nat.fib (j.val*d)%M at e
    have one:WallLift.U M (i.val*d)=WallLift.U M (j.val*d):=by
      unfold WallLift.U;rw [FibonacciLargeFactor.F_standard,FibonacciLargeFactor.F_standard]
      exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr e
    have two:=same_second pr hp ha (dvd_trans even (dvd_mul_left d i.val))
      (dvd_trans even (dvd_mul_left d j.val)) (modeq _) (modeq _) one
    have dt:i.val*d+(j.val-i.val)*d=j.val*d:=by rw [←Nat.add_mul];congr 1;omega
    have shift:=back M (i.val*d) ((j.val-i.val)*d) (by rw [dt];exact one.symm) (by rw [dt];exact two.symm)
    have dv:=((pi_spec (WallValuation.big hp ha) ((cop pr hp).pow_right a)).2 _).mp shift
    rw [fib_period_tower pr hp ha] at dv
    have div:T∣j.val-i.val:=Nat.dvd_of_mul_dvd_mul_right (pi_spec (by omega) (cop pr hp)).1 dv
    by_contra ne
    have:=Nat.le_of_dvd (by omega : 0<j.val-i.val) div
    omega
  letI : Finite (FibResidueBound.attained M):=(FibResidueBound.finite M (pow_pos pr.pos _)).to_subtype
  have inj:Function.Injective f:=by
    intro i j e
    apply Fin.ext
    rcases Nat.le_total i.val j.val with o|o
    · exact ordered _ _ o e
    · exact (ordered _ _ o e.symm).symm
  simpa only [Nat.card_eq_fintype_card (α:=Fin T),Fintype.card_fin] using Nat.card_le_card_of_injective f inj
end FibIdentityFiber
#print axioms FibIdentityFiber.lower
