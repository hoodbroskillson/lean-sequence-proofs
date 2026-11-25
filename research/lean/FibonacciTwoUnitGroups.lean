import FibonacciUnitGroups
import TwoPowers
import FibCoverObstruction
import Batteries.Tactic.OpenPrivate
open private WallLift.U from WallLift
open private FibRegularLifts.second from FibRegularLifts
open private FibonacciLargeFactor.F_standard from FibonacciLargeFactor
open private FibIdentityFiber.back from FibIdentityFiber
open private FibCoverObstruction.bridge FibCoverObstruction.reduce from FibCoverObstruction
namespace FibonacciTwoUnitGroups
open FibonacciUnitGroups WallTransfer PisanoSource FibRegularLifts

private theorem period_divisor (a n:ℕ) (h:Fibonacci (2^(a+3)) (n*6)) : 2^(a+1)∣n := by
  let M:=2^(a+3)
  have big:2<M:=by dsimp [M];rw [pow_add];have e:=Nat.one_le_two_pow (n:=a);omega
  have cop:Nat.Coprime 5 M:=Nat.Coprime.pow_right _ (by decide : Nat.Coprime 5 2)
  have funperiod:=((PisanoSource.pisano (by omega : 1<M) cop).2 _).mp h
  have src:PhaseSix.Tail M 5 (3*(n*6)):=(LucasParity.source big 5 _).mpr
    (Or.inr ⟨le_rfl,Nat.mul_dvd_mul_left 3 funperiod⟩)
  have dv:36*2^a∣3*(n*6):=(TwoPowers.periods a _).mp ⟨5,src⟩
  have dv':2^(a+1)*18∣n*18:=by
    rw [pow_succ,show 2^a*2*18=36*2^a by ring,show n*18=3*(n*6) by ring]
    exact dv
  exact Nat.dvd_of_mul_dvd_mul_right (by decide : 0<18) dv'

private theorem lift {s a r:ℕ} (reg:regular 2 s) (small:r<2^(a+3)) (same:r%4=Nat.fib s%4) :
    r∈FibResidueBound.attained (2^(a+3)) := by
  have pd:Fibonacci 4 6:=(PowerLift.state 4 6).mpr (by decide)
  let M:=2^(a+3)
  let T:=2^(a+1)
  have modeq (i:ℕ):Fibonacci 4 (i*6):=by
    intro n _
    induction i with
    | zero => simp
    | succ i ih =>
      rw [Nat.succ_mul,←Nat.add_assoc]
      exact (pd _ (Nat.zero_le _)).trans ih
  let f (i:Fin T):ℕ:=Nat.fib (s+i.val*6)%M
  have bound (i:Fin T):f i<M:=Nat.mod_lt _ (by dsimp [M];positivity)
  have same_seed (i:Fin T):f i%4=Nat.fib s%4:=by
    have eq:= modeq i.val s (Nat.zero_le _)
    change (F (s+i.val*6):ZMod 4)=F s at eq
    rw [FibonacciLargeFactor.F_standard,FibonacciLargeFactor.F_standard] at eq
    dsimp [f,M]
    rw [Nat.mod_mod_of_dvd _ (by change 2^2∣2^(a+3);apply pow_dvd_pow;omega)]
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp eq
  have ordered (i j:Fin T) (ord:i.val≤j.val) (h:f i=f j) : i.val=j.val := by
    have one:WallLift.U M (s+i.val*6)=WallLift.U M (s+j.val*6):=by
      unfold WallLift.U;rw [FibonacciLargeFactor.F_standard,FibonacciLargeFactor.F_standard]
      exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h
    have two:=FibRegularLifts.second Nat.prime_two (by omega : 0<a+3) reg
      (by omega : 2∣i.val*6) (by omega : 2∣j.val*6)
      (WallLift.descend (by decide : 2∣4) (modeq _)) (WallLift.descend (by decide : 2∣4) (modeq _)) one
    have dt:s+i.val*6+(j.val-i.val)*6=s+j.val*6:=by rw [Nat.add_assoc,←Nat.add_mul];congr 2;omega
    have shift:=FibIdentityFiber.back M (s+i.val*6) ((j.val-i.val)*6)
      (by rw [dt];exact one.symm) (by rw [dt];exact two.symm)
    have div:T∣j.val-i.val:=period_divisor a _ shift
    by_contra ne
    have:=Nat.le_of_dvd (by omega : 0<j.val-i.val) div
    omega
  have quot {v:ℕ} (hv:v<M):v/4<T:=by
    apply (Nat.div_lt_iff_lt_mul (by decide : 0<4)).mpr
    change v<2^(a+1)*4
    rw [show 2^(a+1)*4=2^(a+3) by rw [show a+3=(a+1)+2 by omega,pow_add 2 (a+1) 2];rfl]
    exact hv
  let g (i:Fin T):Fin T:=⟨f i/4,quot (bound i)⟩
  have inj:Function.Injective g:=by
    intro i j e
    have u:=congrArg Fin.val e
    change f i/4=f j/4 at u
    have v:f i=f j:=by
      calc f i = f i%4+4*(f i/4) := (Nat.mod_add_div _ _).symm
           _ = f j := by rw [same_seed i,←same_seed j,u,Nat.mod_add_div]
    apply Fin.ext
    rcases Nat.le_total i.val j.val with o|o
    · exact ordered _ _ o v
    · exact (ordered _ _ o v.symm).symm
  obtain ⟨i,hg⟩:=(Finite.surjective_of_injective inj) (⟨r/4,quot small⟩:Fin T)
  have u:=congrArg Fin.val hg
  change f i/4=r/4 at u
  refine ⟨s+i.val*6,?_⟩
  calc f i = f i%4+4*(f i/4):=(Nat.mod_add_div _ _).symm
       _=r:=by rw [same_seed i,←same,u,Nat.mod_add_div]


theorem all_odd {a r:ℕ} (small:r<2^(a+3)) (odd:r%2=1) : r∈FibResidueBound.attained (2^(a+3)) := by
  rcases (show r%4=1 ∨ r%4=3 by omega) with l|u
  · exact lift (s:=1) (by unfold regular;decide) small l
  · exact lift (s:=4) (by unfold regular;decide) small u

theorem four_missing (a:ℕ) : 4∉FibResidueBound.attained (2^(a+3)) := by
  rintro ⟨n,eq⟩
  have per:= (FibCoverObstruction.bridge 8 12).mpr ((PowerLift.state _ _).mpr (by decide))
  have red:= FibCoverObstruction.reduce per n
  have q:Nat.fib n%8=4:=by
    have h:=congrArg (fun x:ℕ=>x%8) eq
    change Nat.fib n%(2^(a+3))%8=4%8 at h
    rwa [Nat.mod_mod_of_dvd _ (show 8∣2^(a+3) from pow_dvd_pow 2 (by omega : 3≤a+3))] at h
  have excluded:∀j:Fin 12, Nat.fib j.val%8≠4:=by decide
  exact excluded ⟨n%12,Nat.mod_lt _ (by decide)⟩ (red.symm.trans q)

theorem units (a:ℕ) : classes (2^(a+3))=(⊤:Subgroup (ZMod (2^(a+3)))ˣ).carrier := by
  let M:=2^(a+3)
  letI : NeZero M:=⟨by dsimp [M];positivity⟩
  change classes M=(⊤:Subgroup (ZMod M)ˣ).carrier
  ext x
  constructor
  · intro _;trivial
  · intro _
    have unit:IsUnit ((x.val.val:ℕ):ZMod M):=by rw [ZMod.natCast_zmod_val];exact x.isUnit
    have cp:= (ZMod.isUnit_iff_coprime _ _).mp unit
    have dp:2∣M:=by dsimp [M];simpa using pow_dvd_pow 2 (show 1≤a+3 by omega)
    have odd:x.val.val%2=1:=by
      by_contra bad
      have ev:2∣x.val.val:=Nat.dvd_of_mod_eq_zero (by omega)
      have h:=Nat.dvd_gcd ev dp;rw [cp.gcd_eq_one] at h;omega
    obtain ⟨n,e⟩:=all_odd (a:=a) (ZMod.val_lt x.val) odd
    exact ⟨n,ZMod.val_injective _ (by rw [ZMod.val_natCast];exact e)⟩

theorem infinite_incomplete : Set.Infinite {m:ℕ | 4∉FibResidueBound.attained m ∧
    classes m=(⊤:Subgroup (ZMod m)ˣ).carrier} := by
  apply Set.Infinite.mono (s:=Set.range (fun a:ℕ=>2^(a+3)))
  · rintro _ ⟨a,rfl⟩;exact ⟨four_missing a,units a⟩
  · apply Set.infinite_range_of_injective
    intro a b eq
    have e:=Nat.pow_right_injective (by decide : 1<2) eq
    omega
end FibonacciTwoUnitGroups
#print axioms FibonacciTwoUnitGroups.all_odd
#print axioms FibonacciTwoUnitGroups.four_missing
#print axioms FibonacciTwoUnitGroups.units
#print axioms FibonacciTwoUnitGroups.infinite_incomplete
