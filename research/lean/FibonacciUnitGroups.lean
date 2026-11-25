import FibRegularLifts
import ThreePowersSource
import FivePowers
import Batteries.Tactic.OpenPrivate
open private WallLift.U from WallLift
open private FibRegularLifts.second from FibRegularLifts
open private FibonacciLargeFactor.F_standard from FibonacciLargeFactor
open private FibIdentityFiber.back from FibIdentityFiber
open private ThreePowersSource.large from ThreePowersSource
namespace FibonacciUnitGroups
open WallTransfer PisanoSource FibRegularLifts

private theorem field_fiber {p s d:ℕ} (pr:p.Prime) (ed:2∣d) (pd:Fibonacci p d)
    (reg:regular p s) (a r:ℕ) (small:r<p^(a+1)) (same:r%p=Nat.fib s%p)
    (divisor:∀n,Fibonacci (p^(a+1)) (n*d) → p^a∣n) :
    r∈FibResidueBound.attained (p^(a+1)) := by
  let M:=p^(a+1)
  let T:=p^a
  have modeq (i:ℕ):Fibonacci p (i*d):=by
    intro n _
    induction i with
    | zero => simp
    | succ i ih =>
      rw [Nat.succ_mul,←Nat.add_assoc]
      exact (pd _ (Nat.zero_le _)).trans ih
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
    have two:=FibRegularLifts.second pr (by omega : 0<a+1) reg (dvd_trans ed (dvd_mul_left d i.val))
      (dvd_trans ed (dvd_mul_left d j.val)) (modeq _) (modeq _) one
    have dt:s+i.val*d+(j.val-i.val)*d=s+j.val*d:=by rw [Nat.add_assoc,←Nat.add_mul];congr 2;omega
    have shift:=FibIdentityFiber.back M (s+i.val*d) ((j.val-i.val)*d)
      (by rw [dt];exact one.symm) (by rw [dt];exact two.symm)
    have div:T∣j.val-i.val:=divisor _ shift
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

/-- Every residue modulo 5^(a+1) occurs in the Fibonacci sequence. -/
theorem complete_five (a r:ℕ) (small:r<5^(a+1)) :
    r∈FibResidueBound.attained (5^(a+1)) := by
  have seeds:∀v:Fin 5,∃j:Fin 20,Nat.fib j.val%5=v.val ∧ regular 5 j.val :=by
    unfold regular;decide
  obtain ⟨s,sv,reg⟩:=seeds ⟨r%5,Nat.mod_lt _ (by decide)⟩
  refine field_fiber (d:=20) (by decide) (by decide) ((PowerLift.state _ _).mpr (by decide)) reg a r small sv.symm ?_
  intro n h
  have z:5^(a+1)∣Nat.fib (n*20):=by
    have zero:=(PowerLift.state _ _).mp h |>.1
    rw [WallLift.U,FibonacciLargeFactor.F_standard] at zero
    exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp zero
  have fact:5^a*5∣(n*4)*5:=by
    rw [←pow_succ,show n*4*5=n*20 by ring]
    exact (FivePowers.div_iff _ _).mp z
  have div:=Nat.dvd_of_mul_dvd_mul_right (by decide : 0<5) fact
  exact ((by decide : Nat.Coprime 5 4).pow_left a).dvd_of_dvd_mul_right div

/-- Every residue modulo 3^(a+1) occurs in the Fibonacci sequence. -/
theorem complete_three (a r:ℕ) (small:r<3^(a+1)) :
    r∈FibResidueBound.attained (3^(a+1)) := by
  have seeds:∀v:Fin 3,∃j:Fin 8,Nat.fib j.val%3=v.val ∧ regular 3 j.val :=by
    unfold regular;decide
  obtain ⟨s,sv,reg⟩:=seeds ⟨r%3,Nat.mod_lt _ (by decide)⟩
  refine field_fiber (d:=8) (by decide) (by decide) ((PowerLift.state _ _).mpr (by decide)) reg a r small sv.symm ?_
  intro n h
  let c:=Nat.Coprime.pow_right (a+1) (by decide : Nat.Coprime 5 3)
  have fact:= ((pi_spec (ThreePowersSource.large a) c).2 _).mp h
  have result:=ThreePowersSource.powers a
  rw [periods (ThreePowersSource.large a) c] at result
  have eq:pi (ThreePowersSource.large a) c=3^a*8:=by omega
  rw [eq] at fact
  exact Nat.dvd_of_mul_dvd_mul_right (by decide : 0<8) fact

/-- Invertible Fibonacci classes, as a subset of the unit group. -/
def classes (m:ℕ) : Set (ZMod m)ˣ := {u | ∃n:ℕ, (Nat.fib n:ZMod m)=u.val}

private theorem units_all {m:ℕ} (hm:0<m) (h:∀r<m,r∈FibResidueBound.attained m) :
    classes m = (⊤:Subgroup (ZMod m)ˣ).carrier := by
  letI : NeZero m:=⟨by omega⟩
  ext x
  constructor
  · intro _;trivial
  · intro _
    obtain ⟨n,e⟩:=h x.val.val (ZMod.val_lt _)
    exact ⟨n,ZMod.val_injective _ (by rw [ZMod.val_natCast];exact e)⟩

/-- Two infinite explicit families realizing the whole unit group. -/
theorem groups (a:ℕ) : classes (3^(a+1))=(⊤:Subgroup (ZMod (3^(a+1)))ˣ).carrier ∧
    classes (5^(a+1))=(⊤:Subgroup (ZMod (5^(a+1)))ˣ).carrier :=
  ⟨units_all (by positivity) (complete_three a),units_all (by positivity) (complete_five a)⟩

/-- Direct negation of the printed finiteness conjecture. -/
theorem infinite : Set.Infinite {m:ℕ | ∃H:Subgroup (ZMod m)ˣ, classes m=H.carrier} := by
  apply Set.Infinite.mono (s:=Set.range (fun a:ℕ=>5^(a+1)))
  · rintro _ ⟨a,rfl⟩
    exact ⟨⊤,(groups a).2⟩
  · apply Set.infinite_range_of_injective
    intro a b eq
    have e:=Nat.pow_right_injective (by decide : 1<5) eq
    omega
end FibonacciUnitGroups
#print axioms FibonacciUnitGroups.complete_five
#print axioms FibonacciUnitGroups.complete_three
#print axioms FibonacciUnitGroups.groups
#print axioms FibonacciUnitGroups.infinite
