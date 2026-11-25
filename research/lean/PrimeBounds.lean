import RootOrders
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.Tactic.ComputeDegree
namespace PrimeBounds
open Polynomial

theorem root_cases {p : ℕ} [hp' : Fact p.Prime] (hp : 2<p)
    {K : Type*} [Field K] [CharP K p] (f : ZMod p →+* K) (r:K) (hr:r^2=r+1) :
    (r^p=r → FinitePeriod.Tail p 5 (3*(p-1))) ∧
    (r^p≠r → FinitePeriod.Tail p 5 (6*(p+1))) := by
  have nz : r≠0 := by rintro rfl;simp at hr
  have even : 2∣p-1 := even_iff_two_dvd.mp (hp'.out.even_sub_one (by omega))
  constructor
  · intro h
    have rr : r^(p-1)=1 := by
      have e : r^(p-1)*r=1*r := by simpa only [←pow_succ,show p-1+1=p by omega,one_mul] using h
      exact mul_right_cancel₀ nz e
    apply (RootOrders.source hp f r hr 5 _).mpr <| Or.inr ⟨le_rfl,?_⟩
    exact Nat.mul_dvd_mul_left _ (Nat.lcm_dvd even (orderOf_dvd_iff_pow_eq_one.mpr rr))
  · intro h
    have fp : (r^p)^2=r^p+1 := by
      rw [pow_right_comm,hr,add_pow_char,one_pow]
    have z : (r^p-r)*(r^p-(1-r))=0 := by linear_combination fp-hr
    have diff : r^p=1-r := sub_eq_zero.mp ((mul_eq_zero.mp z).resolve_left (sub_ne_zero.mpr h))
    have eq : r^(p+1)= -1 := by rw [pow_succ,diff];linear_combination -hr
    have pow : r^(2*(p+1))=1 := by rw [Nat.mul_comm,pow_mul,eq];norm_num
    apply (RootOrders.source hp f r hr 5 _).mpr <| Or.inr ⟨le_rfl,?_⟩
    simpa only [←Nat.mul_assoc] using Nat.mul_dvd_mul_left 3
      (Nat.lcm_dvd (dvd_mul_right 2 (p+1)) (orderOf_dvd_iff_pow_eq_one.mpr pow))

theorem split {p:ℕ} [Fact p.Prime] (hp:2<p) (r:ZMod p) (hr:r^2=r+1) :
    FinitePeriod.Tail p 5 (3*(p-1)) :=
  (root_cases hp (RingHom.id _) r hr).1 (ZMod.pow_card _)

private theorem fixed {p : ℕ} [Fact p.Prime] (hp:2<p) {K:Type*} [Field K]
    (f : ZMod p →+* K) (r:K) (h:r^p=r) : ∃a:ZMod p,f a=r := by
  classical
  let g : Polynomial (ZMod p):=X^p-X
  have all : g.roots=Finset.univ.val := by
    simpa only [g,ZMod.card] using FiniteField.roots_X_pow_card_sub_X (ZMod p)
  have card : Multiset.card g.roots=g.natDegree := by
    rw [all];change Fintype.card (ZMod p)=(X^p-X:Polynomial (ZMod p)).natDegree
    rw [ZMod.card,FiniteField.X_pow_card_sub_X_natDegree_eq _ (by omega)]
  have mem : r∈(g.map f).roots := by
    rw [mem_roots ((Polynomial.map_ne_zero_iff f.injective).mpr (FiniteField.X_pow_card_sub_X_ne_zero _ (by omega : 1<p)))]
    simp [g,IsRoot.def,h]
  rw [←roots_map_of_injective_of_card_eq_natDegree f.injective card, Multiset.mem_map] at mem
  obtain ⟨a,_,ha⟩:=mem
  exact ⟨a,ha⟩

theorem nonsplit {p:ℕ} [Fact p.Prime] (hp:2<p) (no : ¬∃a:ZMod p,a^2=a+1) :
    FinitePeriod.Tail p 5 (6*(p+1)) := by
  classical
  let g : Polynomial (ZMod p) := X^2-X-1
  have deg : g.degree ≠ 0 := by
    have eq : g.degree=2 := by dsimp [g];compute_degree <;> first | exact one_ne_zero | decide
    rw [eq];decide
  let K:=g.SplittingField
  let f:=algebraMap (ZMod p) K
  obtain ⟨r,hr⟩:=exists_root_of_splits f (SplittingField.splits g) deg
  have root : r^2=r+1 := by
    change eval₂ f r (X^2-X-1)=0 at hr
    simp only [eval₂_sub,eval₂_pow,eval₂_X,eval₂_one] at hr
    linear_combination hr
  have both:=root_cases hp f r root
  apply both.2
  intro same
  obtain ⟨a,ha⟩:=fixed hp f r same
  exact no ⟨a,f.injective (by rw [map_pow,map_add,map_one,ha,root])⟩

theorem either_period {p:ℕ} [Fact p.Prime] (hp:2<p) :
    FinitePeriod.Tail p 5 (3*(p-1)) ∨ FinitePeriod.Tail p 5 (6*(p+1)) := by
  by_cases h : ∃r:ZMod p, r^2=r+1
  · obtain ⟨r,hr⟩:=h
    exact Or.inl (split hp r hr)
  · exact Or.inr (nonsplit hp h)
end PrimeBounds
#print axioms PrimeBounds.split
#print axioms PrimeBounds.either_period
#print axioms PrimeBounds.nonsplit
