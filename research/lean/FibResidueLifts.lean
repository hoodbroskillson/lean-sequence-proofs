import Mathlib.Data.Nat.Fib.Basic
import Mathlib.SetTheory.Cardinal.Finite

namespace FibResidueBound

/-- The residues attained by ordinary Fibonacci numbers F₀=0,F₁=1. -/
def attained (m : ℕ) : Set ℕ := Set.range (fun j : ℕ=> Nat.fib j % m)

theorem below {m : ℕ} (hm : 0<m) (r : attained m) : r.val<m := by
  obtain ⟨j,h⟩:=r.property
  exact h ▸ Nat.mod_lt _ hm

theorem finite (m : ℕ) (hm : 0<m) : (attained m).Finite := by
  apply (Set.finite_lt_nat m).subset
  intro x hx
  exact below hm ⟨x,hx⟩

theorem lifts (a b : ℕ) (ha : 0<a) (hb : 0<b) :
    Nat.card (attained (a*b)) ≤ Nat.card (attained a)*b := by
  letI : Finite (attained a) := (finite a ha).to_subtype
  let f (x : attained (a*b)) : attained a × Fin b :=
    (⟨x.val%a,by
      obtain ⟨j,hj⟩:=x.property
      refine ⟨j,?_⟩
      change Nat.fib j%(a*b)=x.val at hj
      rw [←hj,Nat.mod_mod_of_dvd _ (dvd_mul_right a b)]⟩,
     ⟨x.val/a,(Nat.div_lt_iff_lt_mul ha).mpr (by
       rw [Nat.mul_comm b a]
       exact below (Nat.mul_pos ha hb) x)⟩)
  have inj : Function.Injective f := by
    intro x y eq
    have r:=congrArg (fun z : attained a × Fin b => z.1.val) eq
    have q:=congrArg (fun z : attained a × Fin b => z.2.val) eq
    change x.val%a=y.val%a at r
    change x.val/a=y.val/a at q
    apply Subtype.ext
    calc x.val=x.val%a+a*(x.val/a) := (Nat.mod_add_div _ _).symm
         _=y.val := by rw [r,q,Nat.mod_add_div]
  simpa only [Nat.card_prod,Nat.card_eq_fintype_card (α:=Fin b),Fintype.card_fin] using
    Nat.card_le_card_of_injective f inj

/-- A period of length T leaves at most T distinct Fibonacci residues. -/
theorem of_period {m T : ℕ} (ht : 0<T)
    (h : ∀j, Nat.fib (j+T)%m=Nat.fib j%m) : Nat.card (attained m)≤T := by
  let f (j : Fin T) : attained m := ⟨Nat.fib j.val % m,⟨j.val,rfl⟩⟩
  have reduce (j : ℕ) : ∃ z : Fin T, Nat.fib j%m=Nat.fib z.val%m := by
    induction j using Nat.strong_induction_on with
    | h j ih =>
      by_cases small : j<T
      · exact ⟨⟨_,small⟩,rfl⟩
      obtain ⟨z,hz⟩:=ih (j-T) (by omega)
      refine ⟨z,?_⟩
      have e:=h (j-T)
      rw [show j-T+T=j by omega] at e
      exact e.trans hz
  have onto : Function.Surjective f := by
    intro v
    obtain ⟨j,hj⟩:=v.property
    obtain ⟨z,hz⟩:=reduce j
    exact ⟨z,Subtype.ext (hz.symm.trans hj)⟩
  simpa only [Nat.card_eq_fintype_card (α:=Fin T),Fintype.card_fin] using
    Nat.card_le_card_of_surjective f onto
end FibResidueBound
#print axioms FibResidueBound.lifts
#print axioms FibResidueBound.of_period
