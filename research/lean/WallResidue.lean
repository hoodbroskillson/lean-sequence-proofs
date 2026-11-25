import WallLift
import ResidueBounds
import Apparition
namespace WallResidue
open WallTransfer

/-- Index of the Fibonacci number in the standard Wall–Sun–Sun congruence for p>5. -/
def index (p:ℕ) : ℕ := if p%5=1 ∨ p%5=4 then p-1 else p+1

private theorem source_period {m : ℕ} (hm:2<m) (hc:Nat.Coprime 5 m) (t:ℕ) :
    (∃N, FinitePeriod.Tail m N t) ↔ period hm∣t := by
  rw [periods hm hc,pi_eq]
  constructor
  · rintro ⟨N,h⟩
    rcases (LucasParity.source hm N t).mp h with rfl|⟨_,d⟩
    · exact dvd_zero _
    · exact d
  · intro d;exact ⟨5,(LucasParity.source hm 5 t).mpr (Or.inr ⟨le_rfl,d⟩)⟩

private theorem index_spec {p:ℕ} (prime:p.Prime) (hp:5<p) :
    index p%2=0 ∧ ¬p∣6*index p ∧ period (m:=p) (by omega)∣6*index p := by
  letI : Fact p.Prime := ⟨prime⟩
  have rem : p%2=1 := Nat.Prime.mod_two_eq_one_iff_ne_two.mpr (by omega)
  have not5 : p%5≠0 := by
    intro h
    have d : 5∣p := Nat.dvd_of_mod_eq_zero h
    have := (Nat.dvd_prime prime).mp d
    omega
  have no6 : ¬p∣6 := by
    intro h
    have := Nat.le_of_dvd (by decide) h
    omega
  have bounds:=ResidueBounds.residues (by omega : 2<p)
  by_cases branch:p%5=1 ∨ p%5=4
  · rw [index,if_pos branch]
    have nd : ¬p∣p-1 := by intro h; have := Nat.le_of_dvd (by omega : 0<p-1) h;omega
    refine ⟨by omega,fun d => ((prime.dvd_mul.mp d).elim no6 nd),?_⟩
    have d := (source_period (by omega) (cop prime hp) _).mp ⟨5,bounds.1 branch⟩
    exact dvd_trans d ⟨2,by ring⟩
  · rw [index,if_neg branch]
    have nd : ¬p∣p+1 := by
      intro h
      have done : p∣1 := (Nat.dvd_add_iff_right dvd_rfl).mpr h
      have := Nat.le_of_dvd (by decide) done
      omega
    refine ⟨by omega,fun d => ((prime.dvd_mul.mp d).elim no6 nd),?_⟩
    have res : p%5=2 ∨ p%5=3 := by omega
    exact (source_period (by omega) (cop prime hp) _).mp ⟨5,(bounds.2 res).1⟩

theorem criterion {p:ℕ} (prime:p.Prime) (hp:5<p) :
    period (m:=p^2) (by nlinarith)=period (m:=p) (by omega) ↔ p^2∣Nat.fib (index p) := by
  let d:=period (m:=p) (by omega)
  let D:=period (m:=p^2) (by nlinarith)
  have c2:=(cop prime hp).pow_right 2
  have key:=index_spec prime hp
  have test : D∣6*index p ↔ p^2∣Nat.fib (index p) := by
    rw [←source_period (by nlinarith : 2<p^2) c2]
    change (∃N,PhaseSix.Tail (p^2) N (6*index p)) ↔ _
    rw [PeriodDivisor.six_divisor,PeriodDivisor.periodDivisor,if_pos key.1,Apparition.standard]
    exact ⟨c2.symm.dvd_of_dvd_mul_left,fun h => dvd_mul_of_dvd_right h _⟩
  change D=d ↔ _
  rw [←test]
  constructor
  · intro eq;rw [eq];exact key.2.2
  · intro check
    rcases WallLift.alternatives prime hp with eq|eq
    · exact eq
    · change D=p*d at eq
      rw [eq] at check
      exact False.elim <| key.2.1 (dvd_trans (dvd_mul_right p d) check)

theorem fibonacci_criterion {p:ℕ} (prime:p.Prime) (hp:5<p) :
    pi (m:=p^2) (by nlinarith) ((cop prime hp).pow_right 2)=pi (m:=p) (by omega) (cop prime hp) ↔
    p^2∣Nat.fib (index p) :=
  (wall_iff prime hp).symm.trans (criterion prime hp)

end WallResidue
#print axioms WallResidue.criterion
#print axioms WallResidue.fibonacci_criterion
