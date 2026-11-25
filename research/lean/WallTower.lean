import PowerLift
import WallResidue
namespace WallTower
open WallTransfer WallLift PisanoSource PowerLift
private theorem gt {p:ℕ} (hp:5<p) (k:ℕ) : 2<p^(k+1) := by
  have h : 1≤p^k := Nat.one_le_pow _ _ (by omega)
  rw [pow_succ]
  nlinarith

noncomputable def pis (p k:ℕ) (prime:p.Prime) (hp:5<p) :=
  pi (m:=p^(k+1)) (gt hp k) ((cop prime hp).pow_right _)

theorem lifting {p:ℕ} (prime:p.Prime) (hp:5<p) (no:¬p^2∣Nat.fib (WallResidue.index p)) (k:ℕ) :
    period (m:=p^(k+1)) (gt hp k)=p^k*period (m:=p) (by omega) := by
  let d:=pi (m:=p) (by omega) (cop prime hp)
  have spec := pi_spec (m:=p) (by omega) (cop prime hp)
  have base : Fibonacci p d := (spec.2 _).mpr dvd_rfl
  have bad : ¬ Fibonacci (p^2) d := by
    intro h
    have v:=pi_spec (m:=p^2) (by nlinarith) ((cop prime hp).pow_right 2)
    have div:= (v.2 _).mp h
    have reverse := (spec.2 _).mp (descend (show p∣p^2 by rw [sq];exact dvd_mul_right p p)
      ((v.2 _).mpr dvd_rfl))
    exact no ((WallResidue.fibonacci_criterion prime hp).mp (Nat.dvd_antisymm div reverse))
  have stair (i:ℕ) : Fibonacci (p^(i+1)) (p^i*d) ∧ ¬Fibonacci (p^(i+2)) (p^i*d) := by
    induction i with
    | zero => simpa using And.intro base bad
    | succ i ih =>
      have now:=one_step prime (by omega) (by omega : 0<i+1) ih.1
      have next:=faithful prime (by omega) (by omega : 0<i+1) ih.1
      rw [pow_succ' p i,Nat.mul_assoc]
      exact ⟨now, fun h=>ih.2 (next.mp h)⟩
  let D:=pis p k prime hp
  have tower:=pi_spec (gt hp k) ((cop prime hp).pow_right _)
  have high : D∣p^k*d := (tower.2 _).mp (stair k).1
  have has : Fibonacci (p^(k+1)) D := (tower.2 _).mpr dvd_rfl
  have low : d∣D := (spec.2 _).mp (descend (by rw [pow_succ'];exact dvd_mul_right p (p^k)) has)
  obtain ⟨l,eq⟩:=low
  rw [eq,Nat.mul_comm (p^k) d] at high
  obtain ⟨j,le,hj⟩ := (Nat.dvd_prime_pow prime).mp (Nat.dvd_of_mul_dvd_mul_left spec.1 high)
  have jk : j=k := by
    by_contra ne
    have lowpow : p^(j+2)∣p^(k+1) := pow_dvd_pow _ (by omega)
    rw [eq,hj,Nat.mul_comm] at has
    exact (stair j).2 (descend lowpow has)
  rw [periods (gt hp k) ((cop prime hp).pow_right _),periods (by omega : 2<p) (cop prime hp)]
  change 3*D=p^k*(3*d)
  rw [eq,hj,jk];ring

end WallTower
#print axioms WallTower.lifting
