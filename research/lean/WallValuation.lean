import WallTower
import Mathlib.Data.Nat.Factorization.Basic
import Batteries.Tactic.OpenPrivate
open private WallResidue.source_period WallResidue.index_spec from WallResidue
namespace WallValuation
open WallTransfer WallLift PisanoSource PowerLift

private theorem big {p a:ℕ} (hp:5<p) (ha:0<a) : 2<p^a := by
  have h : p≤p^a := by simpa using (Nat.pow_le_pow_right (by omega : 0<p) (show 1≤a by omega))
  omega

private theorem ratio {p:ℕ} (prime:p.Prime) (hp:5<p) (k:ℕ) :
    ∃j≤k, pi (big hp (by omega : 0<k+1)) ((cop prime hp).pow_right _)=
      p^j*pi (m:=p) (by omega) (cop prime hp) := by
  let d:=pi (m:=p) (by omega) (cop prime hp)
  let D:=pi (big hp (by omega : 0<k+1)) ((cop prime hp).pow_right _)
  have spec:=pi_spec (m:=p) (by omega) (cop prime hp)
  have tower:=pi_spec (big hp (by omega : 0<k+1)) ((cop prime hp).pow_right _)
  have upper (i:ℕ) : Fibonacci (p^(i+1)) (p^i*d) := by
    induction i with
    | zero => simpa using (spec.2 _).mpr (dvd_refl d)
    | succ i ih => rw [pow_succ' p i,Nat.mul_assoc];exact one_step prime (by omega) (by omega) ih
  have high : D∣p^k*d := (tower.2 _).mp (upper k)
  have has : Fibonacci (p^(k+1)) D := (tower.2 _).mpr dvd_rfl
  have low : d∣D := (spec.2 _).mp (descend (by rw [pow_succ'];exact dvd_mul_right p (p^k)) has)
  obtain ⟨l,eq⟩:=low
  rw [eq,Nat.mul_comm (p^k) d] at high
  obtain ⟨j,le,hj⟩ := (Nat.dvd_prime_pow prime).mp (Nat.dvd_of_mul_dvd_mul_left spec.1 high)
  exact ⟨j,le,by change D=_;rw [eq,hj,Nat.mul_comm d]⟩

private theorem stationary {p a:ℕ} (prime:p.Prime) (hp:5<p) (ha:0<a) :
    Fibonacci (p^a) (pi (m:=p) (by omega) (cop prime hp)) ↔ p^a∣Nat.fib (WallResidue.index p) := by
  have c:=(cop prime hp).pow_right a
  have key:=WallResidue.index_spec prime hp
  have test : period (big hp ha)∣6*WallResidue.index p ↔ p^a∣Nat.fib (WallResidue.index p) := by
    rw [←WallResidue.source_period (big hp ha) c]
    change (∃N,PhaseSix.Tail (p^a) N (6*WallResidue.index p)) ↔ _
    rw [PeriodDivisor.six_divisor,PeriodDivisor.periodDivisor,if_pos key.1,Apparition.standard]
    exact ⟨c.symm.dvd_of_dvd_mul_left,fun h=>dvd_mul_of_dvd_right h _⟩
  obtain ⟨k,hk⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  obtain ⟨j,_,eq⟩:=ratio prime hp k
  subst a
  rw [←test,(pi_spec (big hp ha) c).2,periods (big hp ha) c,eq]
  have hi:=key.2.2
  rw [periods (by omega : 2<p) (cop prime hp)] at hi
  let d:=pi (m:=p) (by omega) (cop prime hp)
  change p^j*d∣d ↔ 3*(p^j*d)∣6*WallResidue.index p
  rcases j with _|j
  · simpa using hi
  · have bigd : 1<p^(j+1) := Nat.one_lt_pow (by omega) (by omega)
    have dh : 0<d := (pi_spec (m:=p) (by omega) (cop prime hp)).1
    have small : ¬p^(j+1)*d∣d := by
      intro h
      have := Nat.le_of_dvd dh h
      nlinarith
    have nd : ¬3*(p^(j+1)*d)∣6*WallResidue.index p := by
      intro h
      apply key.2.1
      refine dvd_trans ?_ h
      rw [pow_succ']
      exact ⟨3*(p^j*d),by ring⟩
    simp [small,nd]

private theorem above {p w:ℕ} (prime:p.Prime) (hp:5<p) (hw:0<w)
    (base:Fibonacci (p^w) (pi (m:=p) (by omega) (cop prime hp)))
    (bad:¬Fibonacci (p^(w+1)) (pi (m:=p) (by omega) (cop prime hp))) (k:ℕ) :
    pi (big hp (by omega : 0<w+k)) ((cop prime hp).pow_right _)=p^k*pi (m:=p) (by omega) (cop prime hp) := by
  let d:=pi (m:=p) (by omega) (cop prime hp)
  have stair (i:ℕ) : Fibonacci (p^(w+i)) (p^i*d) ∧ ¬Fibonacci (p^(w+i+1)) (p^i*d) := by
    induction i with
    | zero => simpa using And.intro base bad
    | succ i ih =>
      have now:=one_step prime (by omega) (by omega : 0<w+i) ih.1
      have next:=faithful prime (by omega) (by omega : 0<w+i) ih.1
      rw [pow_succ' p i,Nat.mul_assoc]
      exact ⟨now,fun h=>ih.2 (next.mp h)⟩
  let D:=pi (big hp (by omega : 0<w+k)) ((cop prime hp).pow_right _)
  have tower:=pi_spec (big hp (by omega : 0<w+k)) ((cop prime hp).pow_right _)
  have spec:=pi_spec (m:=p) (by omega) (cop prime hp)
  have high : D∣p^k*d := (tower.2 _).mp (stair k).1
  have has : Fibonacci (p^(w+k)) D := (tower.2 _).mpr dvd_rfl
  have low : d∣D := (spec.2 _).mp (descend (by simpa using pow_dvd_pow p (show 1≤w+k by omega)) has)
  obtain ⟨l,eq⟩:=low
  rw [eq,Nat.mul_comm (p^k) d] at high
  obtain ⟨j,le,hj⟩:=(Nat.dvd_prime_pow prime).mp (Nat.dvd_of_mul_dvd_mul_left spec.1 high)
  have jk : j=k := by
    by_contra ne
    have lowpow : p^(w+j+1)∣p^(w+k) := pow_dvd_pow _ (by omega)
    rw [eq,hj,Nat.mul_comm] at has
    exact (stair j).2 (descend lowpow has)
  change D=_
  rw [eq,hj,jk,Nat.mul_comm]

def wallExponent (p:ℕ) : ℕ := (Nat.fib (WallResidue.index p)).factorization p

theorem all_powers {p a:ℕ} (prime:p.Prime) (hp:5<p) (ha:0<a) :
    period (big hp ha)=p^(a-wallExponent p)*period (m:=p) (by omega) := by
  let w:=wallExponent p
  have ns : Nat.fib (WallResidue.index p)≠0 := by
    apply Nat.ne_of_gt;apply Nat.fib_pos.mpr;unfold WallResidue.index;split <;> omega
  have val (i:ℕ) : p^i∣Nat.fib (WallResidue.index p) ↔ i≤w := prime.pow_dvd_iff_le_factorization ns
  have fx:=pi_spec (m:=p) (by omega) (cop prime hp)
  have hw : 0<w := (val 1).mp ((stationary (a:=1) prime hp (by decide)).mp (by simpa using (fx.2 _).mpr dvd_rfl))
  have src (i:ℕ) (hi:0<i) : Fibonacci (p^i) (pi (m:=p) (by omega) (cop prime hp)) ↔ i≤w :=
    (stationary prime hp hi).trans (val i)
  rw [periods (big hp ha) ((cop prime hp).pow_right a),periods (by omega : 2<p) (cop prime hp)]
  by_cases low:a≤w
  · rw [show a-wallExponent p=0 by change a-w=0;omega,pow_zero,one_mul]
    congr 1
    have v:=pi_spec (big hp ha) ((cop prime hp).pow_right a)
    have high := (v.2 _).mp ((src a ha).mpr low)
    have lower := (fx.2 _).mp (descend (by simpa using pow_dvd_pow p (show 1≤a by omega)) ((v.2 _).mpr dvd_rfl))
    exact Nat.dvd_antisymm high lower
  · obtain ⟨k,hk⟩:=Nat.exists_eq_add_of_le (show w≤a by omega)
    subst a
    have h:=above prime hp hw ((src w hw).mpr le_rfl) (fun h => (show ¬w+1≤w by omega) ((src _ (by omega)).mp h)) k
    rw [show w+k-wallExponent p=k by change w+k-w=k;omega,h]
    ring

end WallValuation
#print axioms WallValuation.all_powers
