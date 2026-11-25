import WallValuation
import Mathlib.NumberTheory.PrimesCongruentOne
import Batteries.Tactic.OpenPrivate
open private WallValuation.stationary from WallValuation
open private WallLift.U WallLift.addF WallLift.recF from WallLift
namespace FibonacciLargeFactor
open WallTransfer

private theorem index_dvd {p q s:ℕ} (pr:q.Prime) (gt:1<p)
    (fq:p∣Nat.fib q) (fs:p∣Nat.fib s) : q∣s := by
  by_contra bad
  have g:Nat.gcd q s=1 := (pr.coprime_iff_not_dvd.mpr bad).gcd_eq_one
  have d:=Nat.dvd_gcd fq fs
  rw [←Nat.fib_gcd,g,Nat.fib_one] at d
  have:=Nat.le_of_dvd (by decide : 0<1) d
  omega

private theorem small_excluded {q p:ℕ} (pr:q.Prime) (gt:5<q) (pp:p.Prime)
    (fq:p∣Nat.fib q) : 5<p := by
  by_contra! le
  have g:=pp.two_le
  have index {s:ℕ} (hs:p∣Nat.fib s) : q∣s:=index_dvd pr (by omega : 1<p) fq hs
  interval_cases p
  · exact (by have := Nat.le_of_dvd (by decide : 0<3) (index (s:=3) (by decide));omega)
  · exact (by have := Nat.le_of_dvd (by decide : 0<4) (index (s:=4) (by decide));omega)
  · exact (by decide : ¬Nat.Prime 4) pp
  · exact (by have := Nat.le_of_dvd (by decide : 0<5) (index (s:=5) (by decide));omega)

private theorem divides_index {p q:ℕ} (pr:q.Prime) (pp:p.Prime) (gt:5<p)
    (fq:p∣Nat.fib q) : q∣WallResidue.index p := by
  have s:=pi_spec (m:=p) (by omega) (cop pp gt)
  have d:= (WallValuation.stationary (a:=1) pp gt (by decide)).mp (by simpa using (s.2 _).mpr dvd_rfl)
  exact index_dvd pr (by omega) fq (by simpa using d)

private theorem near_plus {q p k C:ℕ} (pp:p.Prime) (gq:5<q) (hk:0<k) (small:k≤C+1)
    (hcon:q ≡ 1 [MOD (C+8).factorial]) (eq:p=q*k+1) : False := by
  have cong:q ≡ 1 [MOD k+1] := hcon.of_dvd (Nat.dvd_factorial (by omega) (by omega))
  have ca:= (cong.mul_right k).add_right 1
  have dv:k+1∣p:=by
    apply Nat.modEq_zero_iff_dvd.mp
    rw [eq]
    exact (by simpa only [Nat.one_mul] using ca : q*k+1 ≡ k+1 [MOD k+1]).trans
      (Nat.modEq_zero_iff_dvd.mpr dvd_rfl)
  have cases:=(Nat.dvd_prime pp).mp dv
  have big:=Nat.mul_lt_mul_of_pos_right (show 1<q by omega) hk
  simp only [Nat.one_mul] at big
  omega

private theorem near_minus {q p k C:ℕ} (pp:p.Prime) (qp:q.Prime) (gp:5<p) (gq:5<q)
    (small:k≤C+1) (hcon:q ≡ 1 [MOD (C+8).factorial]) (eq:p+1=q*k)
    (inert:¬(p%5=1 ∨ p%5=4)) : False := by
  have hi:3≤k:=by
    by_contra! low
    interval_cases k
    · simp at eq
    · simp at eq
      letI : Fact p.Prime:=⟨pp⟩
      letI : Fact q.Prime:=⟨qp⟩
      have h1:=Nat.Prime.mod_two_eq_one_iff_ne_two.mpr (show p≠2 by omega)
      have h2:=Nat.Prime.mod_two_eq_one_iff_ne_two.mpr (show q≠2 by omega)
      omega
    · have five:q ≡ 1 [MOD 5] := hcon.of_dvd (Nat.dvd_factorial (by decide) (by omega))
      change q%5=1%5 at five
      omega
  have cong:q ≡ 1 [MOD k-1] := hcon.of_dvd (Nat.dvd_factorial (by omega) (by omega))
  have ca:=cong.mul_right k
  have dv:k-1∣p:=by
    apply Nat.modEq_zero_iff_dvd.mp
    have a:p+1 ≡ (k-1)+1 [MOD k-1]:=by
      rw [eq,show k-1+1=k by omega];simpa only [Nat.one_mul] using ca
    exact (Nat.ModEq.add_right_cancel' 1 a).trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl)
  have cases:=(Nat.dvd_prime pp).mp dv
  have big:=Nat.mul_lt_mul_of_pos_right (show 1<q by omega) (show 0<k by omega)
  simp only [Nat.one_mul] at big
  omega

/-- Primes dividing a Fibonacci number of prime index can exceed any fixed multiple
of the index, with the index arbitrarily large. -/
theorem unbounded (C B:ℕ) : ∃ q p:ℕ, q.Prime ∧ B<q ∧ p.Prime ∧ 5<p ∧
    p∣Nat.fib q ∧ C*q<p := by
  obtain ⟨q,qp,gq,hcon⟩:=Nat.exists_prime_gt_modEq_one (max B 5)
    (Nat.ne_of_gt (Nat.factorial_pos (C+8)))
  have gt:5<q:=(le_max_right _ _).trans_lt gq
  have fibbig:1<Nat.fib q:= (Nat.fib_lt_fib (m:=2) (by decide)).mpr (by omega)
  obtain ⟨p,pp,fq⟩:=Nat.exists_prime_and_dvd (show Nat.fib q≠1 by omega)
  have gp:=small_excluded qp gt pp fq
  refine ⟨q,p,qp,(le_max_left _ _).trans_lt gq,pp,gp,fq,?_⟩
  by_contra! bound
  have d:=divides_index qp pp gp fq
  unfold WallResidue.index at d
  split at d
  next =>
    obtain ⟨k,e⟩:=d
    have eq:p=q*k+1:=by omega
    have hk:0<k:=by by_contra! non;rw [show k=0 by omega] at eq;simp at eq;omega
    have small:k≤C+1:=by
      apply Nat.le_of_mul_le_mul_left (c:=q) _ (by omega)
      rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm q C];omega
    exact near_plus pp gt hk small hcon eq
  next inert =>
    obtain ⟨k,e⟩:=d
    have small:k≤C+1:=by
      apply Nat.le_of_mul_le_mul_left (c:=q) _ (by omega)
      rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm q C];omega
    exact near_minus pp qp gp gt small hcon e inert

private theorem F_standard : ∀ n, PisanoSource.F n=Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n+2 => by rw [PisanoSource.F,Nat.fib_add_two,F_standard (n+1),F_standard n,Nat.add_comm]

private theorem cassini_square (p:ℕ) (n:ℕ) :
    ((WallLift.U p (n+1))^2-WallLift.U p n*WallLift.U p (n+1)-(WallLift.U p n)^2)^2=1 := by
  induction n with
  | zero => norm_num [WallLift.U,PisanoSource.F]
  | succ k ih =>
    rw [WallLift.recF p k]
    linear_combination ih

/-- A modulus dividing F(n) has 4n as a period of the full Fibonacci sequence. -/
theorem period (p n:ℕ) (h:p∣Nat.fib n) : ∀ j, Nat.fib (j+4*n)%p=Nat.fib j%p := by
  have z:WallLift.U p n=0:=(ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr (F_standard n ▸ h)
  have fourth:((WallLift.U p (n+1))^2)^2=1:= by
    simpa only [z,zero_mul,zero_pow (by decide : 2≠0),sub_zero] using cassini_square p n
  have scalar (j:ℕ) : WallLift.U p (j+n)=WallLift.U p j*WallLift.U p (n+1) := by
    rw [(WallLift.addF _ _ _).1,z,mul_zero,add_zero]
  intro j
  apply (ZMod.natCast_eq_natCast_iff' _ _ _).mp
  rw [←F_standard,←F_standard]
  change WallLift.U p (j+4*n)=WallLift.U p j
  rw [show j+4*n=j+n+n+n+n by omega,scalar,scalar,scalar,scalar]
  linear_combination WallLift.U p j*fourth

end FibonacciLargeFactor
#print axioms FibonacciLargeFactor.unbounded
#print axioms FibonacciLargeFactor.period
