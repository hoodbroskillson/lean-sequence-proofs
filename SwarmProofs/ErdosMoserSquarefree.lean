import SwarmProofs.ErdosMoser

/-! The squarefreeness of `m - 1` is part of Theorem 2(3) in Pieter Moree,
"Moser's mathemagical work on the equation 1^k + ... + (m-1)^k = m^k"
(https://arxiv.org/abs/1011.2940). We deduce this necessary condition from a
block-sum congruence that also treats the right-hand multiplier in the
generalized Erdős–Moser equation (https://arxiv.org/abs/1010.2275). -/

namespace ErdosMoser

private theorem sum_after_multiple (k d t b : Nat) :
    powerSum k (d * t + b) % d =
      (powerSum k (d * t) + powerSum k b) % d := by
  induction b with
  | zero => simp [powerSum]
  | succ b ih =>
    change (powerSum k (d*t+b) + (d*t+b)^k) % d =
      (powerSum k (d*t) + (powerSum k b + b^k)) % d
    have hpow : (d*t+b)^k % d = b^k % d := by
      rw [Nat.pow_mod, Nat.mul_add_mod_self_left, ← Nat.pow_mod]
    rw [← Nat.add_assoc, Nat.add_mod, ih, hpow, ← Nat.add_mod]

/-- Each complete block of length d contributes the same residue modulo d. -/
theorem powerSum_complete_blocks (k d t : Nat) :
    powerSum k (d * t) % d = (t * powerSum k d) % d := by
  induction t with
  | zero => simp [powerSum]
  | succ t ih =>
    rw [Nat.mul_succ, sum_after_multiple, Nat.succ_mul, Nat.add_mod, ih, ← Nat.add_mod]

/-- For the generalized equation with multiplier a, a square factor d² of
m − 1 forces d to divide a. The divisor d may be composite. -/
theorem square_divisor_forces_multiplier (m k a d : Nat) (hm : 0 < m) (hk : 0 < k)
    (hd : 2 ≤ d) (hsq : d * d ∣ m - 1) (hsol : powerSum k m = a * m^k) :
    d ∣ a := by
  obtain ⟨t, ht⟩ := hsq
  rw [Nat.mul_assoc] at ht
  have hm' : m = d * (d * t) + 1 := by omega
  have hone : 1 % d = 1 := Nat.mod_eq_of_lt (by omega)
  have hmres : m^k % d = 1 := by
    rw [hm', Nat.pow_mod, Nat.mul_add_mod_self_left, hone, Nat.one_pow, hone]
  have hzero : powerSum k m % d = 0 := by
    rw [hm', powerSum, Nat.add_mod, powerSum_complete_blocks, Nat.pow_mod,
      Nat.mul_mod_right, Nat.zero_pow hk, Nat.mul_assoc, Nat.mul_mod_right]
    simp
  rw [hsol, Nat.mul_mod, hmres, Nat.mul_one, Nat.mod_mod] at hzero
  exact Nat.dvd_of_mod_eq_zero hzero

/-- The predecessor of every positive Erdős–Moser solution is squarefree. -/
theorem predecessor_squarefree (m k : Nat) (hm : 0 < m) (hk : 0 < k)
    (hsol : powerSum k m = m^k) :
    ∀ d : Nat, 2 ≤ d → ¬ d * d ∣ m - 1 := by
  intro d hd hsq
  have h := square_divisor_forces_multiplier m k 1 d hm hk hd hsq (by simpa using hsol)
  have hle := Nat.le_of_dvd (by decide : 0 < 1) h
  omega

end ErdosMoser

/-! Kernel axiom audits for both the generalized result and its classical specialization. -/
/-- info: 'ErdosMoser.square_divisor_forces_multiplier' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ErdosMoser.square_divisor_forces_multiplier

/-- info: 'ErdosMoser.predecessor_squarefree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ErdosMoser.predecessor_squarefree
