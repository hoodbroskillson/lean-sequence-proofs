import Std

/-! A congruence obstruction for the Erdős–Moser equation, as in Theorem 2(2) of
Pieter Moree, "Moser's mathemagical work on the equation
1^k + 2^k + ... + (m-1)^k = m^k" (https://arxiv.org/abs/1011.2940). -/

namespace ErdosMoser

/-- Sum of the kth powers of the natural numbers strictly below m. -/
def powerSum (k : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => powerSum k m + m ^ k

private theorem power_mod_four (n t : Nat) :
    n ^ (2 * (t + 1)) % 4 = n % 2 := by
  have hs : n ^ 2 % 4 = n % 2 := by
    rw [Nat.pow_mod n 2 4]
    have h : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases h with h | h | h | h <;> rw [h] <;> omega
  rw [Nat.pow_mul, Nat.pow_mod, hs]
  by_cases hp : n % 2 = 0
  · simp [hp]
  · have hp' : n % 2 = 1 := by omega
    simp [hp']

private theorem sum_mod_four (m t : Nat) :
    powerSum (2 * (t + 1)) m % 4 = (m / 2) % 4 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [powerSum, Nat.add_mod, ih, power_mod_four]
    omega

private theorem shifted_power (a u t : Nat) :
    (2*u + a) ^ (2*t) % (2*(2*u)) = a ^ (2*t) % (2*(2*u)) := by
  have hs : (2*u + a)^2 = a^2 + (2*(2*u))*(u+a) := by grind
  have hsmod : (2*u+a)^2 % (2*(2*u)) = a^2 % (2*(2*u)) := by
    rw [hs, Nat.add_mul_mod_self_left]
  rw [Nat.pow_mul, Nat.pow_mul, Nat.pow_mod, hsmod, ← Nat.pow_mod]

private theorem shifted_sum (u t b : Nat) :
    powerSum (2*t) (2*u+b) % (2*(2*u)) =
    (powerSum (2*t) (2*u) + powerSum (2*t) b) % (2*(2*u)) := by
  induction b with
  | zero => simp [powerSum]
  | succ b ih =>
    change (powerSum (2*t) (2*u+b) + (2*u+b)^(2*t)) % _ =
      (powerSum (2*t) (2*u) + (powerSum (2*t) b + b^(2*t))) % _
    rw [← Nat.add_assoc]
    rw [Nat.add_mod, ih, shifted_power, ← Nat.add_mod]

/-- Pair the lower and upper halves when m is divisible by four. Descent then
reduces the obstruction to the case where m/2 is odd. -/
private theorem even_nondivisibility (t m : Nat) (hm : 0 < m) (he : m % 2 = 0) :
    ¬ m ∣ powerSum (2*(t+1)) m := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro hd
    let h := m / 2
    have hm' : m = 2*h := by dsimp [h]; omega
    by_cases hh : h % 2 = 0
    · let u := h / 2
      have hu : h = 2*u := by dsimp [u]; omega
      have hpair := shifted_sum u (t+1) (2*u)
      rw [← hu, ← Nat.two_mul, ← Nat.two_mul] at hpair
      have hzero := Nat.mod_eq_zero_of_dvd hd
      rw [hm', hpair, Nat.mul_mod_mul_left] at hzero
      exact ih h (by omega) (by omega) hh (Nat.dvd_of_mod_eq_zero (by omega))
    · have htwo : 2 ∣ m := ⟨h, hm'⟩
      have hz := Nat.mod_eq_zero_of_dvd (Nat.dvd_trans htwo hd)
      have hfour := sum_mod_four m t
      dsimp [h] at hh
      omega

/-- Every positive solution with even exponent at least two has m ≡ 3 (mod 8). -/
theorem three_mod_eight (m k : Nat) (hm : 0 < m) (hk : 2 ≤ k)
    (he : k % 2 = 0) (hsol : powerSum k m = m ^ k) : m % 8 = 3 := by
  let t := k / 2 - 1
  have hkt : k = 2*(t+1) := by dsimp [t]; omega
  rw [hkt] at hsol
  have hodd : m % 2 ≠ 0 := by
    intro h
    apply even_nondivisibility t m hm h
    rw [hsol]
    simpa using (Nat.pow_dvd_pow m (show 1 ≤ 2*(t+1) by omega))
  have h := sum_mod_four m t
  rw [hsol, power_mod_four] at h
  omega

end ErdosMoser

/-- info: 'ErdosMoser.three_mod_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErdosMoser.three_mod_eight
