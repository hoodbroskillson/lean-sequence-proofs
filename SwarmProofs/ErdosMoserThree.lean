import SwarmProofs.ErdosMoser

/-! The modulo-three restriction on the Erdős–Moser equation from Theorem 2(2)
of Pieter Moree (https://arxiv.org/abs/1011.2940), assuming its even-exponent
condition. The descent uses three equal blocks of consecutive terms. -/

namespace ErdosMoser

private theorem even_power_mod_three (a t : Nat) :
    a ^ (2*(t+1)) % 3 = if a % 3 = 0 then 0 else 1 := by
  have hs : a^2 % 3 = if a % 3 = 0 then 0 else 1 := by
    rw [Nat.pow_mod a 2 3]
    have cases : a%3=0 ∨ a%3=1 ∨ a%3=2 := by omega
    rcases cases with h | h | h <;> rw [h] <;> decide
  rw [Nat.pow_mul, Nat.pow_mod, hs]
  split <;> simp

private theorem sum_mod_three (h t : Nat) :
    powerSum (2*(t+1)) (3*h) % 3 = (2*h)%3 := by
  induction h with
  | zero => rfl
  | succ h ih =>
    rw [show 3*(h+1) = 3*h+1+1+1 by omega, powerSum, powerSum, powerSum]
    have h0 := even_power_mod_three (3*h) t
    have h1 := even_power_mod_three (3*h+1) t
    have h2 := even_power_mod_three (3*h+2) t
    simp [show (3*h)%3=0 by omega, show (3*h+1)%3=1 by omega,
      show (3*h+2)%3=2 by omega] at h0 h1 h2
    omega

/-- Shifting each of three summands by the same offset leaves a multiple of
`3*h` as the correction, provided that `3` divides the block length `h`. -/
private theorem triple_power (a h k : Nat) (hh : h % 3 = 0) :
    ∃ w, a^k + (h+a)^k + (2*h+a)^k = 3*a^k + (3*h)*w := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨w, hw⟩ := ih
    have hx : (h+a)^k % 3 = a^k % 3 := by
      rw [Nat.pow_mod (h+a), Nat.add_mod, hh, Nat.zero_add, Nat.mod_mod]
      exact (Nat.pow_mod a k 3).symm
    have hy : (2*h+a)^k % 3 = a^k % 3 := by
      rw [Nat.pow_mod (2*h+a), Nat.add_mod,
          show (2*h)%3=0 by omega, Nat.zero_add, Nat.mod_mod]
      exact (Nat.pow_mod a k 3).symm
    let v := ((h+a)^k + 2*(2*h+a)^k) / 3
    have hv : (h+a)^k + 2*(2*h+a)^k = 3*v := by dsimp [v]; omega
    refine ⟨a*w+v, ?_⟩
    simp only [Nat.pow_succ]
    grind

private theorem three_blocks (h k : Nat) (hh : h%3=0) :
    ∃ w, powerSum k (3*h) = 3*powerSum k h + (3*h)*w := by
  have block (a : Nat) : ∃ w,
      powerSum k a + powerSum k (h+a) + powerSum k (2*h+a) =
      powerSum k h + powerSum k (2*h) + 3*powerSum k a + (3*h)*w := by
    induction a with
    | zero => exact ⟨0, by simp [powerSum]⟩
    | succ a ih =>
      obtain ⟨w, hw⟩ := ih
      obtain ⟨v, hv⟩ := triple_power a h k hh
      refine ⟨w+v, ?_⟩
      simp only [powerSum]
      grind
  obtain ⟨w, hw⟩ := block h
  rw [show h+h=2*h by omega, show 2*h+h=3*h by omega] at hw
  exact ⟨w, by omega⟩

private theorem nondivisibility_three (m t : Nat) (hm : 0<m) (he : m%3=0) :
    ¬ m ∣ powerSum (2*(t+1)) m := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro hd
    let h := m / 3
    have hm' : m=3*h := by dsimp [h]; omega
    by_cases hh : h%3=0
    · obtain ⟨w, hw⟩ := three_blocks h (2*(t+1)) hh
      have hzero := Nat.mod_eq_zero_of_dvd hd
      rw [hm', hw, Nat.add_mul_mod_self_left, Nat.mul_mod_mul_left] at hzero
      exact ih h (by omega) (by omega) hh (Nat.dvd_of_mod_eq_zero (by omega))
    · have hz := Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (show 3 ∣ m from ⟨h,hm'⟩) hd)
      rw [hm', sum_mod_three] at hz
      omega

/-- A positive solution of the Erdős–Moser equation with even exponent at least
two has residue one or two modulo three. -/
theorem not_zero_mod_three (m k : Nat) (hm : 0<m) (hk : 2≤k)
    (he : k%2=0) (hsol : powerSum k m = m^k) : m%3 ≠ 0 := by
  intro h
  let t := k/2-1
  have hkt : k=2*(t+1) := by dsimp [t]; omega
  apply nondivisibility_three m t hm h
  rw [← hkt, hsol]
  simpa using (Nat.pow_dvd_pow m (show 1≤k by omega))

end ErdosMoser

/-- info: 'ErdosMoser.not_zero_mod_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErdosMoser.not_zero_mod_three
