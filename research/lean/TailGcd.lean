import Mathlib.Data.Nat.Prime
namespace TailGcd
def From {α : Type*} (a : ℕ → α) (N t : ℕ) := ∀ n, N ≤ n → a (n+t) = a n

theorem multiples {α : Type*} {a : ℕ → α} {N d t : ℕ} (h : From a N d) (hd : d ∣ t) : From a N t := by
  obtain ⟨k,rfl⟩ := hd
  intro n hn
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ,←Nat.add_assoc,h _ (Nat.le_trans hn (Nat.le_add_right _ _)),ih]

theorem gcd_period {α : Type*} {a : ℕ → α} {N : ℕ} (x y : ℕ) :
    From a N x → From a N y → From a N (x.gcd y) := by
  induction x,y using Nat.gcd.induction with
  | H0 y => simp
  | H1 x y _ ih =>
    intro h1 h2
    rw [Nat.gcd_rec]
    apply ih _ h1
    intro n hn
    have h := multiples h1 (dvd_mul_right x (y/x)) (n+y%x) (by omega)
    rw [Nat.add_assoc, Nat.mod_add_div] at h
    exact h.symm.trans (h2 n hn)

theorem remove_prime {α : Type*} {a : ℕ → α} {N p t v : ℕ} (hp : p.Prime) (hn : ¬p∣t)
    (ht : From a N t) (hv : From a N (p*v)) : From a N v := by
  let g := t.gcd (p*v)
  have hgt : g∣t := Nat.gcd_dvd_left _ _
  have hgp : g.Coprime p := (hp.coprime_iff_not_dvd.mpr (fun h => hn (dvd_trans h hgt))).symm
  exact multiples (gcd_period t (p*v) ht hv) (hgp.dvd_of_dvd_mul_left (Nat.gcd_dvd_right _ _))
end TailGcd
#print axioms TailGcd.remove_prime
