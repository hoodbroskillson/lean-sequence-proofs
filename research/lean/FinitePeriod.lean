import FiniteOrder
import TailGcd
namespace FinitePeriod
open ZeroEnumeration TailGcd

private theorem recE (p n : ℕ) (h : 5≤n) :
    (entry (n+18):ZMod p)+4*entry (n+6)=4*entry (n+12)+entry n := by
  exact_mod_cast congrArg (fun j : ℕ => (j:ZMod p)) (sparse_recurrence n h)

theorem window (p L : ℕ) (cert : ∀i : Fin 18,(entry (5+i.val+L):ZMod p)=entry (5+i.val)) :
    From (fun n => (entry n:ZMod p)) 5 L := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases small : n<23
    · simpa only [show 5+(n-5)=n by omega] using cert ⟨n-5,by omega⟩
    · let m := n-18
      have h5 : 5≤m := by dsimp [m];omega
      have e : m+18=n := by dsimp [m];omega
      have a:=recE p m h5
      have b:=recE p (m+L) (by omega)
      have z (j : ℕ) (hj:j<18) : (entry (m+L+j):ZMod p)=entry (m+j) := by
        rw [show m+L+j=m+j+L by omega]; exact ih _ (by omega) (by omega)
      rw [z 6 (by decide),z 12 (by decide),(show (entry (m+L):ZMod p)=entry m from ih m (by omega) h5),
        show m+L+18=n+L by omega] at b
      rw [e] at a
      exact add_right_cancel (b.trans a.symm)

def Tail (p N t : ℕ) := From (fun n => (CanonicalZeros.a n:ZMod p)) N t

theorem all {p L : ℕ} (hL : 0<L) (cert : ∀i : Fin 18,(entry (5+i.val+L):ZMod p)=entry (5+i.val))
    (proper : ∀j : Fin L, 0<j.val → j.val∣L → ∃i : Fin 18, (entry (5+i.val+j.val):ZMod p)≠entry (5+i.val))
    (bad : (entry (4+L):ZMod p)≠entry 4) (N t : ℕ) :
    Tail p N t ↔ t=0 ∨ (5≤N ∧ L∣t) := by
  let f (n:ℕ) := (CanonicalZeros.a n:ZMod p)
  have up : From f 5 L := by
    intro n hn
    simpa only [f,CanonicalZeros.source_entry _ (show 0<n+L by omega),
        CanonicalZeros.source_entry _ (show 0<n by omega)] using
      (show (entry (n+L):ZMod p)=entry n from window p L cert n hn)
  by_cases tz:t=0
  · subst t; simp [Tail,From]
  rw [or_iff_right tz]
  constructor
  · intro h
    have back : From f 5 t := by
      intro n hn
      have mv (j : ℕ) (hj : 5≤j) := multiples up (dvd_mul_right L N) j hj
      have eq := h (n+L*N) (by have := Nat.le_mul_of_pos_left N hL; omega)
      rw [show n+L*N+t=n+t+L*N by omega] at eq
      exact (mv _ (by omega : 5≤n+t)).symm.trans (eq.trans (mv _ hn))
    have g := gcd_period t L back up
    have gpos := Nat.gcd_pos_of_pos_right t hL
    have dv := Nat.gcd_dvd_right t L
    have same : Nat.gcd t L=L := by
      by_contra ne
      obtain ⟨i,hi⟩ := proper ⟨_,(Nat.le_of_dvd hL dv).lt_of_ne ne⟩ gpos dv
      apply hi
      have eq := g (5+i.val) (by omega)
      dsimp [f] at eq
      simpa only [CanonicalZeros.source_entry _ (show 0<5+i.val+Nat.gcd t L by omega),
          CanonicalZeros.source_entry _ (show 0<5+i.val by omega)] using eq
    have dt : L∣t := same ▸ Nat.gcd_dvd_left t L
    refine ⟨?_,dt⟩
    by_contra! ns
    obtain ⟨k,rfl⟩ := dt
    have kp : 0<k := Nat.pos_of_ne_zero (fun z => tz (by simp [z]))
    have he : L*(k-1)+L=L*k := by rw [←Nat.mul_succ,show (k-1).succ=k by omega]
    have a:=multiples up (dvd_mul_right L (k-1)) (4+L) (by omega)
    have b:=h 4 (by omega)
    change f (4+L*k)=f 4 at b
    rw [show 4+L*k=4+L+L*(k-1) by omega] at b
    have eq := a.symm.trans b
    apply bad
    simpa only [f,CanonicalZeros.source_entry _ (show 0<4+L by omega),
        CanonicalZeros.source_entry _ (show 0<4 by decide)] using eq
  · rintro ⟨hn,dv⟩ n h
    exact multiples up dv n (by omega)

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem period2 (N t : ℕ) : Tail 2 N t ↔ t=0 ∨ (5≤N ∧ 18∣t) :=
  all (by decide) (by decide) (by decide) (by decide) N t
theorem period5 (N t : ℕ) : Tail 5 N t ↔ t=0 ∨ (5≤N ∧ 12∣t) :=
  all (by decide) (by decide) (by decide) (by decide) N t
theorem period7 (N t : ℕ) : Tail 7 N t ↔ t=0 ∨ (5≤N ∧ 48∣t) :=
  all (by decide) (by decide) (by decide) (by decide) N t
theorem period19 (N t : ℕ) : Tail 19 N t ↔ t=0 ∨ (5≤N ∧ 54∣t) :=
  all (by decide) (by decide) (by decide) (by decide) N t
end FinitePeriod
#print axioms FinitePeriod.period2
#print axioms FinitePeriod.period5
#print axioms FinitePeriod.period7
#print axioms FinitePeriod.period19
