import FinitePeriod
import Mathlib.Tactic.LinearCombination
namespace SixPhases
open ZeroEnumeration LucasZeros TailGcd

def E (m n : ℕ) : ZMod m := entry n
def jump (m n : ℕ) := E m (n+1)-E m n

theorem back {m N t : ℕ} (h : FinitePeriod.Tail m N t) : From (E m) 5 t := by
  have rec (n : ℕ) (hn : 5≤n) : E m (n+18)+4*E m (n+6)=4*E m (n+12)+E m n := by
    unfold E; exact_mod_cast congrArg (fun a : ℕ => (a:ZMod m)) (sparse_recurrence n hn)
  have aux (k : ℕ) : ∀n, N≤n+k → 5≤n → E m (n+t)=E m n := by
    induction k with
    | zero =>
      intro n hn h5
      have eq:=h n (by omega)
      unfold E
      simpa only [CanonicalZeros.source_entry _ (show 0<n+t by omega),CanonicalZeros.source_entry _ (show 0<n by omega)] using eq
    | succ k ih =>
      intro n hn h5
      have eq:=rec (n+t) (by omega)
      have base:=rec n h5
      have z (j : ℕ) (hj:0<j) : E m (n+t+j)=E m (n+j) := by
        rw [show n+t+j=n+j+t by omega]; exact ih _ (by omega) (by omega)
      rw [z 18 (by decide),z 6 (by decide),z 12 (by decide)] at eq
      linear_combination base-eq
  exact fun n hn => aux N n (by omega) hn

private theorem slots (k : ℕ) : 5≤luc (2*k+6) ∧ 5≤luc (2*k+7) := by
  have b : 5≤luc 4 := by decide
  exact ⟨b.trans (luc_mono.monotone (by omega)),b.trans (luc_mono.monotone (by omega))⟩

private theorem slot0 (m k : ℕ) : jump m (6*k+9)=1 := by
  unfold jump E
  rw [show 6*k+9+1=6*k+1+9 by omega, six k 1 (by decide),
    show 6*k+9=6*k+0+9 by omega,six k 0 (by decide)]
  change ((luc (2*k+6)-1:ℕ):ZMod m)-((luc (2*k+6)-2:ℕ):ZMod m)=1
  have b:=slots k
  rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega)]
  push_cast
  ring

private theorem slot2 (m k : ℕ) : jump m (6*k+11)=2 := by
  unfold jump E
  rw [show 6*k+11+1=6*k+3+9 by omega, six k 3 (by decide),
    show 6*k+11=6*k+2+9 by omega,six k 2 (by decide)]
  change ((luc (2*k+7)-3:ℕ):ZMod m)-((luc (2*k+7)-5:ℕ):ZMod m)=2
  have b:=slots k
  rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega)]
  push_cast
  ring

private theorem slot3 (m k : ℕ) : jump m (6*k+12)=1 := by
  unfold jump E
  rw [show 6*k+12+1=6*k+4+9 by omega, six k 4 (by decide),
    show 6*k+12=6*k+3+9 by omega,six k 3 (by decide)]
  change ((luc (2*k+7)-2:ℕ):ZMod m)-((luc (2*k+7)-3:ℕ):ZMod m)=1
  have b:=slots k
  rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega)]
  push_cast
  ring

private theorem slot4 (m k : ℕ) : jump m (6*k+13)=1 := by
  unfold jump E
  rw [show 6*k+13+1=6*k+5+9 by omega, six k 5 (by decide),
    show 6*k+13=6*k+4+9 by omega,six k 4 (by decide)]
  change ((luc (2*k+7)-1:ℕ):ZMod m)-((luc (2*k+7)-2:ℕ):ZMod m)=1
  have b:=slots k
  rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega)]
  push_cast
  ring

theorem divides {m N t : ℕ} (hm : 1<m) (ht : FinitePeriod.Tail m N t) : 6∣t := by
  have bk:=back ht
  have mark (i : ℕ) (hi : 5≤i) : jump m (i+t)=jump m i := by
    unfold jump
    rw [show i+t+1=i+1+t by omega,bk (i+1) (by omega),bk i hi]
  let k:=t/6
  have small:=Nat.mod_lt t (by decide : 0<6)
  have nt : (1:ZMod m)≠0 := by
    intro eq
    have dd : m∣1 := (ZMod.natCast_zmod_eq_zero_iff_dvd 1 m).mp (by simpa using eq)
    have := Nat.le_of_dvd (by decide : 0<1) dd
    omega
  by_contra nd
  have cases : t=6*k+1 ∨ t=6*k+2 ∨ t=6*k+3 ∨ t=6*k+4 ∨ t=6*k+5 := by dsimp [k]; omega
  apply nt
  rcases cases with h|h|h|h|h
  · have a:=mark (11) (by decide)
    rw [show 11+t=6*(k+0)+12 by omega,slot3,
        show 11=6*0+11 by decide,slot2] at a
    linear_combination -a
  · have a:=mark (9) (by decide)
    rw [show 9+t=6*(k+0)+11 by omega,slot2,
        show 9=6*0+9 by decide,slot0] at a
    linear_combination a
  · have a:=mark 10 (by decide)
    have b:=mark 22 (by decide)
    rw [show 10+t=6*k+13 by omega,slot4] at a
    rw [show 22+t=6*(k+2)+13 by omega,slot4] at b
    have e : jump m 10=7 := by
      change ((24:ℕ):ZMod m)-(17:ℕ)=7
      push_cast
      ring
    have f : jump m 22=72 := by
      change ((194:ℕ):ZMod m)-(122:ℕ)=72
      push_cast
      ring
    rw [e] at a; rw [f] at b
    linear_combination b-12*a
  · have a:=mark (11) (by decide)
    rw [show 11+t=6*(k+1)+9 by omega,slot0,
        show 11=6*0+11 by decide,slot2] at a
    linear_combination -a
  · have a:=mark (12) (by decide)
    rw [show 12+t=6*(k+1)+11 by omega,slot2,
        show 12=6*0+12 by decide,slot3] at a
    linear_combination a
end SixPhases
#print axioms SixPhases.divides
