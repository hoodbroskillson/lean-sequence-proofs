import SixPhases
namespace LucasPeriods
open ZeroEnumeration LucasZeros TailGcd SixPhases
/-- The ordered Lucas weights agree with the classical Lucas sequence at indices i≥2. -/
def Lucas (m t : ℕ) := From (fun i => (luc i:ZMod m)) 2 t

private theorem slot (m k j : ℕ) (hj:j<6) :
    E m (6*k+j+9)=(luc (2*k+6+(if j<2 then 0 else 1)):ZMod m)-(offset j:ℕ) := by
  unfold E; rw [six k j hj,term,Nat.cast_sub]
  have bound : offset j≤5 := by
    rcases j with _|_|_|_|_|j <;> simp [offset]
  exact bound.trans ((show 5≤luc 4 by decide).trans (luc_mono.monotone (by omega)))

theorem six_iff (m s : ℕ) : FinitePeriod.Tail m 5 (6*s) ↔ Lucas m (2*s) := by
  constructor
  · intro h
    have bk:=back h
    have forSlot (k j : ℕ) (hj:j<6) :
        (luc (2*(k+s)+6+(if j<2 then 0 else 1)):ZMod m)=luc (2*k+6+(if j<2 then 0 else 1)) := by
      have eq:=bk (6*k+j+9) (by omega)
      rw [show 6*k+j+9+6*s=6*(k+s)+j+9 by omega,slot _ _ _ hj,slot _ _ _ hj] at eq
      exact sub_left_inj.mp eq
    have eventual (i : ℕ) (hi : 6≤i) : (luc (i+2*s):ZMod m)=luc i := by
      let k := (i-6)/2
      by_cases even : (i-6)%2=0
      · simpa only [if_pos (by decide : 0<2),Nat.add_zero,show 2*k+6=i by dsimp [k];omega,
          show 2*(k+s)+6=i+2*s by dsimp [k];omega] using forSlot k 0 (by decide)
      · simpa only [if_neg (by decide : ¬2<2),show 2*k+6+1=i by dsimp [k];omega,
          show 2*(k+s)+6+1=i+2*s by dsimp [k];omega] using forSlot k 2 (by decide)
    have rec (n : ℕ) (hn : 2≤n) : (luc (n+2):ZMod m)=luc (n+1)+luc n := by
      obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hn
      rw [show n=d+2 by omega]
      change ((luc (d+3)+luc (d+2):ℕ):ZMod m)=_
      push_cast
      rfl
    have aux (k : ℕ) : ∀n,6≤n+k → 2≤n → (luc (n+2*s):ZMod m)=luc n := by
      induction k with
      | zero => exact fun n hn _ => eventual n (by omega)
      | succ k ih =>
        intro n hn hl
        have eq:=rec (n+2*s) (by omega)
        rw [show n+2*s+2=n+2+2*s by omega,show n+2*s+1=n+1+2*s by omega,
            ih (n+2) (by omega) (by omega),ih (n+1) (by omega) (by omega),rec n hl] at eq
        exact (add_left_cancel eq).symm
    exact fun n hn => aux 6 n (by omega) hn
  · intro h
    have upper : FinitePeriod.Tail m 9 (6*s) := by
      intro n hn
      let k := (n-9)/6
      let j := (n-9)%6
      have hj : j<6 := Nat.mod_lt _ (by decide)
      have eq : n=6*k+j+9 := by dsimp [k,j];omega
      have a := h (2*k+6+(if j<2 then 0 else 1)) (by omega)
      change (luc (_+2*s):ZMod m)=luc _ at a
      rw [show 2*k+6+(if j<2 then 0 else 1)+2*s=2*(k+s)+6+(if j<2 then 0 else 1) by omega] at a
      change (CanonicalZeros.a (n+6*s):ZMod m)=CanonicalZeros.a n
      rw [CanonicalZeros.source_entry _ (by omega),CanonicalZeros.source_entry _ (by omega)]
      change E m (n+6*s)=E m n
      rw [show n+6*s=6*(k+s)+j+9 by omega,eq,slot _ _ _ hj,slot _ _ _ hj,a]
    intro n hn
    have e:=back upper n hn
    simpa only [CanonicalZeros.source_entry _ (show 0<n+6*s by omega),CanonicalZeros.source_entry _ (show 0<n by omega)] using e

private theorem start {m N t : ℕ} (hm : 1<m) (ht : 0<t) (h : FinitePeriod.Tail m N t) : 5≤N := by
  by_contra! small
  have e := congrArg (fun x : ℕ => (x:ZMod m)) (sparse_recurrence (4+t) (by omega))
  push_cast at e
  have mov (i : ℕ) (hi:4≤i) : (entry (i+t):ZMod m)=entry i := by
    have eq:=h i (by omega)
    simpa only [CanonicalZeros.source_entry _ (show 0<i+t by omega),CanonicalZeros.source_entry _ (show 0<i by omega)] using eq
  rw [show 4+t+18=22+t by omega,show 4+t+6=10+t by omega,show 4+t+12=16+t by omega,
      mov 22 (by decide),mov 10 (by decide),mov 16 (by decide),mov 4 le_rfl] at e
  change ((122:ℕ):ZMod m)+4*(17:ℕ)=4*(46:ℕ)+(5:ℕ) at e
  have one : (1:ZMod m)=0 := by linear_combination e
  have dv : m∣1 := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp (by simpa using one)
  have := Nat.le_of_dvd (by decide : 0<1) dv
  omega

theorem characterize {m : ℕ} (hm : 1<m) (N t : ℕ) :
    FinitePeriod.Tail m N t ↔ t=0 ∨ (5≤N ∧ ∃s, t=6*s ∧ Lucas m (2*s)) := by
  constructor
  · intro h
    by_cases zero:t=0
    · exact Or.inl zero
    obtain ⟨s,hs⟩:=divides hm h
    refine Or.inr ⟨start hm (by omega) h,s,hs,(six_iff m s).mp ?_⟩
    subst t
    intro n hn
    have e:=back h n hn
    simpa only [CanonicalZeros.source_entry _ (show 0<n+6*s by omega),CanonicalZeros.source_entry _ (show 0<n by omega)] using e
  · rintro (rfl|⟨lt,s,rfl,hh⟩)
    · intro _ _;rfl
    · exact fun n hn => (six_iff m s).mpr hh n (by omega)

end LucasPeriods
#print axioms LucasPeriods.six_iff
#print axioms LucasPeriods.characterize
