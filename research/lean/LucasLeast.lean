import LucasPeriods
namespace LucasLeast
open LucasPeriods LucasZeros TailGcd

private def state (m n : ℕ) : ZMod m × ZMod m := (luc (n+2), luc (n+3))
private def step (m : ℕ) (x : ZMod m × ZMod m) : ZMod m × ZMod m := (x.2,x.2+x.1)
private theorem advance (m n : ℕ) : state m (n+1)=step m (state m n) := by
  apply Prod.ext
  · rfl
  · change ((luc (n+3)+luc (n+2):ℕ):ZMod m)=_
    push_cast
    rfl

private theorem injective (m : ℕ) : Function.Injective (step m) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have e₁ : b=d := congrArg Prod.fst h
  have e₂ : b+a=d+c := congrArg Prod.snd h
  subst d
  exact Prod.ext (add_left_cancel e₂) rfl

theorem exists_period {m : ℕ} (hm : 1<m) : ∃t,0<t ∧ Lucas m t := by
  letI : NeZero m := ⟨by omega⟩
  obtain ⟨i,j,hij,eq⟩ := Finite.exists_ne_map_eq_of_infinite (state m)
  have fromEq (i t : ℕ) (eq : state m (i+t)=state m i) : Lucas m t := by
    have back (j : ℕ) : state m (j+t)=state m j → state m t=state m 0 := by
      induction j with
      | zero => simp
      | succ j ih =>
        intro h
        rw [show j+1+t=j+t+1 by omega,advance,advance] at h
        exact ih (injective m h)
    have fwd (j : ℕ) : state m (j+t)=state m j := by
      induction j with
      | zero => simpa using back i eq
      | succ j ih => rw [show j+1+t=j+t+1 by omega,advance,advance,ih]
    intro n hn
    have e:=congrArg Prod.fst (fwd (n-2))
    change (luc (n-2+t+2):ZMod m)=luc (n-2+2) at e
    simpa only [show n-2+t+2=n+t by omega,show n-2+2=n by omega] using e
  rcases lt_or_gt_of_ne hij with h|h
  · exact ⟨j-i,by omega,fromEq i (j-i) (by simpa only [show i+(j-i)=j by omega] using eq.symm)⟩
  · exact ⟨i-j,by omega,fromEq j (i-j) (by simpa only [show j+(i-j)=i by omega] using eq)⟩

noncomputable def L {m : ℕ} (hm : 1<m) : ℕ := by
  classical
  exact Nat.find (exists_period hm)

theorem least_spec {m : ℕ} (hm : 1<m) : 0<L hm ∧ Lucas m (L hm) := by
  classical
  exact Nat.find_spec (exists_period hm)

theorem lucas_iff {m : ℕ} (hm : 1<m) (t : ℕ) : Lucas m t ↔ L hm ∣ t := by
  classical
  constructor
  · intro h
    have s:=least_spec hm
    let g:=Nat.gcd (L hm) t
    have pos:0<g:=Nat.gcd_pos_of_pos_left t s.1
    have low : L hm ≤ g := Nat.find_min' (exists_period hm) ⟨pos,gcd_period _ _ s.2 h⟩
    have high := Nat.le_of_dvd s.1 (Nat.gcd_dvd_left (L hm) t)
    have eq : g=L hm := by dsimp [g] at *; omega
    exact eq ▸ (show g∣t from Nat.gcd_dvd_right _ _)
  · exact multiples (least_spec hm).2

theorem source {m : ℕ} (hm : 1<m) (N t : ℕ) :
    FinitePeriod.Tail m N t ↔ t=0 ∨ (5≤N ∧ 3*Nat.lcm 2 (L hm)∣t) := by
  rw [LucasPeriods.characterize hm]
  apply or_congr_right
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨s,rfl,hl⟩
    have d := Nat.lcm_dvd (dvd_mul_right 2 s) ((lucas_iff hm _).mp hl)
    simpa only [←Nat.mul_assoc] using Nat.mul_dvd_mul_left 3 d
  · rintro ⟨k,hk⟩
    let z:=Nat.lcm 2 (L hm)*k
    have hz : 2∣z := dvd_trans (Nat.dvd_lcm_left _ _) (dvd_mul_right _ _)
    obtain ⟨s,hs⟩:=hz
    refine ⟨s,?_,(lucas_iff hm _).mpr ?_⟩
    · rw [Nat.mul_assoc] at hk
      change t=3*z at hk
      omega
    · rw [←hs]
      exact dvd_trans (Nat.dvd_lcm_right _ _) (dvd_mul_right _ _)

theorem positive {m : ℕ} (hm : 1<m) : 0<3*Nat.lcm 2 (L hm) :=
  Nat.mul_pos (by decide) (Nat.lcm_pos (by decide) (least_spec hm).1)
end LucasLeast
#print axioms LucasLeast.source
#print axioms LucasLeast.positive
