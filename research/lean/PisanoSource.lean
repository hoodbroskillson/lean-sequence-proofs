import LucasLeast
namespace PisanoSource
open TailGcd LucasPeriods LucasZeros
/-- The Fibonacci numbers with both occurrences of 1 included. -/
def F : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n+2 => F (n+1)+F n

theorem bridge (m n : ℕ) :
    (luc (n+2):ZMod m)=F n+3*F (n+1) ∧ (luc (n+3):ZMod m)=3*F n+4*F (n+1) := by
  induction n with
  | zero => constructor <;> norm_num [luc,F]
  | succ i ih =>
    have f : (F (i+2):ZMod m)=F (i+1)+F i := by change ((F (i+1)+F i:ℕ):ZMod m)=_; push_cast; rfl
    have l : (luc (i+4):ZMod m)=luc (i+3)+luc (i+2) := by change ((luc (i+3)+luc (i+2):ℕ):ZMod m)=_; push_cast; rfl
    change (luc (i+3):ZMod m)=F (i+1)+3*F (i+2) ∧ (luc (i+4):ZMod m)=3*F (i+1)+4*F (i+2)
    rw [l,ih.1,ih.2,f]
    constructor <;> ring

def Fibonacci (m t : ℕ) := From (fun n => (F n:ZMod m)) 0 t

theorem iff_fib {m : ℕ} (hm : Nat.Coprime 5 m) (t : ℕ) : Lucas m t ↔ Fibonacci m t := by
  constructor
  · intro hl n _
    have a:=hl (n+2) (by omega); have b:=hl (n+3) (by omega)
    change (luc (n+2+t):ZMod m)=luc (n+2) at a
    change (luc (n+3+t):ZMod m)=luc (n+3) at b
    rw [show n+2+t=n+t+2 by omega,(bridge m _).1,(bridge m _).1] at a
    rw [show n+3+t=n+t+3 by omega,(bridge m _).2,(bridge m _).2] at b
    have eq : (5:ZMod m)*F (n+t)=5*F n := by linear_combination 3*b-4*a
    obtain ⟨u,hu⟩:IsUnit (5:ZMod m):=by simpa using (ZMod.isUnit_iff_coprime 5 m).mpr hm
    rw [←hu] at eq
    simpa [←mul_assoc] using congrArg (fun x : ZMod m => (↑(u⁻¹):ZMod m)*x) eq
  · intro hf n hn
    let k:=n-2
    have e : n=k+2 := by dsimp [k];omega
    have a:=hf k (Nat.zero_le _)
    have b:=hf (k+1) (Nat.zero_le _)
    change (F (k+t):ZMod m)=F k at a
    change (F (k+1+t):ZMod m)=F (k+1) at b
    change (luc (n+t):ZMod m)=luc n
    rw [e,show k+2+t=k+t+2 by omega,(bridge m _).1,(bridge m _).1,a,show k+t+1=k+1+t by omega,b]

theorem source {m : ℕ} (hm : 1<m) (hc : Nat.Coprime 5 m) (N t : ℕ) :
    FinitePeriod.Tail m N t ↔ t=0 ∨ (5≤N ∧ ∃s,t=6*s ∧ Fibonacci m (2*s)) := by
  simp only [LucasPeriods.characterize hm,iff_fib hc]

theorem pisano {m : ℕ} (hm : 1<m) (hc : Nat.Coprime 5 m) :
    0<LucasLeast.L hm ∧ ∀t, Fibonacci m t ↔ LucasLeast.L hm∣t :=
  ⟨(LucasLeast.least_spec hm).1,fun t => (iff_fib hc t).symm.trans (LucasLeast.lucas_iff hm t)⟩
end PisanoSource
#print axioms PisanoSource.source
#print axioms PisanoSource.pisano
