import PhaseSix
import Batteries.Tactic.OpenPrivate

namespace SixPair
open CanonicalZeros LucasZeros ZeroEnumeration PhaseSix
open private PhaseSix.digit from PhaseSix

def difference (m q i : ℕ) : ZMod m :=
  (luc (i+4+2*q):ZMod m) - luc (i+4)

private theorem recurrence (m q i : ℕ) : difference m q (i+2)=difference m q (i+1)+difference m q i := by
  have h : luc ((i+2)+4+2*q)=luc ((i+1)+4+2*q)+luc (i+4+2*q) := by
    simp only [show i+2+4+2*q=(i+2*q+2)+4 by omega, show i+1+4+2*q=(i+2*q+2)+3 by omega,
      show i+4+2*q=(i+2*q+2)+2 by omega]
    rfl
  have h' : luc ((i+2)+4)=luc ((i+1)+4)+luc (i+4) := rfl
  simp only [difference,h,h',Nat.cast_add]
  ring

theorem pair (m q i : ℕ) : (difference m q i=0 ∧ difference m q (i+1)=0) ↔
    (difference m q 0=0 ∧ difference m q 1=0) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [←ih,recurrence]
    constructor
    · rintro ⟨a,b⟩
      exact ⟨by simpa [a] using b,a⟩
    · rintro ⟨a,b⟩
      exact ⟨b,by simp [a,b]⟩

private theorem phase {m q u i : ℕ} (hi : i<6) :
    ((a (6*u+i+9+6*q):ZMod m)=a (6*u+i+9)) ↔
      difference m q (2*u+2+(if i<2 then 0 else 1))=0 := by
  rw [source_entry _ (by omega),source_entry _ (by omega),
      show 6*u+i+9+6*q=6*(u+q)+i+9 by omega,PhaseSix.digit hi,PhaseSix.digit hi]
  simp only [difference,sub_eq_zero,sub_left_inj]
  generalize (if i<2 then 0 else 1 : ℕ)=j
  rw [show 2*(u+q)+6+j=2*u+2+j+4+2*q by omega,show 2*u+6+j=2*u+2+j+4 by omega]

theorem six_iff (m q : ℕ) : (∃N, Tail m N (6*q)) ↔
    (difference m q 0=0 ∧ difference m q 1=0) := by
  constructor
  · rintro ⟨N,h⟩
    apply (pair m q (2*N+2)).mp
    constructor
    · exact (phase (q:=q) (u:=N) (i:=0) (by decide)).mp (h _ (by omega))
    · exact (phase (q:=q) (u:=N) (i:=2) (by decide)).mp (h _ (by omega))
  · rintro h
    use 9
    intro n hn
    have idx : n=6*((n-9)/6)+(n-9)%6+9 := by omega
    have z := (phase (q:=q) (u:=(n-9)/6) (i:=(n-9)%6) (by omega)).mpr
      (((pair m q _).mpr h).1)
    simpa only [←idx] using z

end SixPair
#print axioms SixPair.six_iff
