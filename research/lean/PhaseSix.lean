import CanonicalZeros
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
namespace PhaseSix
open CanonicalZeros ZeroEnumeration LucasZeros

def Tail (m N t : ℕ) := ∀n,N≤n → (a (n+t):ZMod m)=(a n:ZMod m)

private def diff (m u i : ℕ) := (entry (6*u+i+10):ZMod m)-(entry (6*u+i+9):ZMod m)

private theorem digit {m u i : ℕ} (hi : i<6) :
    (entry (6*u+i+9):ZMod m) = luc (2*u+6+(if i<2 then 0 else 1)) -
      (offset i : ZMod m) := by
  rw [six _ _ hi,term,Nat.cast_sub]
  have l := luc_mono.monotone (show 6≤2*u+6+(if i<2 then 0 else 1) by omega)
  have ge : 5≤luc 6 := by decide
  have b : offset i ≤ 5 := by interval_cases i <;> decide
  exact b.trans (ge.trans l)

private theorem vals (m u : ℕ) :
    diff m u 0=1 ∧ diff m u 1=(luc (2*u+5):ZMod m)-4 ∧ diff m u 2=2 ∧
    diff m u 3=1 ∧ diff m u 4=1 ∧ diff m u 5=(luc (2*u+6):ZMod m)-1 := by
  have e : luc (2*u+7)=luc (2*u+6)+luc (2*u+5) := rfl
  have f : luc (2*u+8)=luc (2*u+7)+luc (2*u+6) := rfl
  have last : (entry (6*u+5+10):ZMod m)=(entry (6*(u+1)+0+9):ZMod m) := by congr 2
  unfold diff
  rw [last]
  have idx (i : ℕ) : 6*u+i+10=6*u+(i+1)+9 := by omega
  rw [idx 0,idx 1,idx 2,idx 3,idx 4]
  simp only [digit (m:=m) (by decide : 0<6),digit (m:=m) (by decide : 1<6),
    digit (m:=m) (by decide : 2<6),digit (m:=m) (by decide : 3<6),
    digit (m:=m) (by decide : 4<6),digit (m:=m) (by decide : 5<6)]
  norm_num only [offset, Nat.reduceLT,if_true,if_false,Nat.add_zero,Nat.cast_ofNat,
    show 2*(u+1)+6=2*u+8 by omega,show 2*u+6+1=2*u+7 by omega,f,e,Nat.cast_add]
  exact ⟨by ring,by ring,by ring,by ring,by ring,by ring⟩

private theorem move {m N t : ℕ} (h : Tail m N t) (u i v j : ℕ)
    (pos : N≤6*u+i+9) (eq : 6*u+i+9+t=6*v+j+9) : diff m u i=diff m v j := by
  have h1 := h (6*u+i+9) pos
  have h2 := h (6*u+i+10) (by omega)
  simp only [source_entry _ (by omega : 0<6*u+i+9+t),source_entry _ (by omega : 0<6*u+i+9),
    source_entry _ (by omega : 0<6*u+i+10+t),source_entry _ (by omega : 0<6*u+i+10)] at h1 h2
  rw [eq] at h1
  rw [show 6*u+i+10+t=6*v+j+10 by omega] at h2
  simp only [diff,h1,h2]

private theorem lrec (n : ℕ) : luc (n+8)+luc (n+4)=3*luc (n+6) := by
  have a : luc (n+8)=luc (n+7)+luc (n+6) := rfl
  have b : luc (n+7)=luc (n+6)+luc (n+5) := rfl
  have c : luc (n+6)=luc (n+5)+luc (n+4) := rfl
  omega

theorem divisible {m N t : ℕ} (hm : 2≤m) (h : Tail m N t) : 6∣t := by
  let k:=t/6
  letI : Fact (1<m) := ⟨hm⟩
  have bad : (2:ZMod m)≠1 := by
    intro v
    have o : (1:ZMod m)=0 := by linear_combination v
    exact one_ne_zero o
  obtain r|r|r|r|r|r : t%6=0 ∨ t%6=1 ∨ t%6=2 ∨ t%6=3 ∨ t%6=4 ∨ t%6=5 := by omega
  · exact Nat.dvd_of_mod_eq_zero r
  · have z:=move h N 2 (N+k) 3 (by omega) (by omega)
    exact False.elim (bad (by simpa [(vals m N).2.2.1,(vals m (N+k)).2.2.2.1] using z))
  · have z:=move h N 2 (N+k) 4 (by omega) (by omega)
    exact False.elim (bad (by simpa [(vals m N).2.2.1,(vals m (N+k)).2.2.2.2.1] using z))
  · have odd (u : ℕ) (hu : N≤u) : (luc (2*u+5):ZMod m)=5 := by
      have z:=move h u 1 (u+k) 4 (by omega) (by omega)
      rw [(vals _ _).2.1,(vals _ _).2.2.2.2.1] at z
      linear_combination z
    have even (u : ℕ) (hu : N≤u) : (luc (2*u+6):ZMod m)=3 := by
      have z:=move h u 5 (u+k+1) 2 (by omega) (by omega)
      rw [(vals _ _).2.2.2.2.2,(vals _ _).2.2.1] at z
      linear_combination z
    have vanished (x c : ℕ) (hx : 4≤x) (v : ∀u,N≤u → (luc (2*u+x):ZMod m)=c) :
        (c:ZMod m)=0 := by
      have z:=congrArg (fun n:ℕ => (n:ZMod m)) (lrec (2*N+x-4))
      rw [show 2*N+x-4+8=2*(N+2)+x by omega,show 2*N+x-4+6=2*(N+1)+x by omega,
          show 2*N+x-4+4=2*N+x by omega] at z
      push_cast at z
      rw [v _ (by omega),v _ le_rfl,v _ (by omega)] at z
      linear_combination -z
    have three:=vanished 6 3 (by decide) even
    have five:=vanished 5 5 (by decide) odd
    apply False.elim
    apply (one_ne_zero : (1:ZMod m)≠0)
    linear_combination 2*three-five
  · have z:=move h N 4 (N+k+1) 2 (by omega) (by omega)
    exact False.elim (bad (by simpa [(vals m N).2.2.2.2.1,(vals m (N+k+1)).2.2.1] using z.symm))
  · have z:=move h N 3 (N+k+1) 2 (by omega) (by omega)
    exact False.elim (bad (by simpa [(vals m N).2.2.2.1,(vals m (N+k+1)).2.2.1] using z.symm))

end PhaseSix
#print axioms PhaseSix.divisible
