import LucasZeros

namespace ZeroEnumeration
open LucasZeros

/-- The six offsets are read left to right within a pair of successive Lucas boundaries. -/
def offset : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | 2 => 5
  | 3 => 3
  | 4 => 2
  | _ => 1

def term (t j : ℕ) : ℕ := luc (2*t+6+(if j<2 then 0 else 1)) - offset j

/-- The argument is one-based; zero is a sentinel for the empty prefix. -/
def entry : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 5
  | 5 => 6
  | 6 => 8
  | 7 => 9
  | 8 => 10
  | n+9 => term (n/6) (n%6)

theorem six (t j : ℕ) (hj : j<6) : entry (6*t+j+9)=term t j := by
  change term ((6*t+j)/6) ((6*t+j)%6) = term t j
  congr 1 <;> omega

private theorem luc_every_other (k : ℕ) :
    luc (k+6)+luc (k+2)=3*luc (k+4) := by
  have a : luc (k+4)=luc (k+3)+luc (k+2) := rfl
  have b : luc (k+5)=luc (k+4)+luc (k+3) := rfl
  have c : luc (k+6)=luc (k+5)+luc (k+4) := rfl
  omega

private theorem offset_le (j : ℕ) : offset j ≤ 5 := by
  rcases j with _ | _ | _ | _ | _ | j <;> simp [offset]

private theorem block_rec (t j : ℕ) :
    term (t+3) j + 4*term (t+1) j = 4*term (t+2) j + term t j := by
  let k := 2*t+4+(if j<2 then 0 else 1)
  have e := luc_every_other k
  have e' := luc_every_other (k+2)
  have hi (i : ℕ) : offset j ≤ luc (k+2+i) := by
    have l := luc_mono.monotone (show 4≤k+2+i by dsimp [k]; omega)
    exact le_trans (offset_le j) (le_trans (by decide : 5≤luc 4) l)
  have h0 := hi 0
  have h1 := hi 2
  have h2 := hi 4
  have h3 := hi 6
  have re (i : ℕ) : 2*(t+i)+6+(if j<2 then 0 else 1)=k+(2+2*i) := by dsimp [k]; omega
  unfold term
  rw [re 3,re 1,re 2,show 2*t+6+(if j<2 then 0 else 1)=k+2 by dsimp [k]; omega]
  simp only [Nat.add_assoc, Nat.reduceAdd,Nat.reduceMul] at *
  omega

/-- The positive-index enumeration satisfies a constant-coefficient recurrence from n=5. -/
theorem sparse_recurrence (n : ℕ) (hn : 5≤n) :
    entry (n+18) + 4*entry (n+6) = 4*entry (n+12) + entry n := by
  by_cases h : n<9
  · have test : ∀ i : Fin 9, 5≤i.val →
        entry (i.val+18)+4*entry (i.val+6)=4*entry (i.val+12)+entry i.val := by decide
    exact test ⟨n,h⟩ hn
  · let t:= (n-9)/6
    let j:= (n-9)%6
    have hj : j<6 := Nat.mod_lt _ (by decide)
    have en : n=6*t+j+9 := by dsimp [t,j]; omega
    have atShift (a : ℕ) : entry (n+6*a)=term (t+a) j := by
      rw [show n+6*a=6*(t+a)+j+9 by omega, six _ _ hj]
    change entry (n+6*3)+4*entry (n+6*1)=4*entry (n+6*2)+entry n
    rw [atShift,atShift,atShift, en, six t j hj]
    exact block_rec _ _

end ZeroEnumeration
#print axioms ZeroEnumeration.sparse_recurrence
