import CeilingRows
import LeastCarry
namespace CeilingWythoff
open LeastCarry Nat

def lift (d : ℕ) (xs : List ℕ) := xs.map (·+d)

private theorem liftSpaced (d s : ℕ) (xs : List ℕ) (h : Spaced s xs) :
    Spaced (s+d) (lift d xs) := by
  induction xs generalizing s with
  | nil => trivial
  | cons a xs ih =>
    refine ⟨by change s+d≤a+d; have := h.1; omega,?_⟩
    simpa only [show a+2+d=a+d+2 by omega] using ih (a+2) h.2

private theorem lowerSpaced (d s : ℕ) (xs : List ℕ) (h : Spaced (s+d) xs) :
    ∃ys, Spaced s ys ∧ lift d ys=xs := by
  induction xs generalizing s with
  | nil => exact ⟨[],trivial,rfl⟩
  | cons a xs ih =>
    have ha := h.1
    obtain ⟨ys,hy,he⟩ := ih (a-d+2) (by simpa only [show a-d+2+d=a+2 by omega] using h.2)
    exact ⟨(a-d)::ys,⟨by omega,hy⟩,by simp [lift] at he ⊢; exact ⟨by omega,he⟩⟩

private theorem pad (k s : ℕ) (bs : List Bool) :
    value (List.replicate k false ++ bs) s = value bs (s+k) := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ,List.cons_append]
    change 0+value (List.replicate k false ++ bs) (s+1) = _
    rw [Nat.zero_add,ih,show s+1+k=s+(k+1) by omega]

/-- Finite word for a legal list of indices, valid after any uniform shift. -/
private theorem pack (s : ℕ) (xs : List ℕ) (h : Spaced s xs) :
    ∃bs : List Bool, ∀d:ℕ, value bs (s+d)=weight (lift d xs) := by
  induction xs generalizing s with
  | nil => exact ⟨[],fun _ => rfl⟩
  | cons a xs ih =>
    have h1 := h.1
    obtain ⟨bs,hb⟩ := ih (a+2) h.2
    refine ⟨List.replicate (a-s) false ++ true::false::bs,fun d => ?_⟩
    rw [pad,show s+d+(a-s)=a+d by omega]
    change fib (a+d)+(0+value bs (a+d+1+1))=weight ((a+d)::lift d xs)
    rw [weight_cons,Nat.zero_add,show a+d+1+1=a+2+d by omega,hb]

def hasColumn (n k : ℕ) : Prop := ∃r:ℕ, 1≤r ∧ entry r k=(n:ℤ)

theorem column (x k : ℕ) : hasColumn x k ↔
    ∃xs, Spaced (k+3) xs ∧ x=2*fib (k+1)+weight xs := by
  constructor
  · rintro ⟨r,hr,e⟩
    let ys := LeastCarry.digits (r-1)
    obtain ⟨bs,hb⟩ := pack 2 ys (digits_valid _)
    have v : value bs 2=r-1 := by
      have h := hb 0
      simpa [lift,ys,digits_weight] using h
    have vr : value bs 2+1=r := by omega
    have src := sourceDigital bs k
    rw [vr,e,show 2+k+1=2+(k+1) by omega,hb] at src
    refine ⟨lift (k+1) ys,?_,?_⟩
    · simpa only [show 2+(k+1)=k+3 by omega] using liftSpaced (k+1) 2 ys (digits_valid _)
    · exact_mod_cast src
  · rintro ⟨xs,h,rfl⟩
    obtain ⟨ys,hy,he⟩ := lowerSpaced (k+1) 2 xs (by simpa only [show 2+(k+1)=k+3 by omega] using h)
    obtain ⟨bs,hb⟩ := pack 2 ys hy
    refine ⟨value bs 2+1,by omega,?_⟩
    rw [sourceDigital,show 2+k+1=2+(k+1) by omega,hb,he]

theorem columnOne (x : ℕ) : hasColumn x 1 ↔ ∃t ys, LeastCarry.digits x=(3+2*t)::ys :=
  (column x 1).trans (LeastCarry.first x)
theorem columnTwo (x : ℕ) : hasColumn x 2 ↔ ∃t ys, LeastCarry.digits x=2::(4+2*t)::ys :=
  (column x 2).trans (LeastCarry.second x)
theorem columnHigh (x r : ℕ) (hr : 2≤r) :
    hasColumn x (r+1) ↔ ∃t ys, LeastCarry.digits x=r::(r+3+2*t)::ys :=
  (column x (r+1)).trans (LeastCarry.higher r x hr)

end CeilingWythoff
#print axioms CeilingWythoff.columnOne
#print axioms CeilingWythoff.columnTwo
#print axioms CeilingWythoff.columnHigh
