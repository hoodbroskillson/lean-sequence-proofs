import Mathlib.Data.Nat.Fib.Zeckendorf
namespace LeastCarry
open Nat
/-- Legal Fibonacci indices in increasing order, with a lower bound on the first. -/
def Spaced : ℕ → List ℕ → Prop
  | _, [] => True
  | s, i::xs => s≤i ∧ Spaced (i+2) xs

def weight (xs : List ℕ) := (xs.map fib).sum
def digits (x : ℕ) := x.zeckendorf.reverse
@[simp] theorem weight_cons (a : ℕ) (xs : List ℕ) : weight (a::xs)=fib a+weight xs := by simp [weight]

private theorem chain (r : ℕ) (xs : List ℕ) :
    (r::xs).Chain' (fun a b => a+2≤b) ↔ Spaced (r+2) xs := by
  induction xs generalizing r with
  | nil => simp [Spaced]
  | cons a xs ih =>
    rw [List.chain'_cons']
    simp [Spaced,ih a]

theorem valid (xs : List ℕ) : xs.reverse.IsZeckendorfRep ↔ Spaced 2 xs := by
  unfold List.IsZeckendorfRep
  rw [← List.reverse_cons, List.chain'_reverse]
  exact chain 0 xs

theorem identify (xs : List ℕ) (h : Spaced 2 xs) : digits (weight xs)=xs := by
  have e := Nat.zeckendorf_sum_fib ((valid xs).mpr h)
  rw [List.map_reverse,List.sum_reverse] at e
  unfold digits weight
  rw [e,List.reverse_reverse]

theorem digits_valid (x : ℕ) : Spaced 2 (digits x) :=
  (valid _).mp (by simp only [digits,List.reverse_reverse,Nat.isZeckendorfRep_zeckendorf])
theorem digits_weight (x : ℕ) : weight (digits x)=x := by
  simp only [weight,digits,List.map_reverse,List.sum_reverse,Nat.sum_zeckendorf_fib]

/-- Adding F_r below a collection beginning at r+1 carries up in steps of two. -/
theorem carry (xs : List ℕ) (r : ℕ) (h : Spaced (r+1) xs) :
    ∃t ys, Spaced (r+2*t+2) ys ∧ fib r + weight xs = fib (r+2*t) + weight ys := by
  induction xs generalizing r with
  | nil => exact ⟨0,[],trivial,by simp⟩
  | cons i xs ih =>
    obtain ⟨hi,ht⟩ := h
    by_cases eq : i=r+1
    · subst i
      obtain ⟨t,ys,hs,e⟩ := ih (r+2) (by simpa only [show r+2+1=r+1+2 by omega] using ht)
      refine ⟨t+1,ys,?_,?_⟩
      · simpa only [show r+2*(t+1)+2=r+2+2*t+2 by omega] using hs
      · rw [weight_cons]
        rw [←Nat.add_assoc,←fib_add_two,e,show r+2*(t+1)=r+2+2*t by omega]
    · exact ⟨0,i::xs,⟨by omega,ht⟩,by simp⟩

/-- Every carry output of the allowed parity has a legal predecessor. -/
theorem uncarry (t r : ℕ) (ys : List ℕ) (h : Spaced (r+2*t+2) ys) :
    ∃xs, Spaced (r+1) xs ∧ fib r+weight xs=fib (r+2*t)+weight ys := by
  induction t generalizing r with
  | zero => exact ⟨ys,by cases ys with
                          | nil => trivial
                          | cons i zs => exact ⟨by have := h.1; omega,h.2⟩,by simp⟩
  | succ t ih =>
    obtain ⟨xs,hx,e⟩ := ih (r+2) (by simpa only [show r+2*(t+1)+2=r+2+2*t+2 by omega] using h)
    refine ⟨(r+1)::xs,⟨le_rfl,?_⟩,?_⟩
    · simpa only [show r+1+2=r+2+1 by omega] using hx
    · rw [weight_cons]
      rw [←Nat.add_assoc,←fib_add_two,e,show r+2*(t+1)=r+2+2*t by omega]

/-- The first ceiling column doubles F₂=1 and produces an odd least index. -/
theorem first (x : ℕ) : (∃xs, Spaced 4 xs ∧ x=2*fib 2+weight xs) ↔
    ∃t ys, digits x=(3+2*t)::ys := by
  constructor
  · rintro ⟨xs,h,rfl⟩
    obtain ⟨t,ys,hy,e⟩ := carry xs 3 h
    refine ⟨t,ys,?_⟩
    change digits (fib 3+weight xs)=_
    rw [e]
    simpa only [weight_cons] using identify ((3+2*t)::ys) ⟨by omega,hy⟩
  · rintro ⟨t,ys,e⟩
    have h := digits_valid x
    rw [e] at h
    obtain ⟨xs,hx,he⟩ := uncarry t 3 ys h.2
    refine ⟨xs,hx,?_⟩
    change x=fib 3+weight xs
    rw [he,←digits_weight x,e]
    simp only [weight_cons]

/-- F₃=2 carries to F₂ and an even second index at least 4. -/
theorem second (x : ℕ) : (∃xs, Spaced 5 xs ∧ x=2*fib 3+weight xs) ↔
    ∃t ys, digits x=2::(4+2*t)::ys := by
  constructor
  · rintro ⟨xs,h,rfl⟩
    obtain ⟨t,ys,hy,e⟩ := carry xs 4 h
    refine ⟨t,ys,?_⟩
    change digits ((fib 2+fib 4)+weight xs)=_
    rw [Nat.add_assoc,e]
    simpa only [weight_cons] using identify (2::(4+2*t)::ys) ⟨le_rfl,⟨by omega,hy⟩⟩
  · rintro ⟨t,ys,e⟩
    have h := digits_valid x
    rw [e] at h
    obtain ⟨xs,hx,he⟩ := uncarry t 4 ys h.2.2
    refine ⟨xs,hx,?_⟩
    change x=(fib 2+fib 4)+weight xs
    rw [Nat.add_assoc,he,←digits_weight x,e]
    simp only [weight_cons]

/-- All higher columns have a prescribed smallest index and an odd larger gap. -/
theorem higher (r x : ℕ) (hr : 2≤r) :
    (∃xs, Spaced (r+4) xs ∧ x=2*fib (r+2)+weight xs) ↔
    ∃t ys, digits x=r::(r+3+2*t)::ys := by
  have f : 2*fib (r+2)=fib r+fib (r+3) := by
    have a := @fib_add_two r
    have b : fib (r+3)=fib (r+1)+fib (r+2) := @fib_add_two (r+1)
    omega
  constructor
  · rintro ⟨xs,h,rfl⟩
    obtain ⟨t,ys,hy,e⟩ := carry xs (r+3) h
    refine ⟨t,ys,?_⟩
    rw [f,Nat.add_assoc,e]
    simpa only [weight_cons] using identify (r::(r+3+2*t)::ys) ⟨hr,⟨by omega,hy⟩⟩
  · rintro ⟨t,ys,e⟩
    have h := digits_valid x
    rw [e] at h
    obtain ⟨xs,hx,he⟩ := uncarry t (r+3) ys h.2.2
    refine ⟨xs,hx,?_⟩
    rw [f,Nat.add_assoc,he,←digits_weight x,e]
    simp only [weight_cons]
end LeastCarry
#print axioms LeastCarry.first
#print axioms LeastCarry.second
#print axioms LeastCarry.higher
