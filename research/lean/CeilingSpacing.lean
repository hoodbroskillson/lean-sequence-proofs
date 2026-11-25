import CeilingBlocks
import Mathlib.Tactic.FinCases
namespace CeilingBlocks

def allowed (miss : Bool) (d : ℕ) : Prop :=
    (miss=true ∧ d=2) ∨ d=3 ∨ d=5 ∨ d=10 ∨ d=13
def step (miss : Bool) (x y : ℕ) := x<y ∧ allowed miss (y-x)
instance (miss : Bool) (x y : ℕ) : Decidable (step miss x y) := by unfold step allowed; infer_instance

private def first (miss : Bool) (s : S) :=
  if miss then (if s=0 then 1 else if s=1 ∨ s=3 then 0 else if s=4 then 3 else 11)
  else (if s=5 then 0 else if s=1 ∨ s=3 ∨ s=4 then 2 else 10)
private def back (miss : Bool) (k : ℕ) :=
  if k%2=0 then (if miss then 10 else 11) else (if miss then 2 else 3)

private def safe (miss : Bool) (k : ℕ) (s : S) : Prop :=
    (offsets miss k s).head?=some (first miss s) ∧
    (offsets miss k s).getLast?=some (Nat.fib (k+2)-back miss k) ∧
    back miss k≤Nat.fib (k+2) ∧ (offsets miss k s).Chain' (step miss)
private instance (miss : Bool) (k : ℕ) (s : S) : Decidable (safe miss k s) := by unfold safe; infer_instance

private def check (m : Bool) : List ℕ → Bool
  | a::b::xs => decide (step m a b) && check m (b::xs)
  | _ => true
private theorem checkIff (m : Bool) : ∀xs : List ℕ, check m xs=true ↔ xs.Chain' (step m)
  | [] => by simp [check]
  | [a] => by simp [check]
  | a::b::xs => by rw [check,List.chain'_cons,Bool.and_eq_true,decide_eq_true_eq,checkIff m (b::xs)]

set_option maxRecDepth 30000
set_option maxHeartbeats 1600000
private theorem bases : (∀m:Bool,∀s:S,safe m 7 s) ∧ (∀m:Bool,∀s:S,safe m 8 s) := by
  constructor <;> intro m s <;> cases m <;> fin_cases s <;> unfold safe <;> rw [←checkIff] <;> decide

private theorem lastMap (L : List ℕ) (v : ℕ) :
    (L.map (v+·)).getLast?=L.getLast?.map (v+·) := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons b bs => exact ih

private theorem boundary (m : Bool) (k : ℕ) (s : S) :
    allowed m (back m (k+1) + first m (push (k+3) s)) := by
  have parity : k%2=0 ∨ k%2=1 := by omega
  rcases parity with e|e
  · have p : (k+1)%2=1 := by omega
    have q : (k+3)%2=1 := by omega
    cases m <;> fin_cases s <;> simp [allowed,back,first,push,p,q]
  · have p : (k+1)%2=0 := by omega
    have q : (k+3)%2=0 := by omega
    cases m <;> fin_cases s <;> simp [allowed,back,first,push,p,q]

private theorem combine {m : Bool} {k : ℕ} {s : S} (hl : safe m (k+1) s)
    (hr : safe m k (push (k+3) s)) : safe m (k+2) s := by
  obtain ⟨hlf,hll,hlb,hlc⟩ := hl
  obtain ⟨hrf,hrl,hrb,hrc⟩ := hr
  let A:=offsets m (k+1) s
  let C:=offsets m k (push (k+3) s)
  let V:=Nat.fib (k+3)
  let U:=Nat.fib (k+2)
  have f : Nat.fib (k+2+2)=V+U := by dsimp [V,U]; rw [Nat.fib_add_two (n:=k+2),Nat.add_comm]
  have bl : back m (k+2)=back m k := by unfold back; rw [show (k+2)%2=k%2 by omega]
  have pos : 0<back m (k+1) := by unfold back; split <;> cases m <;> decide
  change A.head?=_ at hlf
  change A.getLast?=some (V-back m (k+1)) at hll
  change back m (k+1)≤V at hlb
  change C.head?=_ at hrf
  change C.getLast?=some (U-back m k) at hrl
  change back m k≤U at hrb
  have Apos : A≠[] := by intro e; rw [e] at hlf; contradiction
  have Cpos : C.map (V+·)≠[] := by intro e; have h : C=[] := List.map_eq_nil.mp e; rw [h] at hrf; contradiction
  change (A++C.map (V+·)).head?=_ ∧ (A++C.map (V+·)).getLast?=_ ∧ _ ∧ _
  refine ⟨?_,?_,?_,?_⟩
  · rw [List.head?_append_of_ne_nil _ Apos,hlf]
  · rw [List.getLast?_append_of_ne_nil _ Cpos,lastMap,hrl,bl,f,Option.map_some']
    congr 1; omega
  · rw [f,bl]; omega
  · apply List.Chain'.append hlc
    · apply List.chain'_map_of_chain' (V+·) _ hrc
      rintro x y ⟨lt,g⟩
      exact ⟨Nat.add_lt_add_left lt V,by simpa only [Nat.add_sub_add_left] using g⟩
    · intro x hx y hy
      change x∈A.getLast? at hx
      rw [hll] at hx
      change y∈(C.map (V+·)).head? at hy
      rw [List.head?_map,hrf] at hy
      simp at hx hy
      refine ⟨by omega,?_⟩
      rw [show y-x=back m (k+1)+first m (push (k+3) s) by omega]
      exact boundary m k s

private theorem large (n : ℕ) (m : Bool) (s : S) : safe m (n+7) s := by
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
    rcases n with _|_|n
    · exact bases.1 m s
    · exact bases.2 m s
    · exact combine (ih (n+1) (by omega) s) (ih n (by omega) _)

theorem steps (k : ℕ) (h : 7≤k) (m : Bool) (s : S) : (offsets m k s).Chain' (step m) := by
  have e := (large (k-7) m s).2.2.2
  simpa only [show k-7+7=k by omega] using e

end CeilingBlocks
#print axioms CeilingBlocks.steps
