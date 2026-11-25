import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.List.Chain
namespace CeilingBlocks
/-- Codes for no higher digits, E, O, EE, EO, OE, OO, respectively. -/
abbrev S := Fin 7
def push (i : ℕ) (s : S) : S :=
  if i%2=0 then (if s=0 then 1 else if s=1 ∨ s=3 ∨ s=4 then 3 else 4)
  else (if s=0 then 2 else if s=1 ∨ s=3 ∨ s=4 then 5 else 6)
/-- The first flag is true for the missing-number language, false for duplicates. -/
def test (miss : Bool) (s : S) : Bool := if miss then s==1 || s==3 else s==5
def offsets (miss : Bool) : ℕ → S → List ℕ
  | 0,s => if test miss s then [0] else []
  | 1,s => (if test miss s then [0] else []) ++ (if miss && s==0 then [1] else [])
  | k+2,s => offsets miss (k+1) s ++ (offsets miss k (push (k+3) s)).map (Nat.fib (k+3)+·)
end CeilingBlocks
