import SwarmProofs.SternDyadic

/-! Bruce Reznick conjectured that the same number of entries of Stern's sequence
in [0, 2^r) are divisible by 22 and by 27 for every r. See the paragraph after
(15) in https://cs.uwaterloo.ca/journals/JIS/VOL11/Reznick/reznick4.pdf.

A pair (a,b) of consecutive terms has children (a,a+b) and (a+b,b).
The tables color the residue pairs for the moduli in (15) and its conjecture with a common set of
colors. Each color determines whether the first residue is zero and the unordered
pair of child colors. The kernel checks every table entry against these rules.
Starting with the first-residue-zero test and repeatedly splitting colors
by their previous color and unordered child colors yields the tables below. -/

namespace SternResidues
open SternDyadic

/-- Number of indices i < N for which d divides Stern's s(i), including i = 0. -/
def count (d : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => count d n + (if stern n % d = 0 then 1 else 0)

private def blockCount (d : Nat) : Nat → Nat → Nat
  | 0, n => if stern n % d = 0 then 1 else 0
  | r+1, n => blockCount d r (2*n) + blockCount d r (2*n+1)

private theorem count_block (d r n : Nat) :
    count d (2^r*n) + blockCount d r n = count d (2^r*(n+1)) := by
  induction r generalizing n with
  | zero => simp [blockCount, count]
  | succ r ih =>
    have hl := ih (2*n)
    have hr := ih (2*n+1)
    rw [Nat.pow_succ, Nat.mul_assoc, show 2^r * 2 * (n+1) = 2^r * (2*n+1+1) by grind,
      blockCount, ← Nat.add_assoc, hl, hr]

private def colors22 : Array Nat := #[
  0, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1,
  4, 5, 6, 7, 8, 9, 10, 11, 7, 9, 12, 13, 14, 10, 11, 7, 9, 10, 8, 11, 15, 16,
  17, 6, 18, 7, 19, 8, 20, 9, 20, 12, 21, 13, 19, 14, 20, 10, 20, 8, 21, 11, 22, 15,
  4, 7, 7, 5, 9, 9, 6, 10, 12, 7, 8, 13, 8, 11, 14, 9, 15, 10, 10, 16, 11, 11,
  17, 8, 19, 9, 18, 11, 20, 12, 19, 15, 20, 13, 20, 6, 21, 14, 20, 7, 22, 10, 21, 8,
  4, 9, 8, 9, 11, 5, 12, 11, 10, 7, 6, 13, 15, 11, 9, 7, 14, 16, 7, 10, 8, 10,
  17, 10, 20, 6, 20, 12, 18, 8, 21, 7, 21, 13, 19, 11, 19, 8, 22, 14, 20, 15, 20, 9,
  4, 11, 9, 10, 12, 11, 8, 5, 15, 10, 11, 13, 7, 9, 6, 16, 8, 7, 14, 9, 10, 7,
  17, 7, 20, 12, 19, 10, 21, 15, 18, 8, 20, 13, 20, 8, 22, 6, 19, 9, 21, 14, 20, 11,
  4, 9, 12, 7, 15, 7, 7, 10, 8, 5, 10, 13, 9, 16, 8, 9, 11, 11, 6, 11, 14, 10,
  17, 12, 21, 8, 20, 6, 21, 11, 20, 10, 18, 13, 22, 9, 20, 7, 19, 15, 20, 8, 19, 14,
  23, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 24, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
  17, 14, 19, 8, 20, 15, 19, 7, 20, 9, 22, 13, 18, 10, 20, 11, 21, 6, 20, 8, 21, 12,
  4, 10, 14, 11, 6, 11, 11, 9, 8, 16, 9, 13, 10, 5, 8, 10, 7, 7, 15, 7, 12, 9,
  17, 11, 20, 14, 21, 9, 19, 6, 22, 8, 20, 13, 20, 8, 18, 15, 21, 10, 19, 12, 20, 7,
  4, 7, 10, 9, 14, 7, 8, 16, 6, 9, 7, 13, 11, 10, 15, 5, 8, 11, 12, 10, 9, 11,
  17, 9, 20, 15, 20, 14, 22, 8, 19, 11, 19, 13, 21, 7, 21, 8, 18, 12, 20, 6, 20, 10,
  4, 10, 8, 10, 7, 16, 14, 7, 9, 11, 15, 13, 6, 7, 10, 11, 12, 5, 11, 9, 8, 9,
  17, 8, 21, 10, 22, 7, 20, 14, 21, 6, 20, 13, 20, 15, 19, 12, 20, 11, 18, 9, 19, 8,
  4, 11, 11, 16, 10, 10, 15, 9, 14, 11, 8, 13, 8, 7, 12, 10, 6, 9, 9, 5, 7, 7,
  17, 15, 22, 11, 21, 8, 20, 10, 20, 14, 19, 13, 21, 12, 20, 9, 20, 8, 19, 7, 18, 6,
  4, 16, 15, 11, 8, 10, 9, 7, 11, 10, 14, 13, 12, 9, 7, 11, 10, 9, 8, 7, 6, 5]

private def colors27 : Array Nat := #[
  0, 1, 1, 2, 1, 1, 2, 1, 1, 25, 1, 1, 2, 1, 1, 2, 1, 1, 25, 1, 1, 2, 1, 1, 2, 1, 1,
  4, 5, 6, 7, 9, 10, 8, 9, 12, 13, 14, 10, 11, 15, 6, 7, 9, 12, 13, 14, 10, 8, 9, 10, 11, 15, 16,
  4, 6, 5, 7, 6, 9, 7, 12, 9, 13, 10, 14, 8, 10, 9, 8, 12, 9, 13, 10, 14, 11, 10, 15, 11, 16, 15,
  17, 7, 7, 18, 8, 8, 19, 11, 11, 20, 7, 7, 21, 8, 8, 19, 11, 11, 20, 7, 7, 21, 8, 8, 22, 11, 11,
  4, 9, 6, 8, 5, 12, 7, 9, 6, 13, 9, 10, 7, 14, 12, 11, 9, 10, 13, 15, 10, 11, 14, 16, 8, 15, 10,
  4, 10, 9, 8, 12, 5, 11, 10, 9, 13, 6, 15, 11, 12, 14, 7, 6, 15, 13, 10, 9, 7, 16, 14, 8, 10, 9,
  17, 8, 7, 19, 7, 11, 18, 11, 8, 20, 8, 7, 19, 7, 11, 21, 11, 8, 20, 8, 7, 22, 7, 11, 21, 11, 8,
  4, 9, 12, 11, 9, 10, 11, 5, 10, 13, 15, 12, 8, 15, 6, 8, 14, 6, 13, 9, 16, 7, 9, 10, 7, 14, 10,
  4, 12, 9, 11, 6, 9, 8, 10, 5, 13, 12, 15, 7, 10, 9, 11, 6, 14, 13, 16, 9, 8, 10, 15, 7, 10, 14,
  26, 13, 13, 20, 13, 13, 20, 13, 13, 27, 13, 13, 20, 13, 13, 20, 13, 13, 28, 13, 13, 20, 13, 13, 20, 13, 13,
  4, 14, 10, 7, 9, 6, 8, 15, 12, 13, 5, 10, 11, 9, 10, 7, 9, 16, 13, 14, 6, 8, 15, 10, 11, 9, 12,
  4, 10, 14, 7, 10, 15, 7, 12, 15, 13, 10, 5, 8, 10, 9, 8, 16, 9, 13, 6, 14, 11, 6, 9, 11, 12, 9,
  17, 11, 8, 21, 7, 11, 19, 8, 7, 20, 11, 8, 18, 7, 11, 22, 8, 7, 20, 11, 8, 21, 7, 11, 19, 8, 7,
  4, 15, 10, 8, 14, 12, 7, 15, 10, 13, 9, 10, 7, 5, 16, 11, 9, 10, 13, 9, 6, 11, 14, 12, 8, 9, 6,
  4, 6, 9, 8, 12, 14, 11, 6, 9, 13, 10, 9, 11, 16, 5, 7, 10, 9, 13, 10, 15, 7, 12, 14, 8, 10, 15,
  17, 7, 8, 19, 11, 7, 21, 8, 11, 20, 7, 8, 22, 11, 7, 18, 8, 11, 20, 7, 8, 19, 11, 7, 21, 8, 11,
  4, 9, 12, 11, 9, 6, 11, 14, 6, 13, 9, 16, 8, 9, 10, 8, 5, 10, 13, 15, 12, 7, 15, 10, 7, 14, 10,
  4, 12, 9, 11, 10, 15, 8, 6, 14, 13, 16, 9, 7, 10, 9, 11, 10, 5, 13, 12, 15, 8, 6, 9, 7, 10, 14,
  26, 13, 13, 20, 13, 13, 20, 13, 13, 28, 13, 13, 20, 13, 13, 20, 13, 13, 27, 13, 13, 20, 13, 13, 20, 13, 13,
  4, 14, 10, 7, 15, 10, 8, 9, 16, 13, 14, 6, 11, 9, 10, 7, 15, 12, 13, 5, 10, 8, 9, 6, 11, 9, 12,
  4, 10, 14, 7, 10, 9, 7, 16, 9, 13, 6, 14, 8, 6, 15, 8, 12, 15, 13, 10, 5, 11, 10, 9, 11, 12, 9,
  17, 8, 11, 21, 11, 7, 22, 7, 8, 20, 8, 11, 21, 11, 7, 19, 7, 8, 20, 8, 11, 18, 11, 7, 19, 7, 8,
  4, 9, 10, 8, 14, 16, 7, 9, 10, 13, 15, 6, 7, 14, 12, 11, 15, 6, 13, 9, 10, 11, 5, 12, 8, 9, 10,
  4, 10, 15, 8, 16, 14, 11, 10, 15, 13, 10, 9, 11, 12, 14, 7, 10, 9, 13, 6, 9, 7, 12, 5, 8, 6, 9,
  17, 11, 11, 22, 8, 8, 21, 7, 7, 20, 11, 11, 19, 8, 8, 21, 7, 7, 20, 11, 11, 19, 8, 8, 18, 7, 7,
  4, 15, 16, 11, 15, 10, 11, 14, 10, 13, 9, 12, 8, 9, 10, 8, 14, 10, 13, 9, 12, 7, 9, 6, 7, 5, 6,
  4, 16, 15, 11, 10, 9, 8, 10, 14, 13, 12, 9, 7, 6, 15, 11, 10, 14, 13, 12, 9, 8, 10, 9, 7, 6, 5]

private def colors4 : Array Nat := #[
  0, 29, 3, 29,
  30, 31, 32, 33,
  23, 32, 24, 32,
  30, 33, 32, 31]

private def colors5 : Array Nat := #[
  0, 29, 29, 29, 29,
  30, 31, 32, 32, 33,
  30, 32, 31, 33, 32,
  30, 32, 33, 31, 32,
  30, 33, 32, 32, 31]

private def colors6 : Array Nat := #[
  0, 2, 25, 3, 25, 2,
  17, 18, 19, 20, 21, 22,
  26, 19, 27, 20, 28, 21,
  23, 20, 20, 24, 20, 20,
  26, 21, 28, 20, 27, 19,
  17, 22, 21, 20, 19, 18]

private def colors9 : Array Nat := #[
  0, 2, 2, 25, 2, 2, 25, 2, 2,
  17, 18, 19, 20, 21, 19, 20, 21, 22,
  17, 19, 18, 20, 19, 21, 20, 22, 21,
  26, 20, 20, 27, 20, 20, 28, 20, 20,
  17, 21, 19, 20, 18, 22, 20, 21, 19,
  17, 19, 21, 20, 22, 18, 20, 19, 21,
  26, 20, 20, 28, 20, 20, 27, 20, 20,
  17, 21, 22, 20, 21, 19, 20, 18, 19,
  17, 22, 21, 20, 19, 21, 20, 19, 18]

private def colors11 : Array Nat := #[
  0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  17, 18, 19, 20, 20, 21, 19, 20, 20, 21, 22,
  17, 19, 18, 20, 19, 20, 20, 21, 20, 22, 21,
  17, 20, 20, 18, 21, 21, 19, 19, 22, 20, 20,
  17, 20, 19, 21, 18, 20, 20, 22, 19, 21, 20,
  17, 21, 20, 21, 20, 18, 22, 20, 19, 20, 19,
  17, 19, 20, 19, 20, 22, 18, 20, 21, 20, 21,
  17, 20, 21, 19, 22, 20, 20, 18, 21, 19, 20,
  17, 20, 20, 22, 19, 19, 21, 21, 18, 20, 20,
  17, 21, 22, 20, 21, 20, 20, 19, 20, 18, 19,
  17, 22, 21, 20, 20, 19, 21, 20, 20, 19, 18]

-- A color is accepting when the first component of its residue pairs is zero.
private def accepts (k : Nat) : Bool := k == 0 || k == 1 || k == 2 || k == 3 || k == 25 || k == 29

private def children : Array (Nat × Nat) := #[
  (0, 0), (1, 5), (2, 18), (3, 24), (4, 5), (6, 6),
  (7, 7), (8, 9), (9, 11), (10, 12), (8, 11), (7, 15),
  (13, 13), (13, 14), (10, 10), (6, 16), (1, 4), (17, 18),
  (19, 19), (20, 20), (20, 21), (19, 22), (2, 17), (23, 24),
  (3, 23), (25, 27), (26, 27), (28, 28), (25, 26),
  (29, 31), (30, 31), (32, 32), (32, 33), (29, 30)]

private def color (colors : Array Nat) (d a b : Nat) : Nat :=
  (colors[a*d + b]?).getD 0

private def valid (colors : Array Nat) (d : Nat) (a b : Fin d) : Prop :=
  let k := color colors d a b
  let s := (a.val + b.val) % d
  let left := color colors d a s
  let right := color colors d s b
  let pair := (children[k]?).getD (0, 0)
  (accepts k = true ↔ a.val = 0) ∧
    ((left, right) = pair ∨ (right, left) = pair)

private instance (colors : Array Nat) (d : Nat) (a b : Fin d) :
    Decidable (valid colors d a b) := by unfold valid; infer_instance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem valid22 : ∀ a b : Fin 22, valid colors22 22 a b := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem valid27 : ∀ a b : Fin 27, valid colors27 27 a b := by decide

private theorem valid4 : ∀ a b : Fin 4, valid colors4 4 a b := by decide

private theorem valid5 : ∀ a b : Fin 5, valid colors5 5 a b := by decide

private theorem valid6 : ∀ a b : Fin 6, valid colors6 6 a b := by decide

private theorem valid9 : ∀ a b : Fin 9, valid colors9 9 a b := by decide

set_option maxRecDepth 10000 in
private theorem valid11 : ∀ a b : Fin 11, valid colors11 11 a b := by decide

private def weight : Nat → Nat → Nat
  | 0, k => if accepts k then 1 else 0
  | r+1, k =>
    let p := (children[k]?).getD (0, 0)
    weight r p.1 + weight r p.2

private theorem reads_color (d : Nat) (hd : 0 < d) (colors : Array Nat)
    (checked : ∀ a b : Fin d, valid colors d a b) (r n : Nat) :
    blockCount d r n = weight r (color colors d (stern n % d) (stern (n+1) % d)) := by
  induction r generalizing n with
  | zero =>
    have leaf := (checked ⟨_, Nat.mod_lt (stern n) hd⟩ ⟨_, Nat.mod_lt (stern (n+1)) hd⟩).1
    change (accepts (color colors d (stern n % d) (stern (n+1) % d)) = true ↔
      stern n % d = 0) at leaf
    simp only [blockCount, weight, leaf]
  | succ r ih =>
    let a := stern n % d
    let b := stern (n+1) % d
    have step := (checked ⟨a, Nat.mod_lt _ hd⟩ ⟨b, Nat.mod_lt _ hd⟩).2
    rw [blockCount, ih (2*n), ih (2*n+1)]
    simp only [stern_even, stern_odd, show 2*n+1+1 = 2*(n+1) by omega, stern_even]
    rw [Nat.add_mod (stern n) (stern (n+1)) d]
    change weight r (color colors d a ((a+b)%d)) + weight r (color colors d ((a+b)%d) b) =
      weight (r+1) (color colors d a b)
    simp only [weight]
    rcases step with h | h
    · rw [← h]
    · rw [← h, Nat.add_comm]

private theorem same_root (d e : Nat) (hd : 1 < d) (he : 1 < e)
    (cd ce : Array Nat) (vd : ∀ a b : Fin d, valid cd d a b)
    (ve : ∀ a b : Fin e, valid ce e a b)
    (root : color cd d 0 1 = color ce e 0 1) (r : Nat) :
    count d (2^r) = count e (2^r) := by
  have left := count_block d r 0
  have right := count_block e r 0
  simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one, count] at left right
  rw [← left, ← right, reads_color d (by omega) cd vd, reads_color e (by omega) ce ve]
  simp only [Nat.zero_add, stern_zero, stern_one, Nat.zero_mod,
    Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt he, root]

set_option maxRecDepth 10000 in
/-- Reznick's divisibility-count conjecture, for every dyadic prefix. -/
theorem reznick (r : Nat) : count 22 (2^r) = count 27 (2^r) :=
  same_root 22 27 (by decide) (by decide) colors22 colors27 valid22 valid27 (by decide) r

set_option maxRecDepth 10000 in
/-- The moduli 4 and 5 in Reznick's equation (15). -/
theorem four_five (r : Nat) : count 4 (2^r) = count 5 (2^r) :=
  same_root 4 5 (by decide) (by decide) colors4 colors5 valid4 valid5 (by decide) r

set_option maxRecDepth 10000 in
/-- The moduli 6 and 9 in Reznick's equation (15). -/
theorem six_nine (r : Nat) : count 6 (2^r) = count 9 (2^r) :=
  same_root 6 9 (by decide) (by decide) colors6 colors9 valid6 valid9 (by decide) r

set_option maxRecDepth 10000 in
/-- The moduli 6 and 11 in Reznick's equation (15). -/
theorem six_eleven (r : Nat) : count 6 (2^r) = count 11 (2^r) :=
  same_root 6 11 (by decide) (by decide) colors6 colors11 valid6 valid11 (by decide) r

end SternResidues
/-- info: 'SternResidues.reznick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SternResidues.reznick

/-- info: 'SternResidues.four_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SternResidues.four_five

/-- info: 'SternResidues.six_nine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SternResidues.six_nine

/-- info: 'SternResidues.six_eleven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SternResidues.six_eleven
