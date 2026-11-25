import SwarmProofs.SternResidues

/-! Reznick's classification of equal dyadic divisibility counts for moduli up to
128 (the paragraph following equation (15) in
https://cs.uwaterloo.ca/journals/JIS/VOL11/Reznick/reznick4.pdf).
Four depths distinguish every pair outside the three exceptional groups. -/

namespace SternClassification
open SternDyadic SternResidues

/-- The five ordered pairs obtained by choosing two increasing elements from
{4,5}, {6,9,11}, or {22,27}. -/
def exceptional (d e : Nat) : Prop :=
  (d = 4 ∧ e = 5) ∨ (d = 6 ∧ e = 9) ∨ (d = 6 ∧ e = 11) ∨
    (d = 9 ∧ e = 11) ∨ (d = 22 ∧ e = 27)

private instance (d e : Nat) : Decidable (exceptional d e) := by
  unfold exceptional
  infer_instance

/-- Count multiples by descending from a pair of neighboring Stern values. -/
private def tree (d : Nat) : Nat → Nat → Nat → Nat
  | 0, a, _ => if a % d = 0 then 1 else 0
  | r+1, a, b => tree d r a (a+b) + tree d r (a+b) b

private theorem count_tree (d r n : Nat) :
    count d (2^r*n) + tree d r (stern n) (stern (n+1)) = count d (2^r*(n+1)) := by
  induction r generalizing n with
  | zero => simp [tree, count]
  | succ r ih =>
    have hl := ih (2*n)
    have hr := ih (2*n+1)
    simp only [stern_even, stern_odd, show 2*n+1+1 = 2*(n+1) by omega] at hl hr
    simp only [Nat.pow_succ, Nat.mul_assoc]
    rw [tree, ← Nat.add_assoc, hl, hr]

private theorem from_root (d r : Nat) : tree d r 0 1 = count d (2^r) := by
  simpa only [Nat.mul_zero, Nat.zero_add, count, Nat.mul_one, stern_zero, stern_one]
    using count_tree d r 0

-- Equality at the four depths implies equality of this weighted sum.
-- The certificate checks directly that its only collisions are exceptional.
private def fingerprint (d : Nat) : Nat :=
  tree d 10 0 1 + 3 * (tree d 12 0 1 + 3 * (tree d 13 0 1 + 3 * tree d 14 0 1))

-- The first array entry is for modulus 1 and the last is for modulus 128.
private def values : Array Nat := #[
  529408, 176493, 132562, 87456, 87456, 43464, 67444, 42982,
  43464, 28828, 43464, 21928, 36532, 23336, 22458, 22132,
  28256, 13816, 26124, 14758, 17946, 15716, 22888, 11154,
  17756, 12700, 15716, 11864, 19212, 6700, 16596, 11082,
  11814, 9028, 12384, 7104, 15012, 8872, 9134, 7144,
  12258, 5374, 13248, 7440, 6952, 7092, 12164, 5476,
  10652, 5604, 7182, 6290, 10718, 4948, 6772, 5134,
  6078, 6438, 9672, 3440, 9132, 5300, 5474, 5712,
  5722, 3986, 8924, 4454, 5744, 3852, 8472, 3466,
  8052, 4530, 4106, 4544, 5740, 2914, 6968, 3276,
  5588, 3898, 6616, 2470, 4798, 4108, 4468, 3424,
  6930, 1642, 4828, 3124, 3604, 4060, 4306, 2224,
  5608, 3820, 3370, 2764, 5314, 1702, 5344, 3334,
  3328, 3184, 4732, 1984, 4912, 2044, 4480, 2110,
  4756, 1438, 3058, 3004, 2398, 2716, 3568, 1534,
  4384, 2170, 2596, 2104, 3064, 1036, 4888, 2452]

private def lookup (i : Nat) : Nat := (values[i]?).getD 0

private def checked (offset : Nat) : Prop :=
  ∀ j : Fin 8, fingerprint (offset+j.val+1) = lookup (offset+j.val)

private instance (offset : Nat) : Decidable (checked offset) := by
  unfold checked
  infer_instance

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

-- Small independent chunks bound the memory required by kernel reduction.
private theorem check0 : checked 0 := by decide +kernel
private theorem check1 : checked 8 := by decide +kernel
private theorem check2 : checked 16 := by decide +kernel
private theorem check3 : checked 24 := by decide +kernel
private theorem check4 : checked 32 := by decide +kernel
private theorem check5 : checked 40 := by decide +kernel
private theorem check6 : checked 48 := by decide +kernel
private theorem check7 : checked 56 := by decide +kernel
private theorem check8 : checked 64 := by decide +kernel
private theorem check9 : checked 72 := by decide +kernel
private theorem check10 : checked 80 := by decide +kernel
private theorem check11 : checked 88 := by decide +kernel
private theorem check12 : checked 96 := by decide +kernel
private theorem check13 : checked 104 := by decide +kernel
private theorem check14 : checked 112 := by decide +kernel
private theorem check15 : checked 120 := by decide +kernel

private theorem chunks (k : Fin 16) : checked (8*k.val) := by
  obtain ⟨n, hn⟩ := k
  match n with
  | 0 => exact check0
  | 1 => exact check1
  | 2 => exact check2
  | 3 => exact check3
  | 4 => exact check4
  | 5 => exact check5
  | 6 => exact check6
  | 7 => exact check7
  | 8 => exact check8
  | 9 => exact check9
  | 10 => exact check10
  | 11 => exact check11
  | 12 => exact check12
  | 13 => exact check13
  | 14 => exact check14
  | 15 => exact check15
  | n+16 => omega

private theorem checked_all (i : Fin 128) : fingerprint (i.val+1) = lookup i.val := by
  let k : Fin 16 := ⟨i.val/8, by have := i.isLt; omega⟩
  let j : Fin 8 := ⟨i.val%8, Nat.mod_lt _ (by decide)⟩
  have h : 8*k.val + j.val = i.val := by dsimp [k, j]; omega
  simpa only [h] using chunks k j

private theorem collisions :
    ∀ i j : Fin 128, i.val < j.val → lookup i.val = lookup j.val →
      exceptional (i.val+1) (j.val+1) := by decide +kernel

/-- Among the first 128 positive moduli, matching at these four dyadic depths
already forces one of Reznick's five exceptional pairs. -/
theorem four_depths (d e : Nat) (hd : 0 < d) (hlt : d < e) (he : e ≤ 128)
    (h10 : count d (2^10) = count e (2^10))
    (h12 : count d (2^12) = count e (2^12))
    (h13 : count d (2^13) = count e (2^13))
    (h14 : count d (2^14) = count e (2^14)) : exceptional d e := by
  let i : Fin 128 := ⟨d-1, by omega⟩
  let j : Fin 128 := ⟨e-1, by omega⟩
  have hi : i.val+1 = d := by dsimp [i]; omega
  have hj : j.val+1 = e := by dsimp [j]; omega
  have hij : i.val < j.val := by omega
  have h : fingerprint d = fingerprint e := by
    simp only [fingerprint, from_root, h10, h12, h13, h14]
  have hi' := checked_all i
  have hj' := checked_all j
  rw [hi] at hi'
  rw [hj] at hj'
  simpa only [hi, hj] using collisions i j hij (hi'.symm.trans (h.trans hj'))

/-- Exact classification of pairs with identical divisibility counts on
every dyadic prefix, throughout 1 ≤ d < e ≤ 128. -/
theorem classification (d e : Nat) (hd : 0 < d) (hlt : d < e) (he : e ≤ 128) :
    (∀ r : Nat, count d (2^r) = count e (2^r)) ↔ exceptional d e := by
  constructor
  · intro h
    exact four_depths d e hd hlt he (h 10) (h 12) (h 13) (h 14)
  · intro h r
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact four_five r
    · exact six_nine r
    · exact six_eleven r
    · exact (six_nine r).symm.trans (six_eleven r)
    · exact reznick r

end SternClassification

/-- info: 'SternClassification.four_depths' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SternClassification.four_depths

/-- info: 'SternClassification.classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SternClassification.classification
