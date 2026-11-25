import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime
namespace ExamplePrime
private theorem square0 : (2 : ZMod 433494437)^1 = 2 := by
  decide
private theorem square1 : (2 : ZMod 433494437)^2 = 4 := by
  decide
private theorem square2 : (2 : ZMod 433494437)^4 = 16 := by
  rw [show (4:ℕ)=2+2 by decide,pow_add,square1]
  decide
private theorem square3 : (2 : ZMod 433494437)^8 = 256 := by
  rw [show (8:ℕ)=4+4 by decide,pow_add,square2]
  decide
private theorem square4 : (2 : ZMod 433494437)^16 = 65536 := by
  rw [show (16:ℕ)=8+8 by decide,pow_add,square3]
  decide
private theorem square5 : (2 : ZMod 433494437)^32 = 393517363 := by
  rw [show (32:ℕ)=16+16 by decide,pow_add,square4]
  decide
private theorem square6 : (2 : ZMod 433494437)^64 = 337241391 := by
  rw [show (64:ℕ)=32+32 by decide,pow_add,square5]
  decide
private theorem square7 : (2 : ZMod 433494437)^128 = 121286435 := by
  rw [show (128:ℕ)=64+64 by decide,pow_add,square6]
  decide
private theorem square8 : (2 : ZMod 433494437)^256 = 115904642 := by
  rw [show (256:ℕ)=128+128 by decide,pow_add,square7]
  decide
private theorem square9 : (2 : ZMod 433494437)^512 = 74149666 := by
  rw [show (512:ℕ)=256+256 by decide,pow_add,square8]
  decide
private theorem square10 : (2 : ZMod 433494437)^1024 = 29532244 := by
  rw [show (1024:ℕ)=512+512 by decide,pow_add,square9]
  decide
private theorem square11 : (2 : ZMod 433494437)^2048 = 342447555 := by
  rw [show (2048:ℕ)=1024+1024 by decide,pow_add,square10]
  decide
private theorem square12 : (2 : ZMod 433494437)^4096 = 69867842 := by
  rw [show (4096:ℕ)=2048+2048 by decide,pow_add,square11]
  decide
private theorem square13 : (2 : ZMod 433494437)^8192 = 381834388 := by
  rw [show (8192:ℕ)=4096+4096 by decide,pow_add,square12]
  decide
private theorem square14 : (2 : ZMod 433494437)^16384 = 279174408 := by
  rw [show (16384:ℕ)=8192+8192 by decide,pow_add,square13]
  decide
private theorem square15 : (2 : ZMod 433494437)^32768 = 310860408 := by
  rw [show (32768:ℕ)=16384+16384 by decide,pow_add,square14]
  decide
private theorem square16 : (2 : ZMod 433494437)^65536 = 42924268 := by
  rw [show (65536:ℕ)=32768+32768 by decide,pow_add,square15]
  decide
private theorem square17 : (2 : ZMod 433494437)^131072 = 106899362 := by
  rw [show (131072:ℕ)=65536+65536 by decide,pow_add,square16]
  decide
private theorem square18 : (2 : ZMod 433494437)^262144 = 161874440 := by
  rw [show (262144:ℕ)=131072+131072 by decide,pow_add,square17]
  decide
private theorem square19 : (2 : ZMod 433494437)^524288 = 130639480 := by
  rw [show (524288:ℕ)=262144+262144 by decide,pow_add,square18]
  decide
private theorem square20 : (2 : ZMod 433494437)^1048576 = 350947022 := by
  rw [show (1048576:ℕ)=524288+524288 by decide,pow_add,square19]
  decide
private theorem square21 : (2 : ZMod 433494437)^2097152 = 76678823 := by
  rw [show (2097152:ℕ)=1048576+1048576 by decide,pow_add,square20]
  decide
private theorem square22 : (2 : ZMod 433494437)^4194304 = 356142572 := by
  rw [show (4194304:ℕ)=2097152+2097152 by decide,pow_add,square21]
  decide
private theorem square23 : (2 : ZMod 433494437)^8388608 = 150835792 := by
  rw [show (8388608:ℕ)=4194304+4194304 by decide,pow_add,square22]
  decide
private theorem square24 : (2 : ZMod 433494437)^16777216 = 382152227 := by
  rw [show (16777216:ℕ)=8388608+8388608 by decide,pow_add,square23]
  decide
private theorem square25 : (2 : ZMod 433494437)^33554432 = 77552784 := by
  rw [show (33554432:ℕ)=16777216+16777216 by decide,pow_add,square24]
  decide
private theorem square26 : (2 : ZMod 433494437)^67108864 = 271409371 := by
  rw [show (67108864:ℕ)=33554432+33554432 by decide,pow_add,square25]
  decide
private theorem square27 : (2 : ZMod 433494437)^134217728 = 233694251 := by
  rw [show (134217728:ℕ)=67108864+67108864 by decide,pow_add,square26]
  decide
private theorem square28 : (2 : ZMod 433494437)^268435456 = 33320148 := by
  rw [show (268435456:ℕ)=134217728+134217728 by decide,pow_add,square27]
  decide
private theorem eval0 : (2 : ZMod 433494437)^433494436  = 1 := by
  rw [show (433494436:ℕ)=4+32+128+256+2048+4096+32768+131072+262144+1048576+4194304+8388608+16777216+134217728+268435456 by decide]
  simp only [pow_add,square2,square5,square7,square8,square11,square12,square15,square17,square18,square20,square22,square23,square24,square27,square28]
  decide
private theorem eval1 : (2 : ZMod 433494437)^216747218  ≠ 1 := by
  rw [show (216747218:ℕ)=2+16+64+128+1024+2048+16384+65536+131072+524288+2097152+4194304+8388608+67108864+134217728 by decide]
  simp only [pow_add,square1,square4,square6,square7,square10,square11,square14,square16,square17,square19,square21,square22,square23,square26,square27]
  decide
private theorem eval2 : (2 : ZMod 433494437)^14948084  ≠ 1 := by
  rw [show (14948084:ℕ)=4+16+32+64+128+512+1024+4096+262144+2097152+4194304+8388608 by decide]
  simp only [pow_add,square2,square4,square5,square6,square7,square9,square10,square12,square18,square21,square22,square23]
  decide
private theorem eval3 : (2 : ZMod 433494437)^4870724  ≠ 1 := by
  rw [show (4870724:ℕ)=4+64+512+4096+16384+131072+524288+4194304 by decide]
  simp only [pow_add,square2,square6,square9,square12,square14,square17,square19,square22]
  decide
private theorem eval4 : (2 : ZMod 433494437)^2178364  ≠ 1 := by
  rw [show (2178364:ℕ)=4+8+16+32+256+1024+2048+4096+8192+65536+2097152 by decide]
  simp only [pow_add,square2,square3,square4,square5,square8,square10,square11,square12,square13,square16,square21]
  decide
private theorem eval5 : (2 : ZMod 433494437)^2054476  ≠ 1 := by
  rw [show (2054476:ℕ)=4+8+64+256+2048+4096+16384+65536+131072+262144+524288+1048576 by decide]
  simp only [pow_add,square2,square3,square6,square8,square11,square12,square14,square16,square17,square18,square19,square20]
  decide
theorem f43 : Nat.Prime 433494437 := by
  apply lucas_primality _ (2:ZMod 433494437) eval0
  intro q prime h
  have fac : 433494437-1 = (2*2*29*89*199*211:ℕ) := by decide
  rw [fac] at h
  simp only [prime.dvd_mul] at h
  rcases h with (((((h|h)|h)|h)|h)|h)
  · have eq := ((Nat.dvd_prime (by decide : Nat.Prime 2)).mp h).resolve_left prime.ne_one
    subst q
    exact eval1
  · have eq := ((Nat.dvd_prime (by decide : Nat.Prime 2)).mp h).resolve_left prime.ne_one
    subst q
    exact eval1
  · have eq := ((Nat.dvd_prime (by decide : Nat.Prime 29)).mp h).resolve_left prime.ne_one
    subst q
    exact eval2
  · have eq := ((Nat.dvd_prime (by decide : Nat.Prime 89)).mp h).resolve_left prime.ne_one
    subst q
    exact eval3
  · have eq := ((Nat.dvd_prime (by decide : Nat.Prime 199)).mp h).resolve_left prime.ne_one
    subst q
    exact eval4
  · have eq := ((Nat.dvd_prime (by decide : Nat.Prime 211)).mp h).resolve_left prime.ne_one
    subst q
    exact eval5
end ExamplePrime
#print axioms ExamplePrime.f43
