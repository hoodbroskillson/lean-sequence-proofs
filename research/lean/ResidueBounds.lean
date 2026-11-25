import PrimeBounds
namespace ResidueBounds
open Polynomial

private theorem root {p:ℕ} [Fact p.Prime] (hp:2<p) {K:Type*} [Field K] [CharP K p]
    (f:ZMod p →+* K) (z:K) (zero:z^4+z^3+z^2+z+1=0) :
    (p%5=1 ∨ p%5=4 → FinitePeriod.Tail p 5 (3*(p-1))) ∧
    (p%5=2 ∨ p%5=3 → FinitePeriod.Tail p 5 (6*(p+1)) ∧
      ∀N,¬FinitePeriod.Tail p N (3*(p+1))) := by
  have fifth : z^5=1 := by linear_combination (z-1)*zero
  have reduce (n:ℕ) : z^n=z^(n%5) := by
    conv_lhs => rw [←Nat.mod_add_div n 5,pow_add,pow_mul,fifth,one_pow,mul_one]
  let r := -(z+z^4)
  have hr : r^2=r+1 := by
    dsimp [r];linear_combination zero+(z^3+2)*fifth
  have fr : r^p= -(z^(p%5)+(z^(p%5))^4) := by
    change (frobenius K p) (-(z+z^4))=_
    rw [map_neg,map_add,map_pow,frobenius_def,reduce]
  have cases:=PrimeBounds.root_cases hp f r hr
  constructor
  · intro choice
    apply cases.1
    rcases choice with e|e
    · rw [fr,e,pow_one]
    · rw [fr,e,←pow_mul,reduce (4*4)]
      simp only [show (4*4:ℕ)%5=1 by decide,pow_one,r]
      rw [add_comm]
  · intro choice
    have swap : r^p=1-r := by
      rcases choice with e|e
      · rw [fr,e,←pow_mul,reduce (2*4)]
        change -(z^2+z^3)=1-(-(z+z^4))
        linear_combination -zero
      · rw [fr,e,←pow_mul,reduce (3*4)]
        change -(z^3+z^2)=1-(-(z+z^4))
        linear_combination -zero
    have negative : r^(p+1)= -1 := by rw [pow_succ,swap];linear_combination -hr
    have pow : r^(2*(p+1))=1 := by rw [Nat.mul_comm,pow_mul,negative];norm_num
    constructor
    · apply (RootOrders.source hp f r hr 5 _).mpr <| Or.inr ⟨le_rfl,?_⟩
      simpa only [←Nat.mul_assoc] using Nat.mul_dvd_mul_left 3
        (Nat.lcm_dvd (dvd_mul_right 2 (p+1)) (orderOf_dvd_iff_pow_eq_one.mpr pow))
    · intro N h
      have d:=((RootOrders.source hp f r hr N _).mp h).resolve_left (by omega)
      have rd:=dvd_trans (Nat.dvd_lcm_right 2 (orderOf r)) (Nat.dvd_of_mul_dvd_mul_left (by decide : 0<3) d.2)
      have eq : r^(p+1)=1 := orderOf_dvd_iff_pow_eq_one.mp rd
      have z : (2:K)=0 := by linear_combination negative-eq
      have base : (2:ZMod p)=0 := f.injective (by simpa only [map_ofNat,map_zero] using z)
      have dvd : p∣2 := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp (by simpa using base)
      exact (Nat.not_le_of_lt hp) (Nat.le_of_dvd (by decide : 0<2) dvd)

theorem residues {p:ℕ} [Fact p.Prime] (hp:2<p) :
    (p%5=1 ∨ p%5=4 → FinitePeriod.Tail p 5 (3*(p-1))) ∧
    (p%5=2 ∨ p%5=3 → FinitePeriod.Tail p 5 (6*(p+1)) ∧
      ∀N,¬FinitePeriod.Tail p N (3*(p+1))) := by
  classical
  let g : Polynomial (ZMod p) := X^4+X^3+X^2+X+1
  have deg : g.degree ≠ 0 := by
    have eq : g.degree=4 := by dsimp [g];compute_degree <;> first | exact one_ne_zero | decide
    rw [eq];decide
  let K:=g.SplittingField
  let f:=algebraMap (ZMod p) K
  obtain ⟨z,hz⟩:=exists_root_of_splits f (SplittingField.splits g) deg
  have zero:z^4+z^3+z^2+z+1=0 := by
    simpa only [g,eval₂_add,eval₂_pow,eval₂_X,eval₂_one] using hz
  exact root hp f z zero

end ResidueBounds
#print axioms ResidueBounds.residues
