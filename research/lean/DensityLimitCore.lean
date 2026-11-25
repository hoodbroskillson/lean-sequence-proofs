import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
namespace DensityLimitCore
noncomputable section
open Filter Topology

def ratio (counts : ℕ→ℕ) (p k : ℕ) : ℝ := (counts (p^k):ℝ)/(p:ℝ)^k
def limiting (counts : ℕ→ℕ) (p : ℕ) : ℝ := ⨅ k : ℕ, ratio counts p k
private theorem bounded (c : ℕ→ℕ) (p : ℕ) : BddBelow (Set.range (ratio c p)) := by
  refine ⟨0,?_⟩
  rintro _ ⟨n,rfl⟩
  unfold ratio
  positivity

theorem converges (c : ℕ→ℕ)
    (lift : ∀ a b : ℕ, 0<a → 0<b → c (a*b) ≤ c a*b)
    {p : ℕ} (hp : 0<p) : Tendsto (ratio c p) atTop (𝓝 (limiting c p)) := by
  apply tendsto_atTop_ciInf _ (bounded c p)
  apply antitone_nat_of_succ_le
  intro k
  have h : (c (p^k*p):ℝ)≤(c (p^k):ℝ)*p := by exact_mod_cast lift (p^k) p (pow_pos hp k) hp
  unfold ratio
  rw [pow_succ,pow_succ]
  calc
    _ ≤ ((c (p^k):ℝ)*p)/((p:ℝ)^k*p) := div_le_div_of_nonneg_right h (by positivity)
    _ = _ := by field_simp; ring

theorem nonnegative (c : ℕ→ℕ) (p : ℕ) : 0≤limiting c p := by
  apply le_ciInf
  intro k
  unfold ratio
  positivity

theorem small_primes (c : ℕ→ℕ)
    (bound : ∀ {p n : ℕ}, p.Prime → 1≤n → p∣Nat.fib n → c p≤4*n)
    (large : ∀ C B : ℕ, ∃ q p : ℕ, q.Prime ∧ B<q ∧ p.Prime ∧ 5<p ∧ p∣Nat.fib q ∧ C*q<p)
    (ε : ℝ) (hε : 0<ε) (B : ℕ) :
    ∃p : ℕ, p.Prime ∧ B<p ∧ limiting c p < ε := by
  obtain ⟨K,hK⟩ := exists_nat_gt (4/ε)
  let C := K+1
  obtain ⟨q,p,hq,bq,hp,_,dv,h⟩ := large C B
  have cq : q≤C*q := by simp [C,Nat.add_mul]
  refine ⟨p,hp,by omega,?_⟩
  have upper := ciInf_le (bounded c p) (1:ℕ)
  change limiting c p ≤ ratio c p 1 at upper
  rw [ratio,pow_one,pow_one] at upper
  apply lt_of_le_of_lt upper
  have pos : (0:ℝ)<p := by exact_mod_cast hp.pos
  apply (div_lt_iff pos).mpr
  have qpos : (0:ℝ)<q := by exact_mod_cast hq.pos
  have hr : (C:ℝ)*q<p := by exact_mod_cast h
  have hr' : (4:ℝ)<ε*C := by
    have := (div_lt_iff hε).mp hK
    dsimp [C]
    push_cast
    linarith
  have b : (c p:ℝ)≤4*(q:ℝ) := by exact_mod_cast bound hp hq.pos dv
  calc
    _ ≤ 4*(q:ℝ) := b
    _ < (ε*C)*q := mul_lt_mul_of_pos_right hr' qpos
    _ = ε*(C*q) := by ring
    _ < _ := mul_lt_mul_of_pos_left hr hε
end
end DensityLimitCore
#print axioms DensityLimitCore.converges
#print axioms DensityLimitCore.small_primes
