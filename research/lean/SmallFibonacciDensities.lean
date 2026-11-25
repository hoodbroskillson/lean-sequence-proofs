import DensityLimitCore
import FibResidueBound

namespace SmallFibonacciDensities
noncomputable section
open Filter Topology FibResidueBound

/-- Bragman and Rowland's density of the Fibonacci image modulo p^k, including F₀. -/
def imageDensity (p k : ℕ) : ℝ := (Nat.card (attained (p^k)):ℝ) / (p^k:ℕ)
def dens (p : ℕ) := DensityLimitCore.limiting (fun m => Nat.card (attained m)) p

theorem density_limit {p : ℕ} (hp : 0<p) :
    Tendsto (imageDensity p) atTop (𝓝 (dens p)) := by
  have eq : imageDensity p = DensityLimitCore.ratio (fun m => Nat.card (attained m)) p := by
    funext k
    simp only [imageDensity,DensityLimitCore.ratio,Nat.cast_pow]
  rw [eq]
  exact
    (DensityLimitCore.converges (fun m => Nat.card (attained m)) lifts hp)

theorem arbitrarily_small (ε : ℝ) (hε : 0<ε) (B : ℕ) :
    ∃ p : ℕ, p.Prime ∧ B<p ∧ 0≤dens p ∧ dens p<ε ∧
      Tendsto (imageDensity p) atTop (𝓝 (dens p)) := by
  have bound {p n : ℕ} (hp : p.Prime) (hn : 1≤n) (hd : p∣Nat.fib n) :
      Nat.card (attained p)≤4*n := by
    simpa only [zero_add,pow_one,pow_zero,mul_one] using count hp hn hd 0
  obtain ⟨p,hp,hB,small⟩ := DensityLimitCore.small_primes _
    (fun hp hn hd => bound hp hn hd) FibonacciLargeFactor.unbounded ε hε B
  exact ⟨p,hp,hB,DensityLimitCore.nonnegative _ _,small,density_limit hp.pos⟩

end
end SmallFibonacciDensities
#print axioms SmallFibonacciDensities.density_limit
#print axioms SmallFibonacciDensities.arbitrarily_small
