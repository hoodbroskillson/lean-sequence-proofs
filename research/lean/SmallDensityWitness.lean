import SmallFibonacciDensities
import ExamplePrime
namespace SmallDensityWitness
open FibResidueBound SmallFibonacciDensities
private theorem onePeriod {m T : ℕ} (hT : 0<T) (h : ∀ j, Nat.fib (j+T)%m=Nat.fib j%m) :
    attained m = ↑((Finset.range T).image (fun j => Nat.fib j%m)) := by
  ext r
  constructor
  · rintro ⟨j,rfl⟩
    change Nat.fib j % m ∈ (Finset.range T).image _
    induction j using Nat.strong_induction_on with
    | h j ih =>
      by_cases lt : j<T
      · exact Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr lt,rfl⟩
      · have e := h (j-T)
        rw [show j-T+T=j by omega] at e
        rw [e]; exact ih _ (by omega)
  · intro hr
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hr
    exact ⟨j,hj⟩

set_option maxRecDepth 200000 in
set_option maxHeartbeats 5000000 in
theorem witness : Nat.Prime 433494437 ∧ Nat.card (attained 433494437)=81 ∧
    dens 433494437 ≤ (81:ℝ)/433494437 := by
  have hp : Nat.Prime 433494437 := ExamplePrime.f43
  have h := FibonacciLargeFactor.period 433494437 43 (by decide)
  have eq := onePeriod (T:=172) (by decide) h
  have card : Nat.card (attained 433494437)=81 := by
    rw [eq]
    let s := (Finset.range 172).image (fun j => Nat.fib j % 433494437)
    change Nat.card s=81
    rw [Nat.card_eq_fintype_card,Fintype.card_coe s]
    dsimp only [s]
    decide
  refine ⟨hp,card,?_⟩
  have bounded : BddBelow (Set.range (DensityLimitCore.ratio (fun m => Nat.card (attained m)) 433494437)) := by
    refine ⟨0,?_⟩
    rintro _ ⟨k,rfl⟩
    unfold DensityLimitCore.ratio
    positivity
  have z := ciInf_le bounded (1:ℕ)
  change dens 433494437 ≤ _ at z
  simpa only [DensityLimitCore.ratio,pow_one,card,Nat.cast_ofNat] using z

end SmallDensityWitness
#print axioms SmallDensityWitness.witness
