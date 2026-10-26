import Candidate.Cycle63.Physical.InitialMass.SecondOuterPayment

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondPhysicalBlock
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentSectorLocalization CenteredMomentSecondInputCapacitySource

/-- Zero physical blocks can be removed before the whole joint Cauchy step.
This supplies actual dyad witnesses wherever the outside weight survives. -/
def secondEffectiveWeight {Label : Type*} (s : Label→SecondBlockSource)
    (w : Label→ℂ) (W : 𝓢(ℝ,ℂ)) (l : Label) : ℂ :=
  if (s l).value W=0 then 0 else w l

theorem actual_second_effective_sum {Label : Type*}[Fintype Label]
    (s : Label→SecondBlockSource)(w : Label→ℂ)(W : 𝓢(ℝ,ℂ)) :
    (∑l,w l*(s l).value W)=∑l,secondEffectiveWeight s w W l*(s l).value W := by
  refine Finset.sum_congr rfl fun l hl => ?_
  unfold secondEffectiveWeight
  split_ifs with h <;> simp_all

/-- A scalar bound for the actual effective weights, valid even when a
block has vanished. The normalizer is paid once on each squared side. -/
theorem actual_second_effective_scalar_bound {α Label : Type*}
    [Fintype α][DecidableEq α]
    (N : ℕ)(a ap : ℝ)(ha : 0<a)(hap : 0<ap)
    (d : Label→SecondInputDatum α)(w : Label→ℂ)(W : 𝓢(ℝ,ℂ))
    (hcard : Fintype.card α≤N)
    (hlower : ∀l,a≤(d l).input.lower)
    (hW₁ : ∀l x,(d l).input.W₁ x≠0 → ap≤x)
    (hW₂ : ∀l x,(d l).input.W₂ x≠0 → ap≤x)
    (r : SecondRow (fun l=>(d l).block)) :
    let we := secondEffectiveWeight (fun l=>(d l).block) w W
    let balance := secondGeometricBalance (fun l=>(d l).block) we
    let E := ‖w r.1‖*((d r.1).K/lowerFactor N a ap)*
      normalizer (d r.1).C (d r.1).D (d r.1).inactive
    ‖(balance r:ℂ)⁻¹*secondRowLeftScalar d we r‖^2≤E ∧
    ‖(balance r:ℂ)*secondRowRightScalar d r‖^2≤E := by
  intro we balance E
  obtain ⟨hl,hr⟩ := actual_second_balanced_scalar_norms d we r
  rw [hl,hr]
  suffices hh : ‖we r.1‖*(d r.1).block.outside*volume (d r.1).input.toData≤E from ⟨hh,hh⟩
  have hp := lowerFactor_pos N a ap ha hap
  have hv := volume_pos (d r.1).input.toData
  have hn := normalizer_pos (d r.1).C (d r.1).D (d r.1).hC (d r.1).inactive
  by_cases h : (d r.1).block.value W=0
  · simp only [we,secondEffectiveWeight,h,ite_true,norm_zero,zero_mul]
    dsimp only [E]
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (div_pos (d r.1).K_pos hp).le) hn.le
  · have hh := actual_input_second_outside N a ap ha hap (d r.1) W hcard
      (hlower r.1) (hW₁ r.1) (hW₂ r.1) h
    simp only [we,secondEffectiveWeight,h,ite_false]
    have hh' := mul_le_mul_of_nonneg_left hh (norm_nonneg (w r.1))
    have hh'' := mul_le_mul_of_nonneg_right hh' hv.le
    apply hh''.trans (le_of_eq ?_)
    dsimp only [E]
    field_simp

/-- The original block sum is contracted after removing its zero terms
and balancing the remaining actual scalars. -/
theorem actual_second_effective_contraction (W : 𝓢(ℝ,ℂ))(A J : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀{Label : Type*}[Fintype Label][DecidableEq Label]
      (s : Label→SecondBlockSource)(w : Label→ℂ)(r : ℝ),
      0< r → (∀l,(s l).ratio=r) → ∀E : ℝ,0≤E →
      (∀t : ℝ,secondBalancedEnergyPair s (secondEffectiveWeight s w W)
        (secondGeometricBalance s (secondEffectiveWeight s w W)) t≤E*(1+‖t‖)^J) →
      (1+r)^A*‖∑l,w l*(s l).value W‖≤C*E := by
  obtain ⟨C,hC,hbound⟩ := actual_second_balanced_contraction W A J
  refine ⟨C,hC,?_⟩
  intro Label _ _ s w r hr heq E hE he
  rw [actual_second_effective_sum s w W]
  exact hbound s (secondEffectiveWeight s w W)
    (secondGeometricBalance s (secondEffectiveWeight s w W))
    (second_geometric_balance_nonzero s (secondEffectiveWeight s w W)) r hr heq E hE he

end
end OAI.SevenEighths.Cycle63InitialMass
