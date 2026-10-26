import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.SecondActualSources
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.FinalNatural.State

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open ActualEisensteinCubic ConcreteTraceCRT CenteredMomentFirstAmplificationChoice
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondRadicalBudget CenteredMomentSecondRetainedWidth
open CenteredMomentSectorLocalization CenteredMomentSupport
open Cycle61FinalNatural Cycle61Moment
local notation "O" => HeckeFamily.O

variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]

theorem actual_second_live_correlation (s : Label→SecondBlockSource)
    (r : secondLiveRows s) :
    idealCorrelation (s r.val.1).C (s r.val.1).D (s r.val.1).hC (s r.val.1).hD
      ((s r.val.1).frequency*r.val.2.2.2.val)≠0 :=
  right_ne_zero_of_mul (Finset.mem_filter.mp r.property).2.2.2

/-- Every retained physical row supplies the character conductor cap.
Cancellation of its containing block is irrelevant to this pointwise gate. -/
theorem actual_second_live_conductor (d : Label→SecondInputDatum α)
    (r : secondLiveRows (fun l=>(d l).block)) (χ : RayCharacter) :
    ((d r.val.1).τ χ).modulus.absNorm≤(d r.val.1).input.η.modulus.absNorm*fixedFactor*
      (∏P∈(d r.val.1).inactive,P.val).absNorm*
        (Ideal.span {nonunitFrequencyGenerator (d r.val.1).C (d r.val.1).D
          (d r.val.1).inactive}).absNorm := by
  apply (d r.val.1).rowBudget
    (nonunitFrequencyGenerator (d r.val.1).C (d r.val.1).D (d r.val.1).inactive*r.val.2.2.2.val) _ χ
  simpa only [SecondInputDatum.block,originalSecondBlock,SecondBlockSource.frequency,mul_assoc]
    using actual_second_live_correlation (fun l=>(d l).block) r

/-- Width admissibility now follows from the actual retained row and its
actual character family, without a nonzero-whole-block assumption. -/
theorem actual_second_live_state_width (d : Label→SecondInputDatum α)
    (r : secondLiveRows (fun l=>(d l).block))
    (Z Bmask : ℝ) (hZ : 1<Z) (χ : RayCharacter) (Q P : Ideal O)
    (hP : P≠0) (hPN : (P.absNorm:ℝ)≤Z^Bmask) :
    let v := d r.val.1
    (retainedState Z Bmask hZ (v.τ χ) Q P hP hPN v.radius v.C v.D v.inactive).width≤
      Real.logb Z v.radius+Real.logb Z (v.input.η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator v.C v.D))+
        Real.logb Z ((∏p∈v.inactive,p.val).absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) := by
  dsimp only
  rw [retainedState_width]
  have hU : (∏p∈(d r.val.1).inactive,p.val)≠0 := Finset.prod_ne_zero_iff.mpr
    (fun p _=>(commonPrime_supported_ideal _ _ (d r.val.1).hC p).1)
  exact retained_log_budget _ _ _ _ r.val.2.2.2.val _ hU
    (actual_second_live_conductor d r χ) _ _ hZ
    (actual_second_live_retained_weight (fun l=>(d l).block) r.val r.property)


/-- The actual row lies in the plateau of the retained ball profile. -/
theorem actual_second_live_state_majorant (d : Label→SecondInputDatum α)
    (r : secondLiveRows (fun l=>(d l).block))
    (Z Bmask : ℝ) (hZ : 1<Z) (χ : RayCharacter) (Q P : Ideal O)
    (hP : P≠0) (hPN : (P.absNorm:ℝ)≤Z^Bmask) :
    let v := d r.val.1
    let st := retainedState Z Bmask hZ (v.τ χ) Q P hP hPN v.radius v.C v.D v.inactive
    1≤(st.radial.profile (‖eisEmbedding r.val.2.2.2.val‖^2/st.radial.scale)).re := by
  dsimp only
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact Cycle61FinalRadius.actual_retained_majorant _ _ _ r.val.2.2.2.val
    (actual_second_live_retained_weight (fun l=>(d l).block) r.val r.property)

/-- The nonexceptional branch supplies the exact natural-state keep gate
and a nonvanishing radial value used by high-source admissibility. -/
theorem actual_second_live_state_admission (d : Label→SecondInputDatum α)
    (r : secondLiveRows (fun l=>(d l).block))
    (Z Bmask : ℝ) (hZ : 1<Z) (χ : RayCharacter) (Q P : Ideal O)
    (hP : P≠0) (hPN : (P.absNorm:ℝ)≤Z^Bmask)
    (m : O) (hm : m≠0) (hml : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (hkeep : CenteredMomentRestrictedEnergy.nonexceptional (d r.val.1).input.η χ Q m
      (d r.val.1).block.frequency r.val.2.2.2.val) :
    let v := d r.val.1
    let st := retainedState Z Bmask hZ (v.τ χ) Q P hP hPN v.radius v.C v.D v.inactive
    st.radial.keep r.val.2.2.2.val ∧
      st.radial.profile (‖eisEmbedding r.val.2.2.2.val‖^2/st.radial.scale)≠0 := by
  dsimp only
  refine ⟨(actual_nonexceptional_keep (d r.val.1).family _ Z Bmask hZ χ Q P hP hPN
    m _ hm hml hm2).mp hkeep,?_⟩
  have hp := actual_second_live_state_majorant d r Z Bmask hZ χ Q P hP hPN
  dsimp only at hp
  intro hz
  rw [hz] at hp
  norm_num at hp

/-- The right column uses the reflected row, with the same ball majorant
but its own ray character and puncture. -/
theorem actual_second_reflected_state_admission (d : Label→SecondInputDatum α)
    (r : secondLiveRows (fun l=>(d l).block))
    (Z Bmask : ℝ) (hZ : 1<Z) (χ : RayCharacter) (Q P : Ideal O)
    (hP : P≠0) (hPN : (P.absNorm:ℝ)≤Z^Bmask)
    (m : O) (hm : m≠0) (hml : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (hkeep : CenteredMomentRestrictedEnergy.nonexceptional (d r.val.1).input.η χ Q m
      (d r.val.1).block.frequency (-r.val.2.2.2.val)) :
    let v := d r.val.1
    let st := retainedState Z Bmask hZ (v.τ χ) Q P hP hPN v.radius v.C v.D v.inactive
    st.radial.keep (-r.val.2.2.2.val) ∧
      st.radial.profile (‖eisEmbedding (-r.val.2.2.2.val)‖^2/st.radial.scale)≠0 := by
  dsimp only
  refine ⟨(actual_nonexceptional_keep (d r.val.1).family _ Z Bmask hZ χ Q P hP hPN
    m _ hm hml hm2).mp hkeep,?_⟩
  have hp := actual_second_live_state_majorant d r Z Bmask hZ χ Q P hP hPN
  dsimp only at hp
  rw [map_neg,norm_neg]
  intro hz
  rw [hz] at hp
  norm_num at hp

/-- The actual live row inherits the six-amplifier width saving from the
first main radius. This uses the row conductor budget, so a cancelled
physical block does not invalidate admission. -/
theorem actual_second_live_main_width (d : Label→SecondInputDatum α)
    (r : secondLiveRows (fun l=>(d l).block))
    (η₀ : Character) (C₁ D₁ : Ideal O) (hC₁ : Supported C₁) (hD₁ : Supported D₁)
    (heq : primeSupport C₁=primeSupport D₁) (E : Finset (CommonIndex C₁ D₁))
    (K₀ V Z a δ reserve ξ b : ℝ) (N : ℕ)
    (hK₀ : 0<K₀) (hV : 0<V) (hZ : 1<Z) (hb : 0<b)
    (hmod : (d r.val.1).input.η.modulus=η₀.modulus*
      Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun p : CommonIndex C₁ D₁=>p.val) E*
        activeConductor C₁ D₁})
    (Bmask : ℝ) (χ : RayCharacter) (Q P : Ideal O)
    (hP : P≠0) (hPN : (P.absNorm:ℝ)≤Z^Bmask) :
    let c := Real.logb Z (C₁.absNorm:ℝ)
    let e := Real.logb Z (D₁.absNorm:ℝ)
    let k := nominalLog C₁ D₁
      (Ideal.span {primeSubsetGenerator (fun p : CommonIndex C₁ D₁=>p.val) E}) K₀ V Z
    let Kmain := CenteredMomentAmplifiedRetainedRadius.mainCommonRadius Z e k c (3*a) δ reserve
    (d r.val.1).radius=CenteredMomentSectorLocalization.frequencyRadius
      ((b^N*V/(C₁.absNorm:ℝ))^2/Kmain) Z ξ →
    let v := d r.val.1
    (retainedState Z Bmask hZ (v.τ χ) Q P hP hPN v.radius v.C v.D v.inactive).width≤
      (Real.logb Z K₀+Real.logb Z (η₀.modulus.absNorm:ℝ)-max (c-e) 0-6*a-δ-reserve-
        Real.logb Z (normValue (commonFrequencyGenerator v.C v.D))+
        Real.logb Z ((∏p∈v.inactive,p.val).absNorm:ℝ))+
      (Real.logb Z CenteredMomentFirstPhysicalSource.fixedPresentationCost+
        2*(N:ℝ)*Real.logb Z b+ξ/2+Real.logb Z (4*(fixedFactor:ℝ))) := by
  dsimp only
  intro hradius
  have hw := actual_second_live_state_width d r Z Bmask hZ χ Q P hP hPN
  have hr := Cycle61FinalRadius.main_inverse_radius_log η₀ (d r.val.1).input.η
    C₁ D₁ hC₁ hD₁ heq E K₀ V Z a δ reserve ξ b N hK₀ hV hZ hb hmod
  dsimp only at hw hr
  rw [hradius] at hw ⊢
  linarith

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_live_correlation
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_live_conductor
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_live_state_width

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_live_state_majorant
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_live_state_admission

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_live_main_width

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_reflected_state_admission
