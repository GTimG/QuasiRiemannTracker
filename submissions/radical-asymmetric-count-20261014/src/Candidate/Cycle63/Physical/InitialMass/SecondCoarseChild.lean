import Candidate.Cycle63.Physical.InitialMass.SecondCoarseJoint

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open LocalMoment ProbePhysical IdealMobiusDivisorSum CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildSourceCaps
open Cycle63Moment
local notation "O" => HeckeFamily.O

/-- An all-height joint shell estimate from the original source's fixed
support, coefficient and scale bounds. The two common allocations and their
new heights are quantified after the constant and asymptotic threshold. -/
theorem actual_child_selected_coarse_shell {α : Type}[Fintype α][DecidableEq α]
    (N : ℕ)(hα : Fintype.card α≤N)
    (B loss ε pad Cs b bs window cap : ℝ)
    (hB : 0≤B)(hloss : 0<loss)(hε : 0<ε)(hpad : 0<pad)
    (hCs : 1≤Cs)(hb : 1≤b)(hbs : 1≤bs)(hwindow : 0≤window)(hcap : 0≤cap) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,2≤Z ∧
      ∀{κ : Type}(left : Bool)(u₀ : O)(unit : FirstSourceLabel→O)
        (m control T : ℝ),0≤control → 1≤T →
      ∀(key : κ→NonzeroJointSourceLabel left u₀ unit),Function.Injective key →
      ∀labels : Finset κ,
      (∀label∈labels,rawFrequencyNorm (nonzeroJointSourceRow (key label))≤Z^B) →
      (∀label∈labels,Supported (key label).val.1.1.1 ∧ (key label).val.1.1.2≠0 ∧
        Supported (key label).val.2.1.1 ∧ (key label).val.2.1.2≠0) →
      (∀label∈labels,primeSupport (key label).val.1.1.1=primeSupport (key label).val.1.1.2 ∧
        primeSupport (key label).val.2.1.1=primeSupport (key label).val.2.1.2) →
      (∀label∈labels,((Ideal.span {jointSourceRow left u₀ unit (key label).val}*
        firstSourceMissing left (key label).val.1).absNorm:ℝ)≤Z^B) →
      (∀label∈labels,((key label).val.1.1.1.absNorm:ℝ)≤Z^B ∧
        ((key label).val.1.1.2.absNorm:ℝ)≤Z^B ∧
        ((key label).val.2.1.1.absNorm:ℝ)≤Z^B ∧ ((key label).val.2.1.2.absNorm:ℝ)≤Z^B) →
      (∀label∈labels,((firstSourceMissing left (key label).val.1).absNorm:ℝ)≤Z^m) →
      ∀s : Input α,(∀j,s.M j≤Cs) → s.upper≤b → s.b₁≤bs → s.b₂≤bs →
      (∀j,CenteredMomentSlotRatios.logWindow (s.lo j) (s.hi j)≤window) →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^cap) →
      (∀j,s.P j≤Z^cap) →
      ∀(C₁ R₁ : κ→Ideal O)(A₁ : ∀l,actualAllocations s.pools (C₁ l))
        (χ₁ : κ→Character)(t₁ : κ→ℝ),
      let first := fun l=>child s (C₁ l) (R₁ l) (A₁ l) (χ₁ l) (t₁ l)
      ∀(C₂ R₂ : κ→Ideal O)(A₂ : ∀l,actualAllocations (first l).pools (C₂ l))
        (χ₂ : κ→Character)(t₂ : κ→ℝ)(z : κ→O)
        (Ds : κ→Finset (Ideal O))(B₁ B₂ : ℝ),
      0≤B₁ → 0≤B₂ → (∀x,‖s.W₁ x‖≤B₁) → (∀x,‖s.W₂ x‖≤B₂) →
      (B₁*B₂)^2≤control →
      (∀l∈labels,∀D∈Ds l,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
      let src := fun l=>commonData (withHeight (first l) (χ₂ l) (t₂ l)) (C₂ l) (R₂ l) (A₂ l)
      (∑l∈labels,∑D∈Ds l,∑a∈(src l).toSource.active D,
        retainedAllocationCost (src l) D a (z l))≤
      C*control*(2*T)^(2*ε)*Z^(m+B+loss+((N:ℝ)+2)*cap+pad) := by
  let Index := (S : Finset α) × Finset S
  let Slots := fun i : Index=>↥i.2
  have hN (i : Index) : Fintype.card (Slots i)≤N := by
    exact (Fintype.card_subtype_le _).trans ((Fintype.card_subtype_le _).trans hα)
  obtain ⟨C,hC,hshell⟩ := actual_selected_coarse_shell Slots N hN B loss ε hB hloss hε
  have hfixed := coarse_fixed_control_pos N Cs b bs hCs hb hbs
  refine ⟨C*coarseFixedControl N Cs b bs,mul_pos hC hfixed,?_⟩
  filter_upwards [eventual_two_common_allowance N window bs pad hwindow hbs hpad,
    eventually_ge_atTop (2:ℝ)] with Z hallow hZ
  refine ⟨hZ,?_⟩
  intro κ left u₀ unit m control T hcontrol hT key hinj labels
    hrow hsupported heq hsupport hnorm hmissing s hM hupper hb₁ hb₂ hwin hscales hP
    C₁ R₁ A₁ χ₁ t₁ first C₂ R₂ A₂ χ₂ t₂ z Ds B₁ B₂ hB₁ hB₂ hW₁ hW₂ hcontrolB hDs src
  let index := fun l=> (⟨CenteredMomentCommonProfile.liveIndices (A₁ l).val,
    CenteredMomentCommonProfile.liveIndices (A₂ l).val⟩ : Index)
  have hh := hshell left u₀ unit Z m (((N:ℝ)+2)*cap) pad
    (coarseFixedControl N Cs b bs*control) T hZ (mul_nonneg hfixed.le hcontrol) hT key hinj labels
    hrow hsupported heq hsupport hnorm hmissing index src z Ds (fun _=>B₁) (fun _=>B₂)
    (fun _ _=>⟨hB₁,hB₂⟩) (fun _ _ x=>⟨hW₁ x,hW₂ x⟩) ?_ ?_ hDs
  · convert hh using 1 <;> ring
  · intro l hl
    exact (actual_two_common_coarse_control N Cs b bs cap Z B₁ B₂ hCs hb hbs hcap
      (by linarith) hB₁ hB₂ s hα hM hupper hb₁ hb₂ hscales hP
      (C₁ l) (R₁ l) (A₁ l) (χ₁ l) (t₁ l) (C₂ l) (R₂ l) (A₂ l) (χ₂ l) (t₂ l)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcontrolB hfixed.le) (by positivity))
  · intro l hl
    have hh := hallow.2 s hα hwin hb₁ hb₂ (C₁ l) (R₁ l) (A₁ l) (χ₁ l) (t₁ l)
      (C₂ l) (R₂ l) (A₂ l) (χ₂ l) (t₂ l)
    have hp : 0≤Cycle63.Physical.plainClipAllowance Z ![(src l).b₁,(src l).b₂] := by
      unfold Cycle63.Physical.plainClipAllowance
      exact Finset.sum_nonneg (fun j _=>Real.logb_nonneg hallow.1 (le_max_left _ _))
    linarith

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_child_selected_coarse_shell
