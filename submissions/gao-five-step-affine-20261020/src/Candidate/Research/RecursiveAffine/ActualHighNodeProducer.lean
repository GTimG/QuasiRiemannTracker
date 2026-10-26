/- Literal own-HIGH node of the recursive source tree. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.PrefixHighReturnedNode

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153RecursiveHighProvider
noncomputable section
open Cycle153HighProvider Cycle153SourceReturn
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondCanonicalScalar
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondPhysicalBlock
open Cycle63Moment Cycle63Moment.LowBranch Cycle63InitialMass
open ConcretePrimeRowBridge CompletedGauss Cycle63FinalNatural
open CenteredMomentNaturalFixedRaySource CenteredMomentAllocatedRayDictionary
open CenteredMomentEnergyState CenteredMomentEnergyBands Cycle63InitialSource
open CenteredMomentFirstAmplificationChoice CenteredMomentSecondHeightFamily
open CenteredMomentInductionEnergy CenteredMomentPrimeSlot

variable {Base : Type} {base : Character → Base → Character}
variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
variable [Cycle63.AffineLedger]

/-- The current source's own HIGH output uses its literal actual volume,
row scale and amplifier. Its accumulated masked prefix is supplied by the
actual source state; no count, HIGH energy bound or model length is input. -/
def ActualHighNodeAt
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100 ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7/8)
    (g : GeometryAffineLowSchedule) (ap bp bΦ Bmask mesh ε τlow B lossNeeded : ℝ)
    (hap : 0<ap) (Ψ : 𝓢(ℝ,ℂ)) (SH : Finset (ℕ×ℕ)) (dh : ℕ) (Kclass Kh : ℝ)
    (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)}) (Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(hT : 2<Z^g.τ)(T : Finset α)
    (θ : T→RayQuotient.Characters M H)(w σ freq : T→ℝ)
    (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))(t height : ℝ),
    (∀i,0 ≤ w i) → (∀i,w i ≤ mesh) → 0 ≤ height → (∀i,|freq i| ≤ height) →
  ∀(state : NaturalState Z Bmask bΦ),state.fixedModulus=internalQ Q η₀ → state.width ≤ 1 →
  ∀(p : Profiles ap bp)(X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂),
    Cycle63.AffineLedger.PlainWindow (length Z X₁) (length Z X₂) (∑i,w i) →
  ∀(P : PrefixHighPresentation (base η₀) state.character state.puncture)(τT : ℝ),τlow ≤ τT →
    ((Ideal.span {P.mult}).absNorm:ℝ) ≤ Z^(B-130) →
  let s:=affineInput M H hH η₀ θ W hW.continuous 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq hσ state p hap
    (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) t X₁ X₂ hX₁ hX₂
  let amp:=Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
    (Cycle63.AffineLedger.originalCell (∑i,w i)))
  ∃part : ReturnedPartAt M H hH Cycle63.AffineLedger.q
      (fun η=>extendFixedDictionary (base η)) η₀ Z B (Z^τT) P.mult,
    part.scale=state.rowWidth ∧ part.length=Real.logb Z (volume s) ∧ part.amp=amp ∧
    part.loss=lossNeeded+ε ∧ (∀b,(Fintype.card (part.record b).Class:ℝ) ≤ Kclass) ∧
    GeometryAffineHighGiven (α:=T) M H hH g η₀ Q hQM hQ72 hβlo hβhi Z hZ hT ap bp s p state.puncture 1
      state.rowWidth amp Ψ (profile_zero_of_pos p hap 0) (profile_zero_of_pos p hap 1) SH dh height
      (Kh*(Z^(-(state.rowWidth+3*g.δ-amp+ε))*part.value+1))

/-- Bind the literal current affine source to the records produced by the
native physical HIGH proof. The only source-producing input is its proved
uniform producer conclusion, never an assumed record or energy cap. -/
theorem actual_high_node_at_of_given
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100 ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7/8)
    (g : GeometryAffineLowSchedule) (ap bp bΦ Bmask mesh ε τlow B lossNeeded : ℝ)
    (hap : 0<ap) (Ψ : 𝓢(ℝ,ℂ)) (SH : Finset (ℕ×ℕ)) (dh : ℕ) (Kclass Kh : ℝ)
    (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)}) (Z : ℝ)
    (hgiven : DepthTwoHighGivenAt (base:=base) (α:=α) M H hH W hW hWs hβlo hβhi
      g ap bp bΦ Bmask mesh ε τlow B lossNeeded hap Ψ SH dh Kclass Kh η₀ Q hQM hQ72 Z) :
    ActualHighNodeAt (base:=base) (α:=α) M H hH W hW hWs hβlo hβhi
      g ap bp bΦ Bmask mesh ε τlow B lossNeeded hap Ψ SH dh Kclass Kh η₀ Q hQM hQ72 Z := by
  intro hZ hT T θ w σ freq hσ t height hw hmesh hheight hfreq state hfixed hwidth
    p X₁ X₂ hX₁ hX₂ hwindow P τT hτT hvbound s amp
  exact actual_prefix_high_returned_node (base:=base) M H hH W hW hWs hβlo hβhi g
    ap bp bΦ Bmask mesh ε τlow B lossNeeded hap Ψ SH dh Kclass Kh η₀ Q hQM hQ72 Z
    hgiven hZ hT T θ w σ freq hσ t height hw hmesh hheight hfreq state hfixed hwidth
    p X₁ X₂ hX₁ hX₂ hwindow P.mult τT (Z^τT) hτT ⟨⟨le_rfl,le_rfl⟩,P,rfl⟩ hvbound
    (Real.logb Z (volume s)) amp (lossNeeded+ε) le_rfl le_rfl le_rfl

/-- Uniform actual-node producer, including every surviving original slot
subset. The schedule and constants come from the proved native source
producer; every current node retains its own literal masked prefix and
actual capacity. -/
theorem actual_high_node_producer
    (affineLoss : ℝ) (hupper : affineLoss  ≤  secondStepAffineLoss)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100 ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7/8)
    (mesh τlow B : ℝ) (hε : 0<affineLoss)
    (hmesh0 : 0 ≤ mesh)
    (hmesh : mesh ≤ Cycle25.Energy.commonMesh 2 28 1 (highSourceLossUnit affineLoss/8))
    (hτlow : 0<τlow) (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M)
    (hQ0 : internalQ Q η₀≠0) (hQt : internalQ Q η₀≠⊤)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)})
    (hq : Cycle63.Arithmetic.q0 ≤ Cycle63.AffineLedger.q) :
    ∃g : GeometryAffineLowSchedule,g.μ=highSourceLossUnit affineLoss ∧
      g.δ=geometryFinalDictionaryRate (highSourceLossUnit affineLoss) 31 3 4 3 130
        (3*((Fintype.card α:ℝ)+2)) (Fintype.card α) ∧ 2*g.τ<τlow ∧
    ∀(Ψ : 𝓢(ℝ,ℂ)),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (2+1) → (∀x,0 ≤ (Ψ x).re) →
    ∃(SH : Finset (ℕ×ℕ))(dh : ℕ)(Kclass : ℝ),∀ε : ℝ,0<ε →
    ∃Kh : ℝ,0 ≤ Kh ∧ ∀ᶠZ : ℝ in atTop,
      ActualHighNodeAt (base:=base) (α:=α) M H hH W hW hWs hβlo hβhi g (1/4) (9/4) 2 20
        mesh ε τlow B (highSourceLossNeeded affineLoss (Fintype.card α)) (by norm_num) Ψ SH dh Kclass Kh η₀ Q hQM hQ72 Z := by
  obtain ⟨g,hgμ,hgδ,hgτ,hsource⟩ := twoLevelHighProducer (base:=base) affineLoss hupper
    M H hH (β:=α) W hW hWs hβlo hβhi mesh τlow B hε (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hmesh0 hmesh hτlow η₀ Q hQM hQ0 hQt hQ72
    (highSourceLossUnit affineLoss) rfl hq
  refine ⟨g,hgμ,hgδ,hgτ,?_⟩
  intro Ψ hΨ hΨpos
  obtain ⟨SH,dh,Kclass,hconst⟩:=hsource Ψ hΨ hΨpos
  refine ⟨SH,dh,Kclass,?_⟩
  intro ε hε
  obtain ⟨Kh,hKh,hsource⟩:=hconst ε hε
  refine ⟨Kh,hKh,?_⟩
  filter_upwards [hsource] with Z hZ
  exact actual_high_node_at_of_given (base:=base) M H hH W hW hWs hβlo hβhi g (1/4) (9/4) 2 20
    mesh ε τlow B (highSourceLossNeeded affineLoss (Fintype.card α)) (by norm_num) Ψ SH dh Kclass Kh η₀ Q hQM hQ72 Z hZ

end
end OAI.SevenEighths.Cycle153RecursiveHighProvider
#print axioms OAI.SevenEighths.Cycle153RecursiveHighProvider.actual_high_node_producer
