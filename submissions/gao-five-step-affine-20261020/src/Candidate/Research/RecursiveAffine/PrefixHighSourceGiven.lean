/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineAtState
import Candidate.Cycle63.Moment.DepthTwoHighCount
import Candidate.Research.RecursiveAffine.PrefixHighPresentation

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle153RecursiveHighProvider
noncomputable section
open Cycle153HighProvider
variable {Base : Type} {base : HeckeFamily.Character → Base → HeckeFamily.Character}
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondCanonicalScalar
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondPhysicalBlock
open Cycle63Moment Cycle63Moment.LowBranch Cycle63InitialMass
open ConcretePrimeRowBridge CompletedGauss
open Cycle63FinalNatural CenteredMomentDivisorExtraction CenteredMomentCommonRawScale
open CenteredMomentNaturalFixedRaySource CenteredMomentAllocatedRayDictionary
open CenteredMomentEnergyState CenteredMomentEnergyBands Cycle63InitialSource
open CenteredMomentFirstAmplificationChoice CenteredMomentSecondHeightFamily
open CenteredMomentInductionEnergy CenteredMomentPrimeSlot

variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance depthTwoHighGivenFiniteQuotient : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

variable [Cycle63.AffineLedger] in
/-- At a parent `state` of the second step presented by `v₁`, the HIGH part of the second transform is given by the
count form of two records `Hb b`, one for each orientation `b`: they pay the HIGH reserve at the energy scale
`state.rowWidth` with the length `length`, the amplifier `ampP` and the loss `loss`, they have at most `Kclass` classes,
and `Kh` times one plus the sum of their values divided by `Z` to the exponent of the HIGH term of the contract is a
HIGH given of the parent. -/
def DepthTwoHighGivenAt
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (g : GeometryAffineLowSchedule) (ap bp bΦ Bmask mesh ε τlow B lossNeeded : ℝ) (hap : 0<ap) (Ψ : 𝓢(ℝ,ℂ))
    (SH : Finset (ℕ×ℕ)) (dh : ℕ) (Kclass Kh : ℝ)
    (η₀ : Character) (Q : Ideal O) (hQM : Q≤M) (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}) (Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(hT : 2<Z^g.τ)(T : Finset α)(θ : T→RayQuotient.Characters M H)(w σ freq : T→ℝ)
    (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))(t height : ℝ),
    (∀i,0≤w i) → (∀i,w i≤ mesh) → 0≤height → (∀i,|freq i|≤height) →
  ∀(state : NaturalState Z Bmask bΦ),state.fixedModulus=internalQ Q η₀ → state.width≤1 →
  ∀(p : Profiles ap bp)(X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂),
    Cycle63.AffineLedger.PlainWindow (length Z X₁) (length Z X₂) (∑i,w i) →
  ∀(v₁ : O)(τT Tz : ℝ),τlow≤τT → PrefixHighPresented (base η₀) τT Z state v₁ Tz →
    ((Ideal.span {v₁}).absNorm:ℝ)≤Z^(B-130) →
  let s:=affineInput M H hH η₀ θ W hW.continuous 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq hσ state p hap
    (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) t X₁ X₂ hX₁ hX₂
  let amp:=Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
    (Cycle63.AffineLedger.originalCell (∑i,w i)))
  ∀(length ampP loss : ℝ),
    Real.logb Z (CenteredMomentAmplificationChildInput.volume s)≤length →
    amp≤ampP → lossNeeded+ε≤loss →
  ∃(unit : Bool→FirstSourceLabel→O)
    (Hb : (b : Bool)→SecondStepHighCount M H hH (extendFixedDictionary (base η₀)) η₀ Z B Tz b v₁ (unit b)),
    (∀b,(Hb b).Pays Cycle63.AffineLedger.q state.rowWidth length ampP loss) ∧
    (∀b,(Fintype.card (Hb b).Class:ℝ)≤Kclass) ∧
    GeometryAffineHighGiven (α:=T) M H hH g η₀ Q hQM hQ72 hβlo hβhi Z hZ hT ap bp s p state.puncture 1
      state.rowWidth amp Ψ (profile_zero_of_pos p hap 0) (profile_zero_of_pos p hap 1) SH dh height
      (Kh*(Z^(-(state.rowWidth+3*g.δ-amp+ε))*(∑b,(Hb b).value)+1))

/-- The statement of the producer of the HIGH given at a parent of the second step. For every character `η₀`, fixed
modulus `internalQ Q η₀` and ledger whose junction is at least the second junction there is a schedule `g` of the
first-level loss unit `μ = geometryLossUnit 1 εaffine`, dictionary rate `δ` and height `g.τ` below half of `τlow`; for
every radial majorant `Ψ` of the contract there are the constants `SH`, `dh` of the given and `Kclass`; then for every
`ε > 0` there is a constant `Kh`, and for all large `Z` the given `DepthTwoHighGivenAt` holds for the heights `τT` of
the presentation at least `τlow`, the label caps `Z^B` and the losses at least `lossNeeded + ε`. The slot widths are at
most the mesh `mesh`, below the common mesh of mask `28` at the loss `μ/8`. -/
def DepthTwoHighGivenStatement
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (εaffine ap bp bΦ Bmask mesh τlow B lossNeeded : ℝ) : Prop :=
  0<εaffine → ∀hap : 0<ap,ap≤1/4 → 1≤bp → 2≤bΦ → 0≤Bmask → Bmask≤20 → 0≤ mesh →
  mesh≤Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8) → 0<τlow →
  ∀(η₀ : Character)(Q : Ideal O)(hQM : Q≤M),internalQ Q η₀≠0 → internalQ Q η₀≠⊤ →
  ∀hQ72 : internalQ Q η₀≤Ideal.span {(72:O)},
  ∀μ : ℝ,μ=geometryLossUnit 1 εaffine →
  ∀[Cycle63.AffineLedger],Cycle63.Arithmetic.q0≤Cycle63.AffineLedger.q →
  ∃g : GeometryAffineLowSchedule,g.μ=μ ∧
    g.δ=geometryFinalDictionaryRate μ 31 3 4 3 130 (3*((Fintype.card α:ℝ)+2)) (Fintype.card α) ∧ 2*g.τ<τlow ∧
  ∀Ψ : 𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) → (∀x,0≤(Ψ x).re) →
  ∃(SH : Finset (ℕ×ℕ))(dh : ℕ)(Kclass : ℝ),∀ε : ℝ,0<ε →
  ∃Kh : ℝ,0≤Kh ∧ ∀ᶠZ : ℝ in atTop,
    DepthTwoHighGivenAt (base:=base) (α:=α) M H hH W hW hWs hβlo hβhi g ap bp bΦ Bmask mesh ε τlow B lossNeeded hap Ψ SH dh
      Kclass Kh η₀ Q hQM hQ72 Z

end
end OAI.SevenEighths.Cycle153RecursiveHighProvider
