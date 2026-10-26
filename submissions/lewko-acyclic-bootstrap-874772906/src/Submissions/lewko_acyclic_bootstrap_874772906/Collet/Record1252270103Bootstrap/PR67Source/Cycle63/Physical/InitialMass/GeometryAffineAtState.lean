import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineMainHighBound
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.AffineProfileZero
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryFinalLossParameters
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineExceptionalGates
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialSourceReduction
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondCanonicalScalar
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondPhysicalBlock
open Cycle63Moment Cycle63Moment.LowBranch
open ConcretePrimeRowBridge CompletedGauss
open Cycle63FinalNatural CenteredMomentDivisorExtraction CenteredMomentCommonRawScale
open CenteredMomentNaturalFixedRaySource CenteredMomentAllocatedRayDictionary
open CenteredMomentEnergyState CenteredMomentEnergyBands Cycle63InitialSource
open CenteredMomentFirstAmplificationChoice CenteredMomentSecondHeightFamily
open CenteredMomentInductionEnergy CenteredMomentPrimeSlot

variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance affineAtStateFiniteQuotient : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

variable [Cycle63.AffineLedger] in
/-- The HIGH rows of the second transform of the parent `s` with puncture `R`, seed `seed` and radial scale `Z^Mrow`
are given by one real `EH`: at every reflection, every geometry bin and every first height the canonical bound holds
with the constant `EH` times the profile control of `SH` squared, the side factor and the height weight of degree
`dh`. -/
def GeometryAffineHighGiven
    (g : GeometryAffineLowSchedule) (η₀ : Character) (Q : Ideal O) (hQM : Q≤M)
    (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (Z : ℝ) (hZ : 1<Z) (hT : 2<Z^g.τ) (ap bp : ℝ) (s : Input α) (p : Profiles ap bp)
    (R seed : Ideal O) (Mrow amp : ℝ) (Ψ : 𝓢(ℝ,ℂ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (SH : Finset (ℕ×ℕ)) (dh : ℕ) (height EH : ℝ) : Prop :=
  ∀(reflected : Bool),∀key∈commonGeometryBins s R seed (Z^Mrow) Z (g.μ/64),
  ∀(firstHeight : ℝ)(χ₀ : RayCharacter),
    GeometryAffineMainCanonicalHighBound M H hH g η₀ Q hQM hQ72 hβlo hβhi Z hZ hT ap bp reflected s R seed Mrow amp
      firstHeight key Ψ χ₀ hz₁ hz₂
      (EH*(p.control SH)^2*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card α) 1 ap ap) key*(1+|firstHeight|+height)^dh) dh

variable [Cycle63.AffineLedger] in
/-- The required moment at one natural state of the base `Z`, in the unit of the ledger: for a subset `T` of the slots,
the energy of the state with the plain scales `X₁`, `X₂` is at most the old moment `Z^(1+ε)` plus a term linear in the
HIGH part of the second transform. The state has fixed modulus `internalQ Q η₀` and width at most one, its plain
lengths lie in the window of the ledger, and their overshoot over the unit, with the slots priced at `slotPrice`, is at
most `7/1000`. The plain profiles have the support `[ap, bp]`. The HIGH part is given
by the real `EH` (`GeometryAffineHighGiven`); `SH` and `dh` are the constants of the given. -/
def GeometryAffineAtState
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (g : GeometryAffineLowSchedule) (ap bp bΦ Bmask mesh ε : ℝ) (hap : 0<ap) (Ψ : 𝓢(ℝ,ℂ))
    (SH : Finset (ℕ×ℕ)) (dh degree : ℕ) (S : Finset (ℕ×ℕ)) (C Chigh : ℝ)
    (η₀ : Character) (Q : Ideal O) (hQM : Q≤M) (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}) (Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(hT : 2<Z^g.τ)(T : Finset α)(θ : T→RayQuotient.Characters M H)(w σ freq : T→ℝ)
    (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))(t height : ℝ),
    (∀i,0≤w i) → (∀i,w i≤ mesh) → 0≤height → (∀i,|freq i|≤height) →
  ∀(state : NaturalState Z Bmask bΦ),state.fixedModulus=internalQ Q η₀ → state.width≤1 →
  ∀(p : Profiles ap bp)(X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂),
    Cycle63.AffineLedger.PlainWindow (length Z X₁) (length Z X₂) (∑i,w i) →
    length Z X₁+length Z X₂+6*Cycle63.Optimization.slotPrice*(∑i,w i)≤1+7/1000 →
  ∀EH : ℝ,0≤EH →
  let s:=affineInput M H hH η₀ θ W hW.continuous 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq hσ state p hap
    (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) t X₁ X₂ hX₁ hX₂
  let amp:=Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
    (Cycle63.AffineLedger.originalCell (∑i,w i)))
  GeometryAffineHighGiven (α:=T) M H hH g η₀ Q hQM hQ72 hβlo hβhi Z hZ hT ap bp s p state.puncture 1 state.rowWidth
    amp Ψ (profile_zero_of_pos p hap 0) (profile_zero_of_pos p hap 1) SH dh height EH →
  energy state.character state.mask 1 t (p.profile 0) (p.profile 1)
    (fun i : T=>primePool M H 2 (Z^(w i)))
    (fun (i : T) I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
    (fun i : T=>Z^(w i)) X₁ X₂ state.radial.keep state.radial.profile state.radial.scale≤
  C*diagonalControl state.radial.profile*(p.control S)^2*(1+|t|+height)^degree*
    (Z^(1+ε)+Chigh*Z^(state.rowWidth+3*g.δ-amp+ε)*EH)

/-- The statement of the generic step, for a schedule `g` of loss unit `geometryLossUnit 1 εaffine` and dictionary rate
`δ`: there is one radial majorant `Ψ`, for all ledgers that delete their LOW children into the old region; for every
fixed modulus `internalQ Q η₀` and after the constants `SH`, `dh` of the given HIGH part, there are the degree and the
source set of the profile control and the constants `C`, `Chigh`; and for all large `Z` the moment
`GeometryAffineAtState` holds. The plain profiles have the support `[ap, bp]` with `ap ≤ 1/4` and `1 ≤ bp`. The state
mask is at most `Z^20`, and the slot widths are at most the mesh `mesh`, which is below half the amplifier floor of the
ledger, below the common mesh of mask `28 + Bmask` at the loss `g.μ/8` of the schedule, and below the common mesh of
mask `Bmask` at half the loss `ε` of the old moment. -/
def GeometryAffineAtStateStatement
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (g : GeometryAffineLowSchedule) (εaffine ap bp bΦ Bmask mesh ε : ℝ) : Prop :=
  0<εaffine → g.μ=geometryLossUnit 1 εaffine →
  g.δ=geometryFinalDictionaryRate g.μ 31 3 4 3 130 (3*((Fintype.card α:ℝ)+2)) (Fintype.card α) →
  ∀hap : 0<ap,ap≤1/4 → 1≤bp → 0<bΦ → 0≤Bmask → Bmask≤20 → 0≤ mesh → 0<ε →
  ∃Ψ : 𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧ (∀x,0≤(Ψ x).re) ∧
  ∀[Cycle63.AffineLedger][Cycle63.AffineLedger.DeletesIntoOldRegion],mesh<Cycle63.AffineLedger.amplifierFloor/2 →
  128*g.μ≤Cycle63.AffineLedger.lowReserve →
  mesh≤Cycle25.Energy.commonMesh 2 (28+Bmask) 1 (g.μ/8) →
  mesh≤Cycle25.Energy.commonMesh 1 Bmask 1 (ε/2) →
  ∀(η₀ : Character)(Q : Ideal O)(hQM : Q≤M),internalQ Q η₀≠0 → internalQ Q η₀≠⊤ →
  ∀hQ72 : internalQ Q η₀≤Ideal.span {(72:O)},
  ∀(SH : Finset (ℕ×ℕ))(dh : ℕ),∃(degree : ℕ)(S : Finset (ℕ×ℕ)),SH⊆S ∧ dh≤degree ∧
  ∃C Chigh : ℝ,0<C ∧ 0≤Chigh ∧ ∀ᶠZ : ℝ in atTop,
    GeometryAffineAtState (α:=α) M H hH W hW hWs hβlo hβhi g ap bp bΦ Bmask mesh ε hap Ψ SH dh degree S C Chigh η₀ Q hQM
      hQ72 Z

variable [Cycle63.AffineLedger] in
/-- The literal affine input of a natural state: its dictionary match, the conductor fit at the row width of the state,
the slot window and the plane in its own slot logarithms, and its original cell. -/
theorem affine_state_bundle_data {κ : Type} [Fintype κ] [DecidableEq κ]
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (η₀ : Character) (θ : κ→RayQuotient.Characters M H) (w σ freq : κ→ℝ)
    (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50)) {Z Bmask bΦ ap bp : ℝ} (state : NaturalState Z Bmask bΦ)
    (p : Profiles ap bp) (hap : 0<ap) (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hZ : 1<Z)
    (hwin : Cycle63.AffineLedger.PlainWindow (length Z X₁) (length Z X₂) (∑i,w i)) :
    let s:=affineInput M H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p hap
      (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) t X₁ X₂ hX₁ hX₂
    Matches M H hH s η₀ θ w σ freq W 2 Z ∧
      state.rowWidth+Real.logb Z (s.η.modulus.absNorm:ℝ)≤ state.width ∧
      (Cycle63.AffineLedger.slotFloor≤∑j,Real.logb Z (s.P j) ∧
        (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop) ∧
      length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤
        Cycle63.AffineLedger.B ∧
      Cycle63.AffineLedger.cellUpper (Cycle63.AffineLedger.originalCell (∑i,w i))=
        Cycle63.AffineLedger.cellUpper (Cycle63.AffineLedger.originalCell (∑j,Real.logb Z (s.P j))) := by
  intro s
  have hmatch : Matches M H hH s η₀ θ w σ freq W 2 Z := by constructor <;> intros <;> rfl
  have hsum : (∑j,Real.logb Z (s.P j))=∑i,w i := by
    refine Finset.sum_congr rfl (fun j _=>?_)
    rw [hmatch.scale j,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  have hηs : s.η=state.character := rfl
  have hN1 : (1:ℝ)≤(s.η.modulus.absNorm:ℝ) := by
    exact_mod_cast norm_at_least_one s.η.modulus s.η.modulus_ne_bot
  refine ⟨hmatch,?_,?_,?_,by rw [hsum]⟩
  · have hmod : Real.logb Z (s.η.modulus.absNorm:ℝ)≤ state.characterWidth := by
      rw [Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hN1)]
      rw [hηs]
      exact state.modulus_bound
    unfold NaturalState.width
    linarith
  · rw [hsum]; exact ⟨hwin.slots_ge,hwin.slots_le⟩
  · rw [hsum]; exact hwin.plane

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
