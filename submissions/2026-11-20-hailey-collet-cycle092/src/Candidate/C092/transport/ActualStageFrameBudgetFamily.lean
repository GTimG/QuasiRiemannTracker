/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A price only on the actual native collision/inverse family. All marks,
prime pools, masks, lengths, colors and independent pitches are literal. -/
import Candidate.C092.transport.ActualStageFrameBudgetRestored
import Candidate.C092.transport.ActualStageFrameBudgetRetained
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open HeckeInverseAmplification ProbeHighRowFamily CenteredMomentLattice
open CenteredMomentCommonMaskEnergy CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional
open RayFourExpansion
open QRH.Record1252270103KernelMass QRH.Record1252270103TwoIdeal
open QRH.SilDensitySplit.CubeFree.FP MixedCanonicalSource RestoredRootDictionary RestoredInitialSource
open RepairedSourceSideSupply
open Candidate.FourthPower.KernelCollisionEnergy
open QRH.SilDensitySplit.CubeFree.FP.RestorationFamily
open QRH.SilDensitySplit.CubeFree.FP.RestorationCollisionEnergy
open QRH.Cycle092.TwistedRawBallRootProducer QRH.Cycle092.PairedRetainedBudget
open QRH.Cycle092.OrderedPairActualRestored
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O
variable {Slot:Type} [Fintype Slot]

def FrameRestoredFamilyAt (T:Finset Slot) (M:Id)[NeZero M](Hr:Subgroup (O⧸M)ˣ)
    (hHr:RayOrthogonality.globalUnits M ≤ Hr)(Z:ℝ)(hZ:1<Z)
    (W:ℝ→ℂ)(hW:Continuous W)(hWs:Function.support W⊆Set.Icc (1:ℝ) 2)
    (base η₁ η₂:Character)(θ:T→RayQuotient.Characters M Hr)(w freq:T→ℝ)
    (hw:∀i,0 ≤ w i)(hwcap:∀i,w i ≤ 1/6)(tMark t₁ t₂:ℝ)(p:Profiles (1/4) (9/4))
    (X₁ X₂ Y₁ Y₂ M₁ M₂ height cRad ξ κ loss ξsecond:ℝ)
    (controls:Finset (ℕ×ℕ))(degree J:ℕ)(Cz Ct:RootShape Slot→ℝ)
    (χ₀:RayCharacter)(Q:Id)(m:O)(Cfee δ mesh cap:ℝ) : Prop :=
  ∀(r:Setoid T)(tc:{q // ¬singletonBlock r q}→primeEnclosure Z)
    (A:Finset {q // singletonBlock r q})(ti:A→primeEnclosure Z),Function.Injective ti →
  ∀d∈divisorPool (KernelRowPools.supportedRectangle (primeEnclosure Z) (9/4) M₁ M₂),
  ∀g:DividedLengths Z X₁ X₂ Y₁ Y₂ d,
    let data:=restoredMarksData M Hr Z hZ W hW hWs base η₁ θ w freq hw hwcap tMark p r tc A ti
    let s:=dividedCanonicalSource M Hr hHr data X₁ X₂ Y₁ Y₂ t₁ t₂ d g
    let cover:=canonicalPairSource_original_enclosure M Hr hHr data _ _ _ _ t₁ t₂
      g.x₁ g.x₂ g.y₁ g.y₂ g.product g.capx₁ g.capx₂ g.capy₁ g.capy₂
    FrameRetainedPrices s cover data.w η₁ η₂ ColoredRootRestore.bareBase χ₀ Q m
      (cRad*Z) Z κ (Z^(8:ℝ)) ξsecond
      ((p.control controls)^2*(1+|t₁|+|t₂|+height)^degree) Cfee δ mesh cap J

end
end QRH.Cycle092.ActualStageFrameBudget
