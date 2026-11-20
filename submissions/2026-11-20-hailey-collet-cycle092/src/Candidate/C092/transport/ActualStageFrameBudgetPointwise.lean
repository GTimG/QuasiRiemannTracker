/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual pointwise interface between the native finite physical bank and
the original collision/inverse family. Its supplier is proved in Dispatch. -/
import Candidate.C092.transport.ActualStageFrameBudgetPhysicalBank
import Candidate.C092.transport.ActualStageFrameBudgetFamily
import Candidate.C092.transport.FirstRootCompleteCaps
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion ConcretePrimeRowBridge
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open QRH.Record1252270103KernelMass QRH.Record1252270103TwoIdeal
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyBands
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedInnerExceptionalBlock
open QRH.Cycle092.NativeStrip QRH.Cycle090
open QRH.Cycle092.OrderedPairActualRestored QRH.Cycle092.FixedFramePacking
open QRH.Cycle092.TwistedRawBallRootProducer QRH.Cycle092.PairedRetainedBudget
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O

/-- One elementary geometry horizon, uniform before every ray, actual
restored assignment and positive fee. At is the exact already-proved native
fixed/filled/exhausted packet; Fee is its homogeneous numerical normalization. -/
def RetainedBankHorizon (N:ℕ)(n y l δ mesh ξsecond:ℝ)(hδ:0 < δ) :Prop:=
  ∀ᶠZ:ℝ in atTop,1<Z ∧
  ∀(ι:Type)[Fintype ι](M:Id)[NeZero M](Hr:Subgroup (O⧸M)ˣ)
    (hHr:RayOrthogonality.globalUnits M ≤ Hr)(r:RestoredRootSource.Data M Hr ι)
    (hZr:r.Z=Z)(hW:ContDiff ℝ ∞ r.W)(hL:r.Lcap=8),
    Fintype.card ι ≤ N →
  ∀(X₁ X₂ t₁ t₂:ℝ)(d:IdealPair),d.1≠0 → d.2≠0 →
  ∀g:DividedLengths r.Z X₁ X₂ (r.Z^(115/1000:ℝ)) (X₁*X₂/r.Z^(115/1000:ℝ)) d,
    length r.Z X₁ ≤ n → length r.Z X₂ ≤ y → (∑i,r.w i) ≤ l →
    (∀X∈({X₁,X₂,r.Z^(115/1000:ℝ),X₁*X₂/r.Z^(115/1000:ℝ)}:Finset ℝ),r.Z^(115/1000:ℝ) ≤ X) →
  let s:=dividedCanonicalSource M Hr hHr r X₁ X₂ (r.Z^(115/1000:ℝ))
    (X₁*X₂/r.Z^(115/1000:ℝ)) t₁ t₂ d g
  let cover:=canonicalPairSource_original_enclosure M Hr hHr r _ _ _ _ t₁ t₂
    g.x₁ g.x₂ g.y₁ g.y₂ g.product g.capx₁ g.capx₂ g.capy₁ g.capy₂
  BallCaps s r.Z n y r.w →
  ∀height:ℝ,0 ≤ height → (∀i,r.w i ≤ mesh) → (∀i,|r.freq i| ≤ height) →
    (∀i,(r.R₀ i).card ≤ 2*N) → r.t=t₁ →
  ∀(Q:Id)(hQ:Q ≤ M)(hQ0:Q≠0)(hQt:Q≠⊤)(hQ72:Q ≤ Ideal.span {(72:O)})
    (hQbase:Q ≤ r.η₀.modulus)(ω₁ ω₂:Character)(Kslot:ℝ),
    RestoredRootSource.slotBound r.W r.hW r.hWs ≤ Kslot →
  ∀bank:NativePhysicalBank N,bank.Fee →
    bank.At (fun k=>frameData N k.val M Hr hHr r.W hW r.hWs r.η₀ Q hQ hQ0 hQt hQ72 hQbase)
      ColoredRootRestore.bareBase ω₁ ω₂ Q mesh δ n y Kslot r.Z hδ →
  ∀Kroot:ℝ,r.Z ≤ Kroot →
    FrameRetainedPrices s cover r.w ω₁ ω₂ ColoredRootRestore.bareBase 1 Q fixedBadMask
      Kroot r.Z δ (r.Z^(8:ℝ)) ξsecond
      ((r.p.control bank.controls)^2*(1+|t₁|+|t₂|+height)^bank.degree)
      bank.totalFee (10*δ) mesh (sourceWidth n y) bank.J

end
end QRH.Cycle092.ActualStageFrameBudget
