/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine native pointwise retained price specializes to every original
collision/inverse child in CenteredFramesAt, with the original quantifiers. -/
import Candidate.C092.transport.ActualStageFrameBudgetEarlierFamilyCaps
import Candidate.C092.transport.ActualStageFrameBudgetPointwise
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open QRH.Record1252270103KernelMass QRH.Record1252270103TwoIdeal
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedCanonicalSource
open NativeMaskedEnergy RestoredRootDictionary RestoredInitialSource
open QRH.SilDensitySplit.CubeFree.FP.RestorationFamily
open QRH.SilDensitySplit.CubeFree.FP.RestorationCollisionEnergy
open Candidate.FourthPower.KernelCollisionEnergy Candidate.FourthPower.NativeFiniteHoles
open QRH.Cycle090 QRH.Cycle092.NativeStrip QRH.Cycle092.ReferenceShortP3
open QRH.Cycle092.OrderedPairActualRestored QRH.Cycle092.FixedFramePacking
open QRH.Cycle092.TwistedRawBallRootProducer QRH.Cycle092.PairedRetainedBudget
open RepairedSourceSideSupply
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O
variable {Slot:Type} [Fintype Slot] [DecidableEq Slot]

/-- All geometric intake is proved on the original physical arrays. The
bank and its analytic parameters are fixed before Cz/Ct and the live scale;
only its genuine scale-At packet is used at that scale. -/
theorem earlier_centered_frames_of_bank
    (n y l δ mesh ξsecond bPhi ε loss:ℝ)(hδ:0<δ)
    (hy0:sourceY0 ≤ y)(hy1:y ≤ sourceY)(hn:n ≤ sourceRatio*y)
    (hl:l ≤ sourceWidth n y)(hmesh:mesh ≤ 1/6)
    (M:Id)[NeZero M](Hr:Subgroup (O⧸M)ˣ)(hHr:RayOrthogonality.globalUnits M ≤ Hr)
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(hWs:Function.support W⊆Set.Icc (1:ℝ) 2)
    (η₁ η₂ η₀₁ η₀₂:Character)(Q₁ Q₂ Q:Id)
    (hQ:Q ≤ M)(hQ0:Q≠0)(hQt:Q≠⊤)(hQ72:Q ≤ Ideal.span {(72:O)})
    (hQbase:Q ≤ (η₀₁.product η₁.inverse).modulus)
    (Kslot:ℝ)(hslots:RestoredRootSource.slotBound W hW.continuous hWs ≤ Kslot)
    (bank:NativePhysicalBank (Fintype.card Slot))(hFee:bank.Fee)
    (horizon:RetainedBankHorizon (Fintype.card Slot) n y l δ mesh ξsecond hδ)
    (Cz Ct:RootShape Slot→ℝ) :
    ∀ᶠ Z:ℝ in atTop,∀hZ:1<Z,
      bank.At (fun k=>frameData (Fintype.card Slot) k.val M Hr hHr W hW hWs
        (η₀₁.product η₁.inverse) Q hQ hQ0 hQt hQ72 hQbase)
        ColoredRootRestore.bareBase η₁ η₂ Q mesh δ n y Kslot Z hδ →
      CenteredFramesAt M Hr hHr n y l W hW.continuous hWs bPhi mesh ε Z hZ hmesh
        η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ bank.degree bank.controls bank.J 1 δ δ loss ξsecond
        Cz Ct Q bank.totalFee (10*δ) := by
  filter_upwards [horizon,earlier_divided_caps (Fintype.card Slot)] with Z hpoint hcaps
  intro hZ hAt
  intro T θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw hwm hσ₁lo hσ₁hi hσ₂lo hσ₂hi
    hheight hv₁ hv₂ hsum p X₁ X₂ hX₁ hX₂ hxn hxy rows mark hk₁ hk₂ hrad hm₁ hm₂ hlong₁ hlong₂
  have hshort:shortWidth=(115/1000:ℝ):=by norm_num [shortWidth]
  rw [hshort]
  intro r tc A ti hinj d hd g
  dsimp only
  let data:=restoredMarksData M Hr Z hZ W hW.continuous hWs η₀₁ η₁
    (fun i:T=>θ₁ i.val) (fun i:T=>w i.val) (fun i:T=>v₁ i.val)
    (fun i=>hw i.val) (fun i=>(hwm i.val).trans hmesh) t₁ p r tc A ti
  have intake:=earlier_restored_intake M Hr Z hZ W hW hWs η₀₁ η₁ T θ₁ w v₁
    mesh height l t₁ Kslot hw hwm hmesh hv₁ hsum hslots p r tc A ti
  change EarlierRestoredIntake M Hr data (Fintype.card Slot) mesh height l t₁ Kslot at intake
  have hcap:=hcaps.2 (remainingSet r A) M Hr hHr data rfl intake.count n y l X₁ X₂ t₁ t₂
    hy0 hy1 hn hl intake.width hX₁ hX₂ hxn hxy hlong₁ hlong₂
  rw [hshort] at hcap
  have hcapActual:=hcap d hd g
  have href:=earlier_reference_bounds Z n y X₁ X₂ hZ hy1 hn hX₁ hX₂ hxn hxy hlong₁ hlong₂
  rw [hshort] at href
  have hmins:∀X∈({X₁,X₂,Z^(115/1000:ℝ),X₁*X₂/Z^(115/1000:ℝ)}:Finset ℝ),Z^(115/1000:ℝ) ≤ X:=by
    intro X hX
    simp only [Finset.mem_insert,Finset.mem_singleton] at hX
    rcases hX with rfl|rfl|rfl|rfl
    · simpa only [hshort] using hlong₁.le
    · simpa only [hshort] using hlong₂.le
    · exact le_rfl
    · exact href.2.2.2.2.2.2.1
  have hdcap:=root_divisor_caps (primeEnclosure Z) (9/4)
    (max X₁ (Z^(115/1000:ℝ))) (max X₂ (X₁*X₂/Z^(115/1000:ℝ))) hd
  have hd₁:d.1≠0:=by
    intro h
    have hc:=hdcap.1
    rw [h] at hc
    norm_num at hc
  have hd₂:d.2≠0:=by
    intro h
    have hc:=hdcap.2.1
    rw [h] at hc
    norm_num at hc
  have hp:=hpoint.2 (remainingSet r A) M Hr hHr data rfl intake.smooth intake.Lcap intake.count
    X₁ X₂ t₁ t₂ d hd₁ hd₂ g hxn hxy intake.width hmins hcapActual height hheight
    intake.wmesh intake.frequency intake.holes intake.pitch Q hQ hQ0 hQt hQ72 hQbase
    η₁ η₂ Kslot intake.slots bank hFee hAt Z le_rfl
  convert hp using 1 <;> first | rfl | simp only [one_mul]

#print axioms earlier_centered_frames_of_bank
end
end QRH.Cycle092.ActualStageFrameBudget
