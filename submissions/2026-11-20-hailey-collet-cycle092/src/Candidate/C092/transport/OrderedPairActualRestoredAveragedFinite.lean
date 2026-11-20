/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite native source constants before all restored assignments, profiles,
heights, physical rows and actual shortened rectangles. -/
import Candidate.C092.transport.OrderedPairActualRestoredProfiles
import Candidate.C092.transport.PairedRetainedBudgetFinite
import Candidate.C092.transport.FirstRootCompleteCaps
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.OrderedPairActualRestored
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentLattice CenteredMomentEnergyBands CenteredMomentSecondHeightFamily
open CenteredMomentAllocatedNaturalRadial
open RayFourExpansion CenteredMomentNaturalFixedRaySource
open QRH.Record1252270103KernelMass
open QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedCanonicalSource MixedPrincipalAllocations
open MixedOriginalTail MixedOriginalNormCap RepairedSourceSideSupply
open QRH.Cycle090 QRH.Cycle092.NativeStrip
open QRH.Cycle092.TwistedRawBall QRH.Cycle092.TwistedRawBallRootProducer
open QRH.Cycle092.PairedRetainedBudget
open QRH.Cycle092.FixedFramePacking
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O

/-- Actual positive finite source consumer, uniformly across all possible
surviving slot types. The remaining premise is the literal physical price. -/
theorem finite_root_averaged_sides (Slot:Type) [Fintype Slot] (J:ℕ)
    (cRad Cp ξfirst κ ξsecond εmass εout:ℝ)
    (hcRad:1≤cRad) (hCp:0<Cp) (hξfirst:0<ξfirst) (hκ:0<κ)
    (hξsecond:0<ξsecond) (hsmall:ξfirst/2+κ≤22)
    (hεmass:0<εmass) (hεout:0<εout) (η:Character) :
    ∃ C:ℝ,∃ Cz Ct:RootShape Slot→ℝ,
      0<C ∧ (∀ k,0<Cz k ∧ 0<Ct k) ∧
    ∀ᶠ Z:ℝ in atTop,3≤Z ∧
    ∀ (k:RootShape Slot) (η₁ η₂:Character)
      (s:Source (RootSlot k) (1/4) (9/4)) (cover:OriginalEnclosure s),
      s.H=∅ → s.R=1 → s.d=(1,1) →
    ∀ w:RootSlot k→ℝ,(∀ i,0≤w i) → (∀ i,s.P i=Z^(w i)) →
    ∀ n y:ℝ,sourceY0 ≤ y → y ≤ sourceY → n ≤ sourceRatio*y →
      BallCaps s Z n y w →
    ∀ (χ₀:RayCharacter) (Q:Id) (m:O) (A loss:ℝ),0≤A → profileCap s^2≤Cp*A →
      loss+εmass≤εout →
      AveragedRetainedSidesQ s cover w η₁ η₂ η χ₀ Q m (cRad*Z) Z ξfirst κ
        (Z^(8:ℝ)) A loss ξsecond (Cz k) (Ct k) J →
      ∀ rows:Finset O,(∀ z∈rows,z≠0) → (∀ z∈rows,‖eisEmbedding z‖^2≤Z) →
      (∑ z∈rows,‖sourceSignedRow s (by norm_num) (naturalCharacter η z)
        (idealCoeff η₁) (idealCoeff η₂)‖^2)≤C*A*Z^(1+εout) := by
  choose Cf Cz Ct hCf hCz hCt hev using fun k:RootShape Slot=>
    finite_signed_of_averaged_physical_sides (ι:=RootSlot k) (Fintype.card Slot) J
      cRad Cp ξfirst κ ξsecond εmass εout hcRad hCp hξfirst hκ hξsecond hsmall hεmass hεout η
  let C:=1+∑ k:RootShape Slot,Cf k
  have hC:0<C := by
    have hh:=Finset.sum_nonneg (fun k (_:k∈(Finset.univ:Finset (RootShape Slot)))=>(hCf k).le)
    dsimp [C];linarith
  have hkC(k:RootShape Slot):Cf k≤C := by
    have hh:=Finset.single_le_sum (s:=Finset.univ) (f:=Cf) (fun k _=>(hCf k).le) (Finset.mem_univ k)
    dsimp [C];linarith
  refine ⟨C,Cz,Ct,hC,fun k=>⟨hCz k,hCt k⟩,?_⟩
  filter_upwards [Filter.eventually_all.mpr hev,eventually_ge_atTop (3:ℝ)] with Z hz hZ
  refine ⟨hZ,?_⟩
  intro k η₁ η₂ s cover hH hR hd w hw hP n y hy0 hy1 hn caps χ₀ Q m A loss hA hprofile hloss hprice rows hnz hrad
  have hh:=(hz k).2 η₁ η₂ s cover (root_slot_card k) hH hR hd
    caps.floor caps.x₁ caps.x₂ caps.y₁ caps.y₂ caps.slots caps.pool caps.norm caps.volume
    w hw hP n y hy0 hy1 hn caps.originalBox χ₀ Q m A loss hA hprofile hloss hprice rows hnz hrad
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hkC k) hA) (Real.rpow_nonneg (by linarith : 0≤Z) _))

#print axioms finite_root_averaged_sides
end
end QRH.Cycle092.OrderedPairActualRestored
