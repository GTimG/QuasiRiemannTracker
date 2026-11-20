/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite native source constants before all restored assignments, profiles,
heights, physical rows and actual shortened rectangles. -/
import Candidate.C092.transport.OrderedPairActualRestoredProfiles
import Candidate.C092.transport.TwistedRawBallFull
import Candidate.C092.transport.TwistedRawBallRootRows
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
open QRH.Cycle092.FixedFramePacking
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O

/-- The finite genuine colored source consumer at the balanced retained
contract. No selected-assignment multiplicity is added by this wrapper. -/
theorem finite_root_raw_sides (Slot:Type) [Fintype Slot] (J:ℕ)
    (cRad Cp ξ κ εmass εout:ℝ)
    (hcRad:1 ≤ cRad) (hCp:0<Cp) (hξ:0<ξ) (hκ:0<κ)
    (hεmass:0<εmass) (hεout:0<εout) (η:Character) :
    ∃ C:ℝ,0<C ∧ ∀ᶠ Z:ℝ in atTop,3 ≤ Z ∧
    ∀ (k:RootShape Slot) (η₁ η₂:Character)
      (s:Source (RootSlot k) (1/4) (9/4)) (cover:OriginalEnclosure s),
      s.H=∅ → s.R=1 → s.d=(1,1) →
    ∀ (n y:ℝ) (w:RootSlot k→ℝ),BallCaps s Z n y w →
    ∀ A loss:ℝ,0 ≤ A → profileCap s^2 ≤ Cp*A → loss+εmass ≤ εout →
      SummedRetainedRawSides s (by norm_num) (idealCoeff η₁) (idealCoeff η₂) η
        (cRad*Z) Z ξ κ (Z^(8:ℝ)) A loss J →
    ∀ rows:Finset O,(∀z∈rows,z≠0) → (∀z∈rows,‖eisEmbedding z‖^2 ≤ Z) →
      (∑z∈rows,‖sourceSignedRow s (by norm_num) (naturalCharacter η z)
        (idealCoeff η₁) (idealCoeff η₂)‖^2) ≤ C*A*Z^(1+εout) := by
  choose Cf hCf hev using fun k:RootShape Slot=>
    TwistedRawBall.fullBallCost_of_raw_sides (ι:=RootSlot k) (Fintype.card Slot) J
      cRad Cp ξ κ εmass εout hcRad hCp hξ hκ hεmass hεout η
  let C:=1+∑k:RootShape Slot,Cf k
  have hC:0<C := by
    have hh:=Finset.sum_nonneg (fun k (_:k∈(Finset.univ:Finset (RootShape Slot)))=>(hCf k).le)
    dsimp [C];linarith
  have hkC(k:RootShape Slot):Cf k ≤ C := by
    have hh:=Finset.single_le_sum (s:=Finset.univ) (f:=Cf) (fun k _=>(hCf k).le) (Finset.mem_univ k)
    dsimp [C];linarith
  refine ⟨C,hC,?_⟩
  filter_upwards [Filter.eventually_all.mpr hev,eventually_ge_atTop (3:ℝ)] with Z hz hZ
  refine ⟨hZ,?_⟩
  intro k η₁ η₂ s cover hH hR hd n y w caps A loss hA hprofile hloss hprice rows hnz hrad
  have hball:=(hz k).2 η₁ η₂ s (root_slot_card k) hd
    caps.floor caps.x₁ caps.x₂ caps.y₁ caps.y₂ caps.slots caps.pool caps.norm caps.volume
    A loss hA hprofile hloss hprice
  have hrow:=finite_signed_rows_le_fixed_ball s (by norm_num) (by norm_num) cover hH hd hR
    (idealCoeff η₁) (idealCoeff η₂) η (cRad*Z)
    (mul_pos (zero_lt_one.trans_le hcRad) (by linarith : 0<Z)) rows hnz
    (fun z hzrow=>(hrad z hzrow).trans (le_mul_of_one_le_left (by linarith : 0 ≤ Z) hcRad))
  exact (hrow.trans hball).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hkC k) hA) (Real.rpow_nonneg (by linarith : 0 ≤ Z) _))

#print axioms finite_root_raw_sides
end
end QRH.Cycle092.OrderedPairActualRestored
