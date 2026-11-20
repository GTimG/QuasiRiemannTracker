/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Original aligned pair energy from prices only on its literal canonical
restoration children; finite restoration constants precede all live data. -/
import Candidate.C092.transport.OrderedPairActualRestoredAligned
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.OrderedPairActualRestored
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open HeckeInverseAmplification ProbeHighRowFamily CenteredMomentLattice CenteredMomentEnergyBands
open CenteredMomentCommonMaskEnergy CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentWholeSlotDeletion CenteredMomentFiniteProfileExceptional RayFourExpansion
open QRH.Record1252270103KernelMass QRH.Record1252270103TwoIdeal
open QRH.SilDensitySplit.CubeFree.FP MixedCanonicalSource RestoredRootDictionary RestoredInitialSource
open RepairedSourceSideSupply ReferencePrimeEnclosure
open Candidate.FourthPower.KernelCollisionEnergy
open QRH.SilDensitySplit.CubeFree.FP.RestorationFamily
open QRH.SilDensitySplit.CubeFree.FP.RestorationCollisionEnergy
open QRH.Cycle092.TwistedRawBallRootProducer QRH.Cycle092.PairedRetainedBudget
open QRH.Cycle092.FixedFramePacking QRH.Cycle092.OrderedPairPhase
open QRH.Cycle090 QRH.Cycle092.NativeStrip
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O
local notation "Prime"=>QRH.Record1252270103KernelMass.PrimeIdeal

theorem restored_power_bound (Z ε:ℝ)(hZ:1 ≤ Z)(hε:0 ≤ ε) :
    (4*Z^(2:ℝ))^(ε/8)*Z^(1+ε/2) ≤ (4:ℝ)^(ε/8)*Z^(1+ε) := by
  have hz:0 ≤ Z:=zero_le_one.trans hZ
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) (Real.rpow_nonneg hz _),
    ←Real.rpow_mul hz,mul_assoc,←Real.rpow_add (zero_lt_one.trans_le hZ)]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 4) _)

theorem actual_aligned_of_averaged_family_final (Slot:Type) [Fintype Slot]
    (J degree:ℕ)(W:ℝ→ℂ)(hW:Continuous W)(hWs:Function.support W⊆Set.Icc (1:ℝ) 2)
    (controls:Finset (ℕ×ℕ))(h00:(0,0)∈controls)
    (cRad ξ κ ξsecond εmass ε:ℝ)(hcRad:1 ≤ cRad)(hξ:0<ξ)(hκ:0<κ)
    (hξsecond:0<ξsecond)(hsmall:ξ/2+κ ≤ 22)(hεmass:0<εmass)(hε:0<ε) :
    ∃C:ℝ,∃Cz Ct:RootShape Slot→ℝ,0<C ∧ (∀k,0<Cz k ∧ 0<Ct k) ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(hZ:1<Z)(T:Finset Slot)(M:Id)[NeZero M](Hr:Subgroup (O⧸M)ˣ)
      (hHr:RayOrthogonality.globalUnits M ≤ Hr)
      (base η₁ η₂:Character)(θ:T→RayQuotient.Characters M Hr)(w freq:T→ℝ)
      (hw:∀i,0 ≤ w i)(hwcap:∀i,w i ≤ 1/6)(tMark t₁ t₂:ℝ)
      (p:Profiles (1/4) (9/4))(X₁ X₂ Y₁ Y₂ M₁ M₂ n y l height loss:ℝ),
      sourceY0 ≤ y → y ≤ sourceY → n ≤ sourceRatio*y →
      length Z X₁ ≤ n → length Z X₂ ≤ y → (∑i,w i) ≤ l → l ≤ sourceWidth n y →
      Z^(115/1000:ℝ) ≤ X₁ → Z^(115/1000:ℝ) ≤ X₂ →
      Z^(115/1000:ℝ) ≤ Y₁ → Z^(115/1000:ℝ) ≤ Y₂ → X₁*X₂=Y₁*Y₂ →
      X₁ ≤ M₁ → Y₁ ≤ M₁ → X₂ ≤ M₂ → Y₂ ≤ M₂ → M₁ ≤ Z → M₂ ≤ Z →
      0 ≤ height → loss+εmass ≤ (ε/2) →
    ∀(χ₀:RayCharacter)(Q:Id)(m:O),
      AveragedRestoredFamilyAt T M Hr hHr Z hZ W hW hWs base η₁ η₂ θ w freq hw hwcap
        tMark t₁ t₂ p X₁ X₂ Y₁ Y₂ M₁ M₂ height cRad ξ κ loss ξsecond
        controls degree J Cz Ct χ₀ Q m →
    ∀(rows:Finset FreeRow)(mark:Slot→FreeRow→ℂ),(∀u∈rows,rowNorm u ≤ Z) →
      (∀u∈rows,∀i:T,‖mark i.val u‖=‖normalizedSlot η₁ (fixedBadMask*idealGenerator 1) 1 u.val
        (CenteredMomentPrimeSlot.primePool M Hr 2 (Z^(w i)))
        (fun I=>idealCoeff (relativeCharacter M Hr hHr base (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (33/50) (freq i) I) tMark (Z^(w i))‖) →
      alignedPairEnergyOn T rows η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ Y₁ Y₂ mark ≤
        C*((p.control controls)^2*(1+|t₁|+|t₂|+height)^degree)*Z^(1+ε) := by
  obtain ⟨C,Cz,Ct,hC,hconstants,hbound⟩:=actual_aligned_of_averaged_family Slot J degree W hW hWs
    controls h00 cRad ξ κ ξsecond εmass (ε/2) (ε/8) hcRad hξ hκ hξsecond hsmall hεmass
    (by linarith) (by linarith)
  refine ⟨C*(4:ℝ)^(ε/8),Cz,Ct,mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _),hconstants,?_⟩
  filter_upwards [hbound] with Z hb
  refine ⟨hb.1,?_⟩
  intro hZ T M inst Hr hHr base η₁ η₂ θ w freq hw hwcap tMark t₁ t₂ p X₁ X₂ Y₁ Y₂ M₁ M₂ n y l height loss
    hy0 hy1 hn hxn hxy hsum hl hq₁ hq₂ hq₃ hq₄ hprod hxM₁ hyM₁ hxM₂ hyM₂ hM₁ hM₂ hheight hloss
    χ₀ Q m hprice rows mark hrad hmark
  have hh:=hb.2 hZ T M Hr hHr base η₁ η₂ θ w freq hw hwcap tMark t₁ t₂ p
    X₁ X₂ Y₁ Y₂ M₁ M₂ n y l height loss hy0 hy1 hn hxn hxy hsum hl
    hq₁ hq₂ hq₃ hq₄ hprod hxM₁ hyM₁ hxM₂ hyM₂ hM₁ hM₂ hheight hloss
    χ₀ Q m hprice rows mark hrad hmark
  have hA:0 ≤ (p.control controls)^2*(1+|t₁|+|t₂|+height)^degree:=by positivity
  have hp:=mul_le_mul_of_nonneg_left (restored_power_bound Z ε hZ.le hε.le) (mul_nonneg hC.le hA)
  exact hh.trans (by convert hp using 1 <;> ring)

#print axioms restored_power_bound
#print axioms actual_aligned_of_averaged_family_final
end
end QRH.Cycle092.OrderedPairActualRestored
