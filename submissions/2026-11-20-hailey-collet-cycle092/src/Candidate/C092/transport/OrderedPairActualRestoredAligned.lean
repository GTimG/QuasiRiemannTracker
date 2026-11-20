/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Original aligned pair energy from prices only on its literal canonical
restoration children; finite restoration constants precede all live data. -/
import Candidate.C092.transport.OrderedPairActualRestoredFamily
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

set_option maxHeartbeats 500000 in
theorem actual_aligned_of_averaged_family (Slot:Type) [Fintype Slot]
    (J degree:ℕ)(W:ℝ→ℂ)(hW:Continuous W)(hWs:Function.support W⊆Set.Icc (1:ℝ) 2)
    (controls:Finset (ℕ×ℕ))(h00:(0,0)∈controls)
    (cRad ξ κ ξsecond εmass εout δ:ℝ)(hcRad:1 ≤ cRad)(hξ:0<ξ)(hκ:0<κ)
    (hξsecond:0<ξsecond)(hsmall:ξ/2+κ ≤ 22)(hεmass:0<εmass)(hεout:0<εout)(hδ:0<δ) :
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
      0 ≤ height → loss+εmass ≤ εout →
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
        C*(4*Z^(2:ℝ))^δ*((p.control controls)^2*(1+|t₁|+|t₂|+height)^degree)*Z^(1+εout) := by
  let B:=RestoredRootSource.slotBound W hW hWs
  have hB:1 ≤ B:=(RestoredRootSource.slotBound_spec W hW hWs).1
  choose Cr hCr hrestore using fun T:Finset Slot=>ColoredRootRestore.actual_aligned_restoration T B δ hB hδ
  let Crestore:=1+∑T:Finset Slot,Cr T
  have hCrestore:0<Crestore:=by
    have hh:=Finset.sum_nonneg (fun T (_:T∈(Finset.univ:Finset (Finset Slot)))=>(hCr T).le)
    dsimp [Crestore];linarith
  have hCrC(T:Finset Slot):Cr T ≤ Crestore:=by
    have hh:=Finset.single_le_sum (s:=Finset.univ) (f:=Cr) (fun T _=>(hCr T).le) (Finset.mem_univ T)
    dsimp [Crestore];linarith
  obtain ⟨Cleaf,Cz,Ct,hCleaf,hConstants,hleaf⟩:=actual_canonical_divided_averaged_leaf Slot J degree
    W hW hWs controls h00 cRad ξ κ ξsecond εmass εout hcRad hξ hκ hξsecond hsmall hεmass hεout
    ColoredRootRestore.bareBase
  refine ⟨Crestore*Cleaf,Cz,Ct,mul_pos hCrestore hCleaf,hConstants,?_⟩
  filter_upwards [hleaf] with Z hb
  refine ⟨hb.1,?_⟩
  intro hZ T M inst Hr hHr base η₁ η₂ θ w freq hw hwcap tMark t₁ t₂ p X₁ X₂ Y₁ Y₂ M₁ M₂ n y l height loss
    hy0 hy1 hn hxn hxy hsum hl hq₁ hq₂ hq₃ hq₄ hprod hxM₁ hyM₁ hxM₂ hyM₂ hM₁ hM₂ hheight hloss
    χ₀ Q m hprice rows mark hrad hmark
  have hz:0<Z:=zero_lt_one.trans hZ
  have hq:0<Z^(115/1000:ℝ):=Real.rpow_pos_of_pos hz _
  have hx₁:=hq.trans_le hq₁
  have hx₂:=hq.trans_le hq₂
  have hy₁:=hq.trans_le hq₃
  have hy₂:=hq.trans_le hq₄
  let Amp:=(p.control controls)^2*(1+|t₁|+|t₂|+height)^degree
  have hAmp:0 ≤ Amp:=by dsimp [Amp];positivity
  let E:=Cleaf*Amp*Z^(1+εout)
  have hE:0 ≤ E:=by dsimp [E];positivity
  have hXcap:1 ≤ 4*Z^(2:ℝ):=by nlinarith [Real.one_le_rpow hZ.le (by norm_num : (0:ℝ) ≤ 2)]
  have hS:∀P∈primeEnclosure Z,Supported P.val ∧ (P.val.absNorm:ℝ) ≤ 4*Z^(2:ℝ):=by
    intro P hP
    exact enclosure_bound _ P hP
  have hpool:∀i:T,supportedPool (CenteredMomentPrimeSlot.primePool M Hr 2 (Z^(w i)))⊆primeValues (primeEnclosure Z):=by
    intro i
    change _⊆primeValues (enclosure (4*Z^(2:ℝ)))
    rw [enclosure_values]
    exact canonical_pool_enclosed M Hr Z (w i) 2 4 hZ.le ((hwcap i).trans (by norm_num)) (by norm_num)
  have hweights:∀i:T,∀I:Id,I∈CenteredMomentPrimeSlot.primePool M Hr 2 (Z^(w i)) →
      ‖HeckePrimeAnnular.annularWeight W (Z^(w i)) (33/50) (freq i) I‖ ≤ B:=by
    intro i I hI
    exact (RestoredRootSource.slotBound_spec W hW hWs).2 (freq i) (I.absNorm/(Z^(w i)))
  have henclose:∀I:Id,Supported I → ((I.absNorm:ℝ) ≤ (9/4)*M₁ ∨ (I.absNorm:ℝ) ≤ (9/4)*M₂) →
      primeValues (primeEnclosure Z) ⊇ primeSupport I:=by
    intro I hI hlen
    apply support_enclosed _ I hI
    have hZZ:Z ≤ Z^(2:ℝ):=by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num : (1:ℝ) ≤ 2)
    rcases hlen with hlen|hlen <;> nlinarith
  have hroot:=(hrestore T) (4*Z^(2:ℝ)) hXcap (primeEnclosure Z) hS M Hr hHr base η₁ η₂ θ rows
    (fun i=>CenteredMomentPrimeSlot.primePool M Hr 2 (Z^(w i)))
    (fun i I=>HeckePrimeAnnular.annularWeight W (Z^(w i)) (33/50) (freq i) I)
    (fun i=>Z^(w i)) hpool (fun i=>Real.rpow_pos_of_pos hz _)
    (fun i I hI=>canonical_pool_norm_le M Hr _ (Real.rpow_pos_of_pos hz _) I hI) hweights
    mark tMark (p.profile 0) (p.profile 1) (1/4) (9/4) (by norm_num) (by norm_num)
    (p.support 0) (p.support 1) ((p.profile 0).smooth ⊤) ((p.profile 1).smooth ⊤)
    t₁ t₂ M₁ M₂ X₁ X₂ Y₁ Y₂ E hx₁ hx₂ hy₁ hy₂ hprod.symm hxM₁ hxM₂ hyM₁ hyM₂ hE henclose hmark
  dsimp only at hroot
  have henergy:alignedPairEnergyOn T rows η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ Y₁ Y₂ mark ≤
      Cr T*(4*Z^(2:ℝ))^δ*E:=by
    apply hroot
    intro r tc A ti hti d hd
    let g:=divided_lengths Z X₁ X₂ Y₁ Y₂ M₁ M₂ (primeEnclosure Z) d
      hx₁ hx₂ hy₁ hy₂ hprod hxM₁ hyM₁ hxM₂ hyM₂ hM₁ hM₂ hd
    let data:=restoredMarksData M Hr Z hZ W hW hWs base η₁ θ w freq hw hwcap tMark p r tc A ti
    have hsum':(∑i:remainingSet r A,w i.val) ≤ l:=
      (width_injected (⟨Subtype.val,Subtype.val_injective⟩:remainingSet r A↪T) w hw).trans hsum
    have hp:=hprice r tc A ti hti d hd g
    have hbound:=hb.2 (⟨T,remainingSet r A⟩:RootShape Slot) M Hr hHr data rfl rfl
      (primeEnclosure Z) d X₁ X₂ Y₁ Y₂ M₁ M₂ n y l t₁ t₂ height loss
      hy0 hy1 hn hxn hxy hsum' hl hq₁ hq₂ hq₃ hq₄ hprod hxM₁ hyM₁ hxM₂ hyM₂ hM₁ hM₂ hd hheight hloss
      g.x₁ g.x₂ g.y₁ g.y₂ g.product g.capx₁ g.capx₂ g.capy₁ g.capy₂ η₁ η₂ χ₀ Q m hp rows hrad
    let V₁:=normPowerProfile (p.profile 0) (1/4) (9/4) (by norm_num)
      (p.support 0) ((p.profile 0).smooth ⊤) t₁
    let V₂:=normPowerProfile (p.profile 1) (1/4) (9/4) (by norm_num)
      (p.support 1) ((p.profile 1).smooth ⊤) t₂
    change (∑u∈rows,‖actualRestoredRow M Hr hHr Z W base η₁ θ w freq tMark r tc A ti
      (ColoredRootRestore.bareCharacter u.val) (idealCoeff η₁) (idealCoeff η₂) V₁ V₂
        (X₁/d.1.absNorm) (X₂/d.2.absNorm)-
      actualRestoredRow M Hr hHr Z W base η₁ θ w freq tMark r tc A ti
      (ColoredRootRestore.bareCharacter u.val) (idealCoeff η₁) (idealCoeff η₂) V₁ V₂
        (Y₁/d.1.absNorm) (Y₂/d.2.absNorm)‖^2) ≤ E
    apply (le_of_eq ?_).trans hbound
    apply Finset.sum_congr rfl
    intro u hu
    rw [actual_restored_signed_source M Hr hHr Z hZ W hW hWs base η₁ θ w freq hw hwcap tMark p r tc A ti
      (ColoredRootRestore.bareCharacter u.val) (idealCoeff η₁) (idealCoeff η₂)
      (natural_character_off_supported ColoredRootRestore.bareBase u.val u.property.1)
      _ _ _ _ t₁ t₂ g.x₁ g.x₂ g.y₁ g.y₂ g.product g.capx₁ g.capx₂ g.capy₁ g.capy₂]
    rfl
  apply henergy.trans
  have hscale:0 ≤ (4*Z^(2:ℝ))^δ:=Real.rpow_nonneg (by positivity) _
  have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hCrC T) hscale) hE
  convert hh using 1 <;> dsimp [E,Amp] <;> ring

#print axioms actual_aligned_of_averaged_family
end
end QRH.Cycle092.OrderedPairActualRestored
