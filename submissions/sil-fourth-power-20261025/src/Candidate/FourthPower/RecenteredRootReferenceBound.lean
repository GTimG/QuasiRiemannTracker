/- Copyright (c) 2026 Sil. Apache-2.0.
The actual kept root reference is supplied by the existing homogeneous
two-orientation theorem. No reference-energy estimate is an input.

-/
import Candidate.FourthPower.RecenteredRootReferenceCaps
import Candidate.FourthPower.MixedFirstReferenceOrientation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RecenteredRootReferenceBound
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open ConcretePrimeRowBridge ConcreteTraceCRT CompletedGauss
open QRH.Record1252270103KernelMass
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentUncenteredTerminal
open CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonMaskEnergy CenteredMomentSecondHeightFamily CenteredMomentAllocatedNaturalRadial
open CenteredMomentNaturalFixedRaySource CenteredMomentDetectorEnergyInitialState
open CenteredMomentOriginalRadialComparison
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedCanonicalSource
open MixedFirstReferenceDispatch MixedFirstReferenceEnergy MixedFirstReferenceOrientation
open RestoredRootDictionary RestoredRootEnergy RestoredInitialSource NativeMaskedEnergy
open RecenteredRootSetup RecenteredRootRows RecenteredRootReferenceDictionary
open RecenteredRootReferenceEvent RecenteredRootReferenceCaps
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ:Type*} : DecidableEq κ := Classical.decEq _
variable {α:Type u}[Fintype α]
variable (M:Id)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M ≤ H)

private theorem ordinary_enclosure_caps (s:Setup M H α)
    (hn₁:comparisonScale (9/4) < s.Y₁)(hn₂:comparisonScale (9/4) < s.Y₂)(hZ:5 ≤ s.Z) :
    (s.rootSource hH hn₁ hn₂).U₁ ≤ s.Z^(3:ℝ) ∧ (s.rootSource hH hn₁ hn₂).U₂ ≤ s.Z^(3:ℝ) := by
  have hc:=(s.rootData hn₁ hn₂).source_length_caps hH hZ
  change max _ _ ≤ _ ∧ max _ _ ≤ _
  exact ⟨max_le hc.1 hc.2.2.1,max_le hc.2.1 hc.2.2.2⟩

private theorem coarse_product_caps (s:Setup M H α)(ε:ℝ)(hε:0 < ε)
    (hn₁:comparisonScale (9/4) < s.Y₁)(hn₂:comparisonScale (9/4) < s.Y₂)
    (η:Character)(bΦ:ℝ)(he:Event (Fintype.card α) η bΦ ε s.Z)
    (X:ℝ)(hX:0 < X)(hXcap:X ≤ s.Z^(3:ℝ)) :
    (∏i,2*(s.rootSource hH hn₁ hn₂).P i) ≤ s.Z^(4:ℝ) ∧
      (9/4:ℝ)*X*(∏i,2*(s.rootSource hH hn₁ hn₂).P i) ≤ s.Z^(4:ℝ) := by
  have hz:=zero_lt_one.trans s.hZ
  have hf:=actual_face M H s
  have homega:=RepairedRootParameters.omega_spec ε hε
  have hdim:=event_dimension (remaining_card M H s) he
  have hp:0 ≤ (2:ℝ)^Fintype.card (remainingSet s.r s.A):=pow_nonneg (by norm_num) _
  have htwo:(2:ℝ)^Fintype.card (remainingSet s.r s.A) ≤ s.Z^(RepairedRootParameters.omegaLoss ε):=by nlinarith
  have hb:(9/4:ℝ)*2^Fintype.card (remainingSet s.r s.A) ≤ s.Z^(RepairedRootParameters.omegaLoss ε):=by nlinarith
  have hP:0 ≤ s.Z^(markedWidth M H s):=Real.rpow_nonneg hz.le _
  have he₁:RepairedRootParameters.omegaLoss ε+markedWidth M H s ≤ 4:=by linarith [hf.2.1,homega.2.2.2]
  have he₂:RepairedRootParameters.omegaLoss ε+3+markedWidth M H s ≤ 4:=by linarith [hf.2.1,homega.2.2.2]
  constructor
  · rw [doubled_root_product]
    calc
      _ ≤ s.Z^(RepairedRootParameters.omegaLoss ε)*s.Z^(markedWidth M H s):=mul_le_mul_of_nonneg_right htwo hP
      _=s.Z^(RepairedRootParameters.omegaLoss ε+markedWidth M H s):=(Real.rpow_add hz _ _).symm
      _ ≤ _:=Real.rpow_le_rpow_of_exponent_le s.hZ.le he₁
  · rw [doubled_root_product]
    calc
      _=((9/4:ℝ)*2^Fintype.card (remainingSet s.r s.A))*X*s.Z^(markedWidth M H s):=by ring
      _ ≤ s.Z^(RepairedRootParameters.omegaLoss ε)*s.Z^(3:ℝ)*s.Z^(markedWidth M H s):=
        mul_le_mul_of_nonneg_right (mul_le_mul hb hXcap hX.le (Real.rpow_nonneg hz.le _)) hP
      _=s.Z^(RepairedRootParameters.omegaLoss ε+3+markedWidth M H s):=by
        rw [←Real.rpow_add hz,←Real.rpow_add hz]
      _ ≤ _:=Real.rpow_le_rpow_of_exponent_le s.hZ.le he₂

set_option maxHeartbeats 1400000 in
/-- Both original short-side orientations and the newly installed
reference rectangle. Constants precede all restoration data, profiles,
heights and rectangles. The original initialKeep is retained throughout.
The final source theorem adds the contrary-beta hypothesis; this
standalone reference application needs no new source estimate. -/
theorem uniform_original_reference
    (W:ℝ → ℂ)(hW:ContDiff ℝ ∞ W)(hWs:Function.support W⊆Icc (1:ℝ) 2)
    (Lcap ε:ℝ)(hLcap:8 ≤ Lcap)(hε:0 < ε) :
    ∃J:ℕ,∃control:Finset (ℕ×ℕ),∃C:ℝ,0 < C ∧
    ∀(η:Character)(bΦ:ℝ),2 ≤ bΦ → ∀ᶠZ:ℝ in atTop,1 < Z ∧
    ∀s:Setup M H α,s.Z=Z → s.W=W → s.Lcap=Lcap → 
    ∀hn₁:comparisonScale (9/4) < s.Y₁,∀hn₂:comparisonScale (9/4) < s.Y₂,
    RepairedRootParameters.NeedsCentering ε (ordinaryExponent M H s) (markedWidth M H s) → 
    ∀X Y:ℝ,0 < X → 0 < Y → X*Y=s.Y₁*s.Y₂ → 
      X ≤ (s.rootSource hH hn₁ hn₂).U₁ → Y ≤ (s.rootSource hH hn₁ hn₂).U₂ → 
      (X ≤ rootReference M H s ε ∨ Y ≤ rootReference M H s ε) → 
    ∀Q:Id,∀Φ:𝓢(ℝ,ℂ),Function.support (Φ:ℝ → ℂ)⊆Iic bΦ → (∀x,0 ≤ (Φ x).re) → ∀rows:Finset O,
      (∑z∈rows,initialWeight η s.η₀ Q Φ Z z*
        ‖rectangle (s.rootSource hH hn₁ hn₂) (by norm_num) (naturalCharacter η z) X Y‖^2) ≤ 
      radialControl Φ*(C*(sourceControl control (s.p.profile 0)*sourceControl control (s.p.profile 1))^2*
        (MixedFirstProfileEnvelope.height 0 0 s.t s.t)^J*
        Z^(1+RepairedRootParameters.omegaLoss ε+ε/100)) := by
  let omega:=RepairedRootParameters.omegaLoss ε
  let Bf:=RestoredRootSource.slotBound W hW.continuous hWs
  have homega:0 < omega := (RepairedRootParameters.omega_spec ε hε).1
  have hBf:1 ≤ Bf := (RestoredRootSource.slotBound_spec W hW.continuous hWs).1
  obtain ⟨J,control,C,hC,h00,hbound⟩:=uniform_profiled_reference_energy_either (ι:=α)
    (ε/100) 4 (Lcap+8) (1/4) (9/4) omega Bf (by positivity) (by norm_num) (by linarith)
    (by norm_num) (by norm_num) homega hBf
  refine ⟨J,control,C,hC,?_⟩
  intro η bΦ hbΦ
  filter_upwards [eventual_event (Fintype.card α) η bΦ ε hε] with Z he
  refine ⟨he.1,?_⟩
  intro s hsZ hsW hsLc hn₁ hn₂ hhigh X Y hX hY hXY hXU hYU hshort Q Φ hΦs hΦ rows
  subst Z
  let r:=s.rootSource hH hn₁ hn₂
  let T0:=remainingSet s.r s.A
  let ν:=fun i:T0=>relativeCharacter M H hH s.η₀ (s.θ i.val)
  let R₀:=fun _i:T0=>restorationHoles s.r (RestoredInitialSource.primeEnclosure s.Z) s.tc s.A s.ti
  let U:=conductorUpper η bΦ s.Z
  have hz:=zero_lt_one.trans s.hZ
  have hf:=actual_face M H s
  have hg:=RepairedRootParameters.reference_gates hε hf hhigh
  have hgeo:=reference_geometry M H s ε hε hhigh
  have hU:=conductor_upper_gates hε hLcap he
  have hucap:=ordinary_enclosure_caps M H hH s hn₁ hn₂ (by linarith [he.2.1])
  have hXcap:X ≤ s.Z^(3:ℝ):=hXU.trans hucap.1
  have hYcap:Y ≤ s.Z^(3:ℝ):=hYU.trans hucap.2
  have hpX:=coarse_product_caps M H hH s ε hε hn₁ hn₂ η bΦ he X hX hXcap
  have hpY:=coarse_product_caps M H hH s ε hε hn₁ hn₂ η bΦ he Y hY hYcap
  have hprod:X*Y=s.Z^(ordinaryExponent M H s):=by
    rw [hXY]
    exact (Real.rpow_logb hz s.hZ.ne' (mul_pos s.hY₁ s.hY₂)).symm
  have hν:r.ν=slotCoefficient ν R₀ s.t:=rfl
  have hMs:∀i,r.M i ≤ Bf:=by
    intro i
    change RestoredRootSource.slotBound s.W s.hW s.hWs ≤ Bf
    subst W
    exact le_rfl
  have hβ:∀i I,I∈r.pool i → ‖slotCoefficient ν R₀ (s.t+0) i I*r.Wslot i (I.absNorm/r.P i)‖ ≤ Bf:=by
    intro i I hI
    simp only [add_zero,←hν,norm_mul]
    exact (mul_le_mul (r.hν i I) (r.hWnorm i _) (norm_nonneg _) zero_le_one).trans
      (by simpa only [one_mul] using hMs i)
  have hholes:((r.Fhole*r.R).absNorm:ℝ) ≤ s.Z^(Lcap+8):=by
    change (Ideal.absNorm ((1:Id)*1):ℝ) ≤ _
    simpa only [one_mul,map_one,Nat.cast_one] using Real.one_le_rpow s.hZ.le (by linarith : 0 ≤ Lcap+8)
  have hHR:∀i P,P∈r.H → P.val∈R₀ i:=by
    intro i P hP
    change P∈(∅:Finset PrimeIdeal) at hP
    exact (Finset.notMem_empty P hP).elim
  have heligible:∀z,initialKeep η (internalQ Q s.η₀) z → 
      ¬CenteredExceptionalProfile.FixedInducingRow η (internalQ Q s.η₀) fixedBadMask
        ((primaryGenerator (1:Id))^2) z := by
    intro z hk
    simpa only [primaryGenerator_one,one_pow] using ((initial_keep_iff η (internalQ Q s.η₀) z).mp hk).2
  have ha:=hbound T0 r s.Z (1+omega) (ordinaryExponent M H s) (markedWidth M H s) omega
    (rootExponent M H s ε) omega s.hZ.le (by linarith) hf.1 homega.le hgeo.2.2.2.2.1.le homega.le
    hg.1 (reference_total_cap hε hf hhigh) hg.2.1 hg.2.2.1
    (event_dimension (remaining_card M H s) he) hg.2.2.2
    η fixedBadMask 1 (internalQ Q s.η₀) fixedBadMask_ne_zero
    CenteredMomentAddedZero.supported_one_ideal (dvd_mul_right _ _) (dvd_mul_left _ _)
    (initialKeep η (internalQ Q s.η₀)) (fun z hk=>hk.1) heligible
    U X Y 0 s.t 0 ν R₀ hν hU.1 hU.2.1 hU.2.2.1 hX hY hprod hshort (by norm_num)
    hholes (actual_enclosure_cap M H hH s ε η bΦ Lcap hsLc he hn₁ hn₂)
    (actual_rectangle_enclosed M H hH s hn₁ hn₂ X Y hXU hYU) hβ hHR hpX.1 hpX.2 hpY.2
    (root_product M H hH s hn₁ hn₂).le Φ s.Z bΦ hz (by linarith) hΦs he.2.2.2.1 hU.2.2.2
  have hfinite:=finite_reference_le_radial r (by norm_num) η s.η₀ Q Φ s.Z bΦ X Y hz hΦs hΦ rows
  exact hfinite.trans ha

end
end Candidate.FourthPower.RecenteredRootReferenceBound
