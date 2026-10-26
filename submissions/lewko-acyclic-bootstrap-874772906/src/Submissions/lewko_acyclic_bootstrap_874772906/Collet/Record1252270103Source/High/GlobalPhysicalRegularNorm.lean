/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The complete regular family is integrated jointly. Its coarse absolute
budget controls the unrestricted Mellin tail; only actual ratio bins are paid. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularHeights
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularPhase
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Contraction.SelectedFullNormalizedFamily
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Contraction.SelectedFullNormalizedContraction
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn CenteredMomentCanonicalFirst
open CenteredMomentAddedZeroUniform CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical CenteredMomentSecondInputCapacitySource
open CenteredMomentSectorLocalization Cycle61InitialMass Cycle61Moment Record1252270103Second
open Admission.SelectedRegularSourceData Admission.SelectedSecondPhase Admission.SelectedHighPaid
local notation "O"=>HeckeFamily.O
local instance regularNormDecidable {ι:Type*}:DecidableEq ι:=Classical.decEq _

open Admission CenteredMomentLogDyadic
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentFirstAmplificationChoice CenteredMomentSecondCanonical

theorem regular_ratio_bins (ε:ℝ)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
    ∀{α Label:Type}[Fintype α][Fintype Label](a:Anchor α Z)(F:Family a Label),
    (∀l,Z^(-(32:ℝ))≤F.Hmain l)→(∀l,F.Hmain l≤Z^(32:ℝ))→
    (∀l,frequencyRadius (F.Tsec l) Z F.ξ≤Z^(4:ℝ))→
    (∀l,sourceRadius (F.input l)≤Z^(2:ℝ))→
    ((secondRatioBins (fun q:F.Complete=>modifiedDatumBlock (F.datum q) (F.childModifier q.1))).card:ℝ)≤C*Z^ε:=by
  obtain ⟨C,hC,he⟩:=Contraction.modified_second_family_ratio_bins_subpower 32 32 2 4 1 ε
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hε
  refine ⟨C,hC,?_⟩
  filter_upwards [he] with Z h
  intro α Label instα instLabel a F hHlo hHhi hfreq hsource
  exact h F.slots F.input F.childModifier F.mask F.childSeed F.childSeed_sf
    (fun _=>F.zero₁) (fun _=>F.zero₂) ballProfile F.Hmain F.Tsec (fun _=>F.ξ) F.Hmain_pos
    hHlo hHhi (by simpa only [one_mul] using hfreq) hsource (regularFamilyKeep F)

/-- All constants and the integration degree precede the actual first family.
The small-height premise is the bounded normalized source estimate. -/
theorem regular_joint_of_bounded_normalized (τ A reserve Cs Ca:ℝ)(N smallDegree:ℕ)
    (hτ:0<τ)(hr:0<reserve)(hCs:0≤Cs)(hCa:0≤Ca):
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,2≤Z ∧
    ∀{α Label:Type}[Fintype α][Fintype Label](a:Anchor α Z)(F:Family a Label),
    sourceRadius F.s≤Z^(2:ℝ)→
    (∀l,Z^(-(32:ℝ))≤F.Hmain l)→(∀l,F.Hmain l≤Z^(32:ℝ))→
    (∀l,frequencyRadius (F.Tsec l) Z F.ξ≤Z^(4:ℝ))→
    (∀l,sourceRadius (F.input l)≤Z^(2:ℝ))→
    ∀(W:𝓢(ℝ,ℂ))(P:Label→Finset (Ideal O))(H0 radius:Label→ℝ)(ell control external:ℝ),
    0≤control→1≤external→
    (∀second:Bool,∀t u:ℝ,(1+‖t‖)*(1+‖u‖)≤Z^τ→
      modifiedSecondNormalizedSum second F.datum (fun q=>F.childModifier q.1)
        (regularFamilyWeight F W P H0 radius ell) t u≤
        Cs*geometryHighFactor F.reflected (geometrySupportConstant N 1 (1/4) (1/4)) F.bin*
          control*external^smallDegree*((1+‖t‖)*(1+‖u‖))^smallDegree*Z^(-(reserve/4)))→
    secondAbsoluteBudget F.datum (fun q=>F.childModifier q.1)
      (regularFamilyWeight F W P H0 radius ell)≤Ca*control*Z^A→
    ‖∑q:F.Complete,SelectedRegularAbsolute.phase F W P H0 radius ell (regularFamilyKeep F) q*
      (modifiedDatumBlock (F.datum q) (F.childModifier q.1)).value ballProfile‖≤
      C*geometryHighFactor F.reflected (geometrySupportConstant N 1 (1/4) (1/4)) F.bin*
        control*external^smallDegree*Z^(-(reserve/8)):=by
  obtain ⟨J,hJ⟩:=regular_normalized_height_extension τ A 2 (reserve/4) hτ smallDegree
  obtain ⟨Cc,hCc,hcon⟩:=Contraction.modified_retained_from_full_normalized ballProfile J J
    logAnnulus_compact logAnnulus_smooth
  obtain ⟨Cr,hCr,eratio⟩:=regular_ratio_bins (reserve/8) (by positivity)
  let Cg:=regularGeometryFloor (geometrySupportConstant N 1 (1/4) (1/4))
  have hCg:0≤Cg:=zero_le_one.trans (le_max_left _ _)
  let C:=1+Cc*Cr*(Cs+Ca*Cg)
  have hC:0<C:=by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [eratio,eventually_ge_atTop (2:ℝ)] with Z hratio hZ
  refine ⟨hZ,?_⟩
  intro α Label instα instLabel a F hsource hHlo hHhi hfreq hchild W P H0 radius ell control external hc he hsmall habs
  have hz:0<Z:=zero_lt_one.trans F.hZ
  have hg:=geometry_high_factor_pos F.reflected (geometrySupportConstant N 1 (1/4) (1/4)) F.bin
    (geometrySupportConstant_pos N 1 (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num))
  by_cases hlabel:Nonempty Label
  · letI:=hlabel
    let l:Label:=Classical.choice hlabel
    have hbin:F.bin∈CoupledFirst.commonGeometryBins F.s F.modifier F.R F.seed (Z^F.D) Z F.ξ:=by
      exact Finset.mem_image.mpr ⟨(F.column l).1.val,Finset.mem_univ _,(F.column l).1.property⟩
    have hb:=FirstTruncatedHeights.actual_geometry_balance_cap F.s F.modifier F.R F.seed
      (Z^F.D) Z F.ξ 2 hZ F.seed_sf F.zero₁ F.zero₂ hsource F.bin hbin F.reflected
    have hfloor:1≤Cg*geometryHighFactor F.reflected (geometrySupportConstant N 1 (1/4) (1/4)) F.bin*Z^(2:ℝ):=by
      apply regular_geometry_floor _ Z 2
        (geometrySupportConstant_pos N 1 (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num)) hz
      norm_num at hb ⊢;exact hb
    have hall(second:Bool):=hJ second F.datum (fun q=>F.childModifier q.1)
      (regularFamilyWeight F W P H0 radius ell) Z control
      (geometryHighFactor F.reflected (geometrySupportConstant N 1 (1/4) (1/4)) F.bin)
      external Cs Ca Cg F.hZ.le hc hg.le he hCs hCa hCg hfloor (hsmall second) habs
    have hn:=hcon F.datum (fun q=>F.childModifier q.1)
      (SelectedRegularAbsolute.phase F W P H0 radius ell (regularFamilyKeep F))
      ((Cs+Ca*Cg)*geometryHighFactor F.reflected (geometrySupportConstant N 1 (1/4) (1/4)) F.bin*
        control*external^smallDegree*Z^(-(reserve/4))) (by positivity) hall
    have hcount:=hratio a F hHlo hHhi hfreq hchild
    calc
      _≤Cc*((secondRatioBins (fun q:F.Complete=>modifiedDatumBlock (F.datum q) (F.childModifier q.1))).card:ℝ)*
          ((Cs+Ca*Cg)*geometryHighFactor F.reflected (geometrySupportConstant N 1 (1/4) (1/4)) F.bin*
            control*external^smallDegree*Z^(-(reserve/4))):=hn
      _≤Cc*(Cr*Z^(reserve/8))*
          ((Cs+Ca*Cg)*geometryHighFactor F.reflected (geometrySupportConstant N 1 (1/4) (1/4)) F.bin*
            control*external^smallDegree*Z^(-(reserve/4))):=by gcongr
      _=(Cc*Cr*(Cs+Ca*Cg))*geometryHighFactor F.reflected (geometrySupportConstant N 1 (1/4) (1/4)) F.bin*
          control*external^smallDegree*Z^(-(reserve/8)):=by
        have hp:Z^(reserve/8)*Z^(-(reserve/4))=Z^(-(reserve/8)):=by
          rw [←Real.rpow_add hz];congr 1;ring
        calc
          _=(Cc*Cr*(Cs+Ca*Cg))*geometryHighFactor F.reflected (geometrySupportConstant N 1 (1/4) (1/4)) F.bin*
            control*external^smallDegree*(Z^(reserve/8)*Z^(-(reserve/4))):=by ring
          _=_:=by rw [hp]
      _≤C*geometryHighFactor F.reflected (geometrySupportConstant N 1 (1/4) (1/4)) F.bin*
          control*external^smallDegree*Z^(-(reserve/8)):=by dsimp [C];gcongr;linarith
  · letI:IsEmpty Label:=not_nonempty_iff.mp hlabel
    have hz0:(∑q:F.Complete,SelectedRegularAbsolute.phase F W P H0 radius ell (regularFamilyKeep F) q*
      (modifiedDatumBlock (F.datum q) (F.childModifier q.1)).value ballProfile)=0:=by
      exact Finset.sum_eq_zero (fun q _=>False.elim (isEmptyElim q.1))
    rw [hz0,norm_zero]
    positivity
end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_ratio_bins
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_joint_of_bounded_normalized
