import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RetunedCentralExponent

/- UNVERIFIED auxiliary physical-exponent margins; analytic estimates separate. -/
set_option autoImplicit false
namespace BelowSevenEighthsTight.CentralExtension
noncomputable section
open RowCountExtension PrincipalExtension

theorem rational_floor_source_margin (q β ζ v : ℝ) (hq : q≤1/100)
    (hζ : 0≤ζ) (hv : v≤hRat+ζ) :
    sourceExponent lxRat lyRat ellRat (51/100) v v 1 q-
      (β+sourceShift lxRat ellRat)≤-7/1200-(β-sigmaRat)+2*ζ := by
  have hs := conductor_slack (1/50) v v 1 ζ 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hζ hv (by norm_num) (by linarith)
  have hb : physicalExponent (1/50) q 1 β hRat≤-7/1200-(β-sigmaRat) := by
    have hq' := mul_le_mul_of_nonneg_left hq (show 0≤ellRat by norm_num [ellRat])
    norm_num [physicalExponent,hRat,lyRat,ellRat,bRat,sigmaRat] at hq' ⊢
    linarith
  have he := rational_physical_transport (1/50) v v 1 q β
  norm_num at he hs
  linarith

theorem rational_intermediate_source_margin (δ q β v : ℝ)
    (hδ : 0≤δ) (hδ1 : δ≤5/6) (hq : q≤δ/2) (hv : v≤1/2) :
    sourceExponent lxRat lyRat ellRat ((1+δ)/2) v v (76/75-(2/3)*δ) q-
      (β+sourceShift lxRat ellRat)≤-1/400-(β-sigmaRat) := by
  have hs : 0≤(76/75-(2/3)*δ)+δ/2-17/50 := by linarith
  have hm := mul_le_mul_of_nonneg_right hv hs
  have hq' := mul_le_mul_of_nonneg_left hq (show 0≤ellRat by norm_num [ellRat])
  norm_num [sourceExponent,sourceShift,lxRat,lyRat,ellRat,bRat,sigmaRat] at hq' ⊢
  nlinarith

theorem old_intermediate_constant_cannot_be_copied :
    -(49/14400:ℝ)<
      sourceExponent lxRat lyRat ellRat ((1+5/6)/2) (1/2) (1/2)
        (76/75-(2/3)*(5/6)) ((5/6)/2)-
        (sigmaRat+sourceShift lxRat ellRat) := by
  norm_num [sourceExponent,sourceShift,lxRat,lyRat,ellRat,bRat,sigmaRat]

#print axioms rational_floor_source_margin
#print axioms rational_intermediate_source_margin
#print axioms old_intermediate_constant_cannot_be_copied
end
end BelowSevenEighthsTight.CentralExtension
