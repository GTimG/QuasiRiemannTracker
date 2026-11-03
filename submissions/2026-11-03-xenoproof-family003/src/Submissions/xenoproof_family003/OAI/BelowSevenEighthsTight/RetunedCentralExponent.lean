import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RationalEndpointConnection
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RetunedSourceNormalization
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.CentralExponent

/- UNVERIFIED physical-exponent connection. Analytic row bounds remain separate. -/
set_option autoImplicit false
namespace BelowSevenEighthsTight.CentralExtension
noncomputable section
open RowCountExtension PrincipalExtension

def sourceExponent (ξ υ total a v d R q : ℝ) : ℝ :=
  ξ*(1/2-17/50)+a+17/50-1-a*υ-v*(17/50)+d*R+
    v*(a-1/2)+total*(17/50-1/2+q)

def realLoss (υ total : ℝ) (N : ℕ) (v e eps heightLoss mesh : ℝ) : ℝ :=
  (16-6*υ)*e+12*v*e+v*eps*(N+8)+heightLoss+total*mesh

theorem original_source_exponent (a d R q : ℝ) :
    sourceExponent (17/48) (23/48) (1/6) a d d R q =
      OAI.SevenEighths.ProbeCentralExponent.sourceExponent a d R q := by
  unfold sourceExponent OAI.SevenEighths.ProbeCentralExponent.sourceExponent
  ring

theorem physical_scale_identity (ξ υ Z a e : ℝ) (hZ : 0<Z) :
    (Z^ξ)^(4/25:ℝ)*Z^(a+16*e-33/50)*(Z^υ)^(-a-6*e)=
      Z^((1-υ)*a+4*ξ/25-33/50+(16-6*υ)*e) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,
    ←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring

theorem mixed_physical_exponent (ξ υ total Z a v d R q e eps loss mesh : ℝ)
    (N : ℕ) (hZ : 0<Z) :
    ((Z^ξ)^(4/25:ℝ)*Z^(a+16*e-33/50)*(Z^υ)^(-a-6*e))*
      ((Z^d)^R*(Z^v)^(a-1/2+12*e+eps*(N+8)-17/50)*
        Z^(total*(17/50-1/2+q)+total*mesh+loss))=
      Z^(sourceExponent ξ υ total a v d R q+realLoss υ total N v e eps loss mesh) := by
  rw [physical_scale_identity ξ υ Z a e hZ]
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  unfold sourceExponent realLoss
  ring

theorem realLoss_bound (υ total : ℝ) (N : ℕ) (v e eps heightLoss mesh : ℝ)
    (hυ : 1/3≤υ) (htotal : total≤1/5) (hv : v≤1)
    (he : 0≤e) (heps : 0≤eps) (hmesh : 0≤mesh) :
    realLoss υ total N v e eps heightLoss mesh≤
      26*e+(N+8)*eps+heightLoss+mesh/5 := by
  have h1 := mul_le_mul_of_nonneg_right hv he
  have h2 := mul_le_mul_of_nonneg_right hv (show 0≤eps*(N+8) by positivity)
  have h3 := mul_le_mul_of_nonneg_right hυ he
  have h4 := mul_le_mul_of_nonneg_right htotal hmesh
  unfold realLoss
  nlinarith

theorem rational_physical_transport (δ v d R q β : ℝ) :
    sourceExponent lxRat lyRat ellRat ((1+δ)/2) v d R q-
      (β+sourceShift lxRat ellRat)=
    physicalExponent δ q R β hRat+(v-hRat)*(R+δ/2-17/50)+(d-v)*R := by
  unfold sourceExponent sourceShift physicalExponent lxRat lyRat hRat
  ring

theorem conductor_slack (δ v d R ζ μ : ℝ)
    (hδ : 0≤δ) (hδ1 : δ≤1) (hRlo : 1-δ≤R) (hRhi : R≤3/2)
    (hζ : 0≤ζ) (hv : v≤hRat+ζ) (hμ : 0≤μ) (hd : d-v≤μ) :
    (v-hRat)*(R+δ/2-17/50)+(d-v)*R≤2*ζ+(3/2)*μ := by
  have hR : 0≤R := by linarith
  have hs : 0≤R+δ/2-17/50 := by linarith
  have hs1 : R+δ/2-17/50≤2 := by linarith
  have h1 := mul_le_mul_of_nonneg_right (show v-hRat≤ζ by linarith) hs
  have h2 := mul_le_mul_of_nonneg_left hs1 hζ
  have h3 := mul_le_mul_of_nonneg_right hd hR
  have h4 := mul_le_mul_of_nonneg_left hRhi hμ
  linarith

theorem rational_balanced_source_margin (δ y v d R q β ζ μ loss : ℝ)
    (hδ : 0≤δ) (hδ1 : δ≤5/6) (hy : 0≤y) (hy1 : y≤1/2)
    (hβ : sigmaRat≤β) (hRlo : 1-δ≤R) (hRhi : R≤3/2)
    (hζ : 0≤ζ) (hv : v≤hRat+ζ) (hμ : 0≤μ) (hd : d-v≤μ)
    (hq : q≤δ*(1/2-y)) (hR : R≤countR δ y+(β-sigmaRat)/4+loss) :
    sourceExponent lxRat lyRat ellRat ((1+δ)/2) v d R q-
      (β+sourceShift lxRat ellRat)≤
      -1/1000000000000000-3*(β-sigmaRat)/4+hRat*loss+2*ζ+(3/2)*μ := by
  have hb := rational_low_endpoint_with_errors δ y q R β hRat 0 loss
    hδ hδ1 hy hy1 hβ (by norm_num [hRat,ellRat,bRat])
    (by norm_num [hRat,ellRat,bRat]) (by norm_num) (by linarith) hq hR
  have hs := conductor_slack δ v d R ζ μ hδ (by linarith) hRlo hRhi hζ hv hμ hd
  rw [rational_physical_transport]
  linarith

theorem rational_high_source_margin (δ v d R q β ζ μ loss : ℝ)
    (hδ : 5/6≤δ) (hδ1 : δ≤1) (hRlo : 1-δ≤R) (hRhi : R≤3/2)
    (hζ : 0≤ζ) (hv : v≤hRat+ζ) (hμ : 0≤μ) (hd : d-v≤μ)
    (hq : q≤δ/2) (hR : R≤1-δ+loss) :
    sourceExponent lxRat lyRat ellRat ((1+δ)/2) v d R q-
      (β+sourceShift lxRat ellRat)≤
      -1/20-(β-sigmaRat)+hRat*loss+2*ζ+(3/2)*μ := by
  have hb := rational_high_endpoint_with_errors δ q R β hRat 0 loss hδ hδ1
    (by norm_num [hRat,ellRat,bRat]) (by norm_num) (by linarith) hq hR
  have hs := conductor_slack δ v d R ζ μ (by linarith) hδ1 hRlo hRhi hζ hv hμ hd
  rw [rational_physical_transport]
  linarith

#print axioms original_source_exponent
#print axioms physical_scale_identity
#print axioms mixed_physical_exponent
#print axioms realLoss_bound
#print axioms rational_physical_transport
#print axioms conductor_slack
#print axioms rational_balanced_source_margin
#print axioms rational_high_source_margin
end
end BelowSevenEighthsTight.CentralExtension
