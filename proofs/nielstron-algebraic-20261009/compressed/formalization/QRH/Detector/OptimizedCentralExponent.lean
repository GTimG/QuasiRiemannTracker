import QRH.NumericFacts
import OAI.NumberTheory.DirichletL.Detector.CentralExponent
import QRH.OtherRanges
/-! Exact exponents for the original physical powers at optimized geometry.
The Fourier weight 1/6 is retained; ell changes the slot product only. -/
namespace OAI
noncomputable section
open scoped BigOperators
namespace SevenEighths.QRHProbeCentralExponent

def sourceExponent (a d R q : ℝ) : ℝ :=
  QRH.lx*(1/2-17/50)+a+17/50-1-a*QRH.ly-d*(17/50)+d*R+
    d*(a-1/2)+QRH.ell*(17/50-1/2+q)

def mixedSourceExponent (a v d R q : ℝ) : ℝ := sourceExponent a v R q+(d-v)*R

def realLoss (N : ℕ) (v e eps heightLoss mesh : ℝ) : ℝ :=
  (16-6*QRH.ly)*e+12*v*e+v*eps*(N+8)+heightLoss+mesh*QRH.ell

lemma manuscript_exponent_identity (a d R q : ℝ) :
    sourceExponent a d R q=QRH.C QRH.tightTheta+QRH.exponent d (2*a-1) q R := by
  unfold sourceExponent QRH.C QRH.exponent QRH.h QRH.lx QRH.ly QRH.M
  ring

lemma physical_scale_identity (Z a e : ℝ) (hZ : 0<Z) :
    (Z^QRH.lx)^(4/25:ℝ)*Z^(a+16*e-33/50)*(Z^QRH.ly)^(-a-6*e)=
      Z^((1-QRH.ly)*a+(4/25)*QRH.lx-33/50+(16-6*QRH.ly)*e) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring



lemma realLoss_bound (N : ℕ) (v e eps heightLoss mesh : ℝ)
    (hv : v≤1) (he : 0≤e) (heps : 0≤eps) :
    realLoss N v e eps heightLoss mesh≤26*e+(N+8)*eps+heightLoss+mesh*QRH.ell := by
  have hly : (1/3:ℝ)≤QRH.ly := by linarith [QRH.NumericFacts.ly_lower]
  have h1 := mul_le_mul_of_nonneg_right hv he
  have h2 := mul_le_mul_of_nonneg_right hv (show 0≤eps*(N+8) by positivity)
  have h3 := mul_nonneg (show 0≤QRH.ly-1/3 by linarith) he
  unfold realLoss
  nlinarith

lemma central_class_exponent_identity (N : ℕ) (a v d R q e eps loss mesh overhead : ℝ) :
    ((1-QRH.ly)*a+(4/25)*QRH.lx-33/50+(16-6*QRH.ly)*e)+
      (overhead+d*R+v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-
        (4/25)*QRH.ell+q*QRH.ell+mesh*QRH.ell)=
    mixedSourceExponent a v d R q+realLoss N v e eps loss mesh+overhead := by
  unfold mixedSourceExponent sourceExponent realLoss
  ring

lemma mixed_source_slack (a v d R q μ Rmax : ℝ)
    (hR : 0≤R) (hRmax : R≤Rmax) (hμ : 0≤μ) (hd : d-v≤μ) :
    mixedSourceExponent a v d R q≤sourceExponent a v R q+μ*Rmax := by
  have h1 := mul_le_mul_of_nonneg_right hd hR
  have h2 := mul_le_mul_of_nonneg_left hRmax hμ
  unfold mixedSourceExponent
  linarith
end SevenEighths.QRHProbeCentralExponent
end
end OAI
