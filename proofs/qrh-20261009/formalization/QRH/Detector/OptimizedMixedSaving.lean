import QRH.Detector.OptimizedCentralExponent
import QRH.PrimeRows.DynamicSourceCount

/-! Strict continuous saving for the actual optimized count exponent, including
capacity loss and dyadic conductor slack. Analytic estimates remain separate. -/
namespace OAI
noncomputable section
namespace SevenEighths.QRHProbeCentralExponent

lemma adaptive_count_range (δ x gap loss : ℝ)
    (hδ : 0≤δ) (hd : δ≤5/6) (hx : 0≤x) (hx1 : x≤1/2)
    (hg : 0≤gap) (hg1 : gap≤(1-QRH.kappa0)/2) (hl : 0≤loss) (hl1 : loss≤1/32) :
    let R:=QRH.adaptiveCount δ x+(30/169)*gap+loss;
    1-δ≤R ∧ R≤3/2 := by
  have ht:=QRH.Certificate.witness_range hδ hd hx hx1
  have hid : QRH.adaptiveCount δ x=1-δ+(5/6-δ)*(QRH.Certificate.witness δ x-1) := by
    unfold QRH.adaptiveCount QRH.Certificate.witness
    ring
  have hg2 : gap≤1/6 := by
    have hk : (2/3:ℝ)≤QRH.kappa0 := by norm_num [QRH.kappa0,QRH.theta]
    linarith
  have hlo:=mul_nonneg (show 0≤5/6-δ by linarith) (show 0≤QRH.Certificate.witness δ x-1 by linarith)
  have hhi:=mul_le_mul_of_nonneg_left (show QRH.Certificate.witness δ x-1≤1/2 by linarith)
    (show 0≤5/6-δ by linarith)
  dsimp only
  rw [hid]
  constructor <;> nlinarith

lemma balanced_mixed_margin (δ x gap loss ζ μ v d : ℝ)
    (hδ : 0≤δ) (hd : δ≤5/6) (hx : 0≤x) (hx1 : x≤1/2)
    (hg : 0≤gap) (hg1 : gap≤(1-QRH.kappa0)/2) (hl : 0≤loss) (hl1 : loss≤1/32)
    (hζ : 0≤ζ) (hv : v≤QRH.h+ζ) (hμ : 0≤μ) (hdv : d-v≤μ) :
    let R:=QRH.adaptiveCount δ x+(30/169)*gap+loss;
    mixedSourceExponent ((1+δ)/2) v d R (δ*x)-QRH.C (QRH.theta+gap)<
      -(2/1000000000000:ℝ)+QRH.h*loss+2*ζ+(3/2)*μ := by
  let R:=QRH.adaptiveCount δ x+(30/169)*gap+loss
  have hr:=adaptive_count_range δ x gap loss hδ hd hx hx1 hg hg1 hl hl1
  have hlo : 0≤R+δ/2-17/50 := by dsimp [R];linarith [hr.1]
  have hhi : R+δ/2-17/50≤2 := by dsimp [R];linarith [hr.2]
  have h1:=mul_le_mul_of_nonneg_right (show v-QRH.h≤ζ by linarith) hlo
  have h2:=mul_le_mul_of_nonneg_left hhi hζ
  have he:=QRH.Certificate.endpoint_saving hδ hd hx hx1
  have hi:=QRH.endpoint_is_manuscript δ x
  have hs:=mixed_source_slack ((1+δ)/2) v d R (δ*x) μ (3/2)
    (by dsimp [R];linarith [hr.1]) hr.2 hμ hdv
  have hh : QRH.h≤1 := by norm_num [QRH.h,QRH.lx,QRH.M,QRH.ell,QRH.b,QRH.theta]
  have hgprod:=mul_nonneg (show 0≤1-QRH.h*(30/169) by linarith) hg
  rw [manuscript_exponent_identity] at hs
  have hδeq : 2*((1+δ)/2)-1=δ := by ring
  rw [hδeq] at hs
  dsimp only
  unfold QRH.exponent at hi hs
  unfold QRH.C at hs ⊢
  dsimp only [R] at *
  nlinarith

lemma balanced_mixed_saving (δ x gap loss ζ μ v d other saving : ℝ)
    (hδ : 0≤δ) (hd : δ≤5/6) (hx : 0≤x) (hx1 : x≤1/2)
    (hg : 0≤gap) (hg1 : gap≤(1-QRH.kappa0)/2) (hl : 0≤loss) (hl1 : loss≤1/32)
    (hζ : 0≤ζ) (hv : v≤QRH.h+ζ) (hμ : 0≤μ) (hdv : d-v≤μ)
    (hb : QRH.h*loss+2*ζ+(3/2)*μ+other+saving≤(1/1000000000000:ℝ)) :
    mixedSourceExponent ((1+δ)/2) v d
      (QRH.adaptiveCount δ x+(30/169)*gap+loss) (δ*x)+other≤QRH.C (QRH.theta+gap)-saving := by
  have hm:=balanced_mixed_margin δ x gap loss ζ μ v d hδ hd hx hx1 hg hg1 hl hl1 hζ hv hμ hdv
  linarith

end SevenEighths.QRHProbeCentralExponent
end
end OAI
