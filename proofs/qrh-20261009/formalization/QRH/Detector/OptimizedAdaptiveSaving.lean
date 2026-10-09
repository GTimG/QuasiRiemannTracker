import QRH.Detector.OptimizedMixedSaving

namespace OAI
noncomputable section
namespace SevenEighths.QRHProbeCentralExponent

lemma high_mixed_margin (δ q gap loss ζ μ v d : ℝ)
    (hδ : 5/6≤δ) (hd : δ≤1) (hq : q≤δ/2)
    (hg : 0≤gap) (hl : 0≤loss) (hl1 : loss≤1/32)
    (hζ : 0≤ζ) (hv : v≤QRH.h+ζ) (hμ : 0≤μ) (hdv : d-v≤μ) :
    mixedSourceExponent ((1+δ)/2) v d (1-δ+loss) q-QRH.C (QRH.theta+gap)<
      -(7/100:ℝ)+QRH.h*loss+2*ζ+μ := by
  have hlo : 0≤1-δ+loss+δ/2-17/50 := by linarith
  have hhi : 1-δ+loss+δ/2-17/50≤2 := by linarith
  have h1:=mul_le_mul_of_nonneg_right (show v-QRH.h≤ζ by linarith) hlo
  have h2:=mul_le_mul_of_nonneg_left hhi hζ
  have he:=QRH.large_saving hδ hq
  have hs:=mixed_source_slack ((1+δ)/2) v d (1-δ+loss) q μ 1
    (by linarith) (by linarith) hμ hdv
  rw [manuscript_exponent_identity] at hs
  have hδeq : 2*((1+δ)/2)-1=δ := by ring
  rw [hδeq] at hs
  unfold QRH.exponent at he hs
  unfold QRH.C at hs ⊢
  nlinarith

lemma adaptive_mixed_saving (N : ℕ) (a q gap ε εm slotMesh ν ζ μ v d e eps loss mesh overhead saving : ℝ)
    (ha : 1/2<a) (ha1 : a≤1) (hq : 0≤q) (hq1 : q≤(2*a-1)/2)
    (hg : 0≤gap) (hg1 : gap≤(1-QRH.kappa0)/2) (hε : 0≤ε) (hεm : 0≤εm)
    (hslot : 0≤slotMesh) (hν : 0≤ν) (hcount : 159*ε+εm+slotMesh+7*ν≤1/32)
    (hζ : 0≤ζ) (hv : v≤QRH.h+ζ) (hv1 : v≤1)
    (hμ : 0≤μ) (hdv : d-v≤μ) (he : 0≤e) (heps : 0≤eps)
    (hbudget : QRH.h*(159*ε+εm+slotMesh+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+mesh*QRH.ell)+overhead+saving≤(1/1000000000000:ℝ)) :
    mixedSourceExponent a v d
      (QRHProbeHighRowFamily.adaptiveRowExponent (2*a-1) q gap ε εm slotMesh ν) q+
      realLoss N v e eps loss mesh+overhead≤QRH.C (QRH.theta+gap)-saving := by
  have hδ : 0<2*a-1 := by linarith
  have hx : 0≤q/(2*a-1) := div_nonneg hq hδ.le
  have hx1 : q/(2*a-1)≤1/2 := (div_le_iff₀ hδ).mpr (by linarith)
  have hl : 0≤159*ε+εm+slotMesh+7*ν := by positivity
  have haeq : (1+(2*a-1))/2=a := by ring
  have hqeq : (2*a-1)*(q/(2*a-1))=q := mul_div_cancel₀ q hδ.ne'
  have hr:=realLoss_bound N v e eps loss mesh hv1 he heps
  by_cases hd : 2*a-1≤5/6
  · have hb:=balanced_mixed_saving (2*a-1) (q/(2*a-1)) gap (159*ε+εm+slotMesh+7*ν)
      ζ μ v d (realLoss N v e eps loss mesh+overhead) saving
      hδ.le hd hx hx1 hg hg1 hl hcount hζ hv hμ hdv (by linarith)
    rw [haeq,hqeq] at hb
    simpa only [QRHProbeHighRowFamily.adaptiveRowExponent,ite_eq_left hd,add_assoc] using hb
  · have hh:=high_mixed_margin (2*a-1) q gap (78*ε+εm) ζ μ v d
      (le_of_lt (lt_of_not_ge hd)) (by linarith) hq1 hg (by positivity) (by linarith)
      hζ hv hμ hdv
    rw [haeq] at hh
    have hH : 0≤QRH.h := by norm_num [QRH.h,QRH.lx,QRH.M,QRH.ell,QRH.b,QRH.theta]
    have hcost:=mul_le_mul_of_nonneg_left (show 78*ε+εm≤159*ε+εm+slotMesh+7*ν by linarith) hH
    simp only [QRHProbeHighRowFamily.adaptiveRowExponent,ite_eq_right hd]
    simp only [add_assoc] at hh ⊢
    linarith

end SevenEighths.QRHProbeCentralExponent
end
end OAI
