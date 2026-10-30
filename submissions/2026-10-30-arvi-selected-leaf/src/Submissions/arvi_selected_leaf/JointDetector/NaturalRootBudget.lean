/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.NaturalRoundedBudget
import Submissions.arvi_selected_leaf.JointDetector.NaturalPhysicalBudget
import Submissions.arvi_selected_leaf.JointDetector.NaturalSqrtBudget

/-! The actual two-radius square-root budget. Both source endpoints 2T
and pivot endpoints 2U are retained, together with radial rounding.
-/
namespace Qrh.JointDetector.NaturalRootBudget
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open FiveColourNorm NaturalRoundedBudget NaturalPhysicalBudget

theorem physical_source2_cost_le (U V X G H J E F R r b rho Nb Bad δ D T : ℝ)
    (hU : 0 < U) (hV : 0 < V) (hX : U*V^2 ≤ X)
    (hG : 1 ≤ G) (hH : 1 ≤ H) (hJ : 1 ≤ J) (hE : 1 ≤ E)
    (hF : 1 ≤ F) (hR : 1 ≤ R) (hpuncture : R ≤ G*H)
    (hr : 0 < r) (hb : 1 ≤ b) (hbBad : b ≤ Bad)
    (hrho : rho ∈ Set.Icc (1/2:ℝ) 32) (hNb : 1 ≤ Nb)
    (hδ : δ ∈ Set.Icc (0:ℝ) 1)
    (hD : D=rho*U*V/(G*H*E*F*J))
    (hT : T=(r*(b*rho^2/Nb))*sharedDualScale U V X G H J E F R) :
    (X/(b*R*Real.sqrt ((E*F*J)*D^2)))/(1+r)^2*
      Real.sqrt ((V/(H*J*E))*(V/(H*J*F)))*
      Real.sqrt ((2*T+(2*(U/(G*E)))^(1-δ)*(2*T)^δ)*
        (2*T+(2*(U/(G*F)))^(1-δ)*(2*T)^δ)) ≤ 16384*Bad*X := by
  have hXp : 0 < X := (by positivity : 0 < U*V^2).trans_le hX
  have hGp : 0 < G := by linarith
  have hHp : 0 < H := by linarith
  have hJp : 0 < J := by linarith
  have hEp : 0 < E := by linarith
  have hFp : 0 < F := by linarith
  have hRp : 0 < R := by linarith
  have hbp : 0 < b := by linarith
  have hrhop : 0 < rho := by linarith [hrho.1]
  have hNbp : 0 < Nb := by linarith
  have hDp : 0 < D := by rw [hD]; positivity
  have hTp : 0 < T := by rw [hT]; unfold sharedDualScale; positivity
  have hnormal := physical_normalization X b R rho U V G H E F J D hXp hbp hRp hrhop
    hU hV hGp hHp hEp hFp hJp hD
  rw [mul_comm (V/(H*J*F)) (V/(H*J*E))] at hnormal
  have hdoubled := double_source_root_le (2*(U/(G*E))) (2*(U/(G*F))) T δ
    (by positivity) (by positivity) hTp hδ
  have hrounded := rounded_shared_cost_le U V X G H J E F R r b rho Nb Bad δ 2
    hU hV hX hG hH hJ hE hF hR hpuncture hr hb hbBad hrho hNb hδ (by decide)
  dsimp only at hrounded
  rw [← hT] at hrounded
  calc
    _ = ((X*G/(U*R*Real.sqrt J))/(b*rho))*
        Real.sqrt ((2*T+(2*(U/(G*E)))^(1-δ)*(2*T)^δ)*
          (2*T+(2*(U/(G*F)))^(1-δ)*(2*T)^δ))/(1+r)^2 := by
      rw [← hnormal]
      ring
    _ ≤ ((X*G/(U*R*Real.sqrt J))/(b*rho))*
        (2*Real.sqrt ((T+(2*(U/(G*E)))^(1-δ)*T^δ)*
          (T+(2*(U/(G*F)))^(1-δ)*T^δ)))/(1+r)^2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdoubled (by positivity)) (by positivity)
    _ = 2*((X*G/(U*R*Real.sqrt J))/(b*rho)*
        Real.sqrt ((T+(2*(U/(G*E)))^(1-δ)*T^δ)*
          (T+(2*(U/(G*F)))^(1-δ)*T^δ))/(1+r)^2) := by ring
    _ ≤ 2*(8192*Bad*X) := mul_le_mul_of_nonneg_left hrounded (by norm_num)
    _ = _ := by ring

/-- Both higher counts, both actual SF bounds and both divisor losses are
paid simultaneously. W is the common Y^epsilon, Zl the common Z^loss. -/
theorem complete_root_budget
    (U V X G H J E F R r b rho Nb Bad δ D T : ℝ)
    (nL nR KL KR C Ch Cs Deps Zl W fL fR EL ER : ℝ)
    (hU : 0 < U) (hV : 0 < V) (hX : U*V^2 ≤ X)
    (hG : 1 ≤ G) (hH : 1 ≤ H) (hJ : 1 ≤ J) (hE : 1 ≤ E)
    (hF : 1 ≤ F) (hR : 1 ≤ R) (hpuncture : R ≤ G*H)
    (hr : 0 < r) (hb : 1 ≤ b) (hbBad : b ≤ Bad)
    (hrho : rho ∈ Set.Icc (1/2:ℝ) 32) (hNb : 1 ≤ Nb)
    (hδ : δ ∈ Set.Icc (0:ℝ) 1)
    (hD : D=rho*U*V/(G*H*E*F*J))
    (hT : T=(r*(b*rho^2/Nb))*sharedDualScale U V X G H J E F R)
    (hfL : fL=2*T+(2*(U/(G*E)))^(1-δ)*(2*T)^δ)
    (hfR : fR=2*T+(2*(U/(G*F)))^(1-δ)*(2*T)^δ)
    (hnL0 : 0 ≤ nL) (hnR0 : 0 ≤ nR) (hKL0 : 0 ≤ KL) (hKR0 : 0 ≤ KR)
    (hC : 0 ≤ C) (hCh : 0 ≤ Ch) (hCs : 0 ≤ Cs) (hDeps : 0 ≤ Deps)
    (hZl : 0 ≤ Zl) (hW : 0 ≤ W) (hfL0 : 0 ≤ fL) (hfR0 : 0 ≤ fR)
    (hEL : 0 ≤ EL) (hER : 0 ≤ ER)
    (hnR : nR ≤ Ch*(16*(V/(H*J*E)))*W)
    (hnL : nL ≤ Ch*(16*(V/(H*J*F)))*W)
    (hKL : KL ≤ Cs*Zl*fL) (hKR : KR ≤ Cs*Zl*fR) :
    (8*X/(b*R*Real.sqrt ((E*F*J)*D^2))*C/(1+r)^2)*
      Real.sqrt (nR*KL*(Deps*W)*EL)*Real.sqrt (nL*KR*(Deps*W)*ER) ≤
      (8*16*16384*Bad*C*Ch*Cs*Deps)*Zl*W^2*X*Real.sqrt EL*Real.sqrt ER := by
  have hXp : 0 < X := (by positivity : 0 < U*V^2).trans_le hX
  have hGp : 0 < G := by linarith
  have hHp : 0 < H := by linarith
  have hJp : 0 < J := by linarith
  have hEp : 0 < E := by linarith
  have hFp : 0 < F := by linarith
  have hRp : 0 < R := by linarith
  have hbp : 0 < b := by linarith
  have hrhop : 0 < rho := by linarith [hrho.1]
  have hDp : 0 < D := by rw [hD]; positivity
  have hsplit := NaturalSqrtBudget.sqrt_product_polynomial nL nR KL KR Ch Cs Zl W Deps
    (V/(H*J*F)) (V/(H*J*E)) fL fR EL ER hnL0 hnR0 hKL0 hKR0 hCh hCs hZl hW hDeps
    (by positivity) (by positivity) hfL0 hfR0 hEL hER hnR hnL hKL hKR
  have hphysical := physical_source2_cost_le U V X G H J E F R r b rho Nb Bad δ D T
    hU hV hX hG hH hJ hE hF hR hpuncture hr hb hbBad hrho hNb hδ hD hT
  rw [← hfL,← hfR] at hphysical
  let pref := X/(b*R*Real.sqrt ((E*F*J)*D^2))
  have hpref : 0 ≤ pref := by dsimp [pref]; positivity
  change pref/(1+r)^2*Real.sqrt ((V/(H*J*E))*(V/(H*J*F)))*Real.sqrt (fL*fR) ≤ _ at hphysical
  calc
    _ = (8*pref*C/(1+r)^2)*
        (Real.sqrt (nR*KL*(Deps*W)*EL)*Real.sqrt (nL*KR*(Deps*W)*ER)) := by dsimp [pref]; ring
    _ ≤ (8*pref*C/(1+r)^2)*(16*Ch*Cs*Deps*Zl*W^2*
        Real.sqrt ((V/(H*J*E))*(V/(H*J*F)))*Real.sqrt (fL*fR)*Real.sqrt EL*Real.sqrt ER) :=
      mul_le_mul_of_nonneg_left hsplit (by positivity)
    _ = (8*16*C*Ch*Cs*Deps*Zl*W^2*Real.sqrt EL*Real.sqrt ER)*
        (pref/(1+r)^2*Real.sqrt ((V/(H*J*E))*(V/(H*J*F)))*Real.sqrt (fL*fR)) := by ring
    _ ≤ (8*16*C*Ch*Cs*Deps*Zl*W^2*Real.sqrt EL*Real.sqrt ER)*(16384*Bad*X) :=
      mul_le_mul_of_nonneg_left hphysical (by positivity)
    _ = _ := by ring

end
end Qrh.JointDetector.NaturalRootBudget

#print axioms Qrh.JointDetector.NaturalRootBudget.physical_source2_cost_le
#print axioms Qrh.JointDetector.NaturalRootBudget.complete_root_budget
