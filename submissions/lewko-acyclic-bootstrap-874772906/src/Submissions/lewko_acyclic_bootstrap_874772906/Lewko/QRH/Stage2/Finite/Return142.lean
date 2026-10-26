/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row142_coefficients : Fin 3 → Fin 4 → ℝ := ![![(400215717214044195386885886218370959/38017818544143800992164750000000000:ℝ),(800903426558396132445884902695549293/38017818544143800992164750000000000:ℝ),(493810342373596178004218280729166159/38017818544143800992164750000000000:ℝ),(3519678621213456286748927820079513/1520712741765752039686590000000000:ℝ)],
![(727348035364395243246646543050602831/19008909272071900496082375000000000:ℝ),(1417171162330725442975265906170513277/19008909272071900496082375000000000:ℝ),(829869921947934423555571666902068461/19008909272071900496082375000000000:ℝ),(25957091996757711254792033256431603/3801781854414380099216475000000000:ℝ)],
![(2271050546927347922855679199882834703/38017818544143800992164750000000000:ℝ),(5187229047978652975284090977556919661/38017818544143800992164750000000000:ℝ),(3900990705098193254288637754344015013/38017818544143800992164750000000000:ℝ),(192857906810251373350848340333986011/7603563708828760198432950000000000:ℝ)]]
theorem row142_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (3519678621213456286748927820079513/692093265585835594950696960000000000:ℝ) row142_coefficients (3/8:ℝ) (3/4:ℝ) (0:ℝ) (1/4:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newTop,edgeC_newTop,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row142_coefficients,Fin.sum_univ_succ]
 ring
theorem row142_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/4:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row142_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row142_coefficients]
#print axioms row142_identity
#print axioms row142_pos
end
end LewkoStage2Finite
