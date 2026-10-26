/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row189_coefficients : Fin 3 → Fin 4 → ℝ := ![![(29444718951575361526300200612178153/704033676743403722077125000000000:ℝ),(1325530418717530723634644409752122211/19008909272071900496082375000000000:ℝ),(295256869956402230390777445970797277/9504454636035950248041187500000000:ℝ),(18451364571361623181391794671641237/9504454636035950248041187500000000:ℝ)],
![(22836225850981388722275271659495949/176008419185850930519281250000000:ℝ),(1125416471458996782124495095724262237/4752227318017975124020593750000000:ℝ),(122710123629926148714493001915023541/950445463603595024804118750000000:ℝ),(89320242170407955619914042407246091/4752227318017975124020593750000000:ℝ)],
![(12763335000126316675821890154324403/117338946123900620346187500000000:ℝ),(2093368302086272298198806658166605081/9504454636035950248041187500000000:ℝ),(1363362439077886711142434582711060033/9504454636035950248041187500000000:ℝ),(56660320401242945715843350408946319/1900890927207190049608237500000000:ℝ)]]
theorem row189_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (18451364571361623181391794671641237/17302331639645889873767424000000000000:ℝ) row189_coefficients (9/16:ℝ) (3/4:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newTop,edgeC_newTop,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row189_coefficients,Fin.sum_univ_succ]
 ring
theorem row189_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/16:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row189_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row189_coefficients]
#print axioms row189_identity
#print axioms row189_pos
end
end LewkoStage2Finite
