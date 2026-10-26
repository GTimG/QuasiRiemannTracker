/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row041_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5111596397681155004039895928783/3333056677634565263671875:ℝ),(14921830643039024988073240467167/3333056677634565263671875:ℝ),(5805777232624362509111612742829/1333222671053826105468750:ℝ),(3136120673185813230154442587459/2222037785089710175781250:ℝ)],
![(3051010558108989760964588923646/1111018892544855087890625:ℝ),(26648583629242895652131710528982/3333056677634565263671875:ℝ),(1033993371463351899134689342196/133322267105382610546875:ℝ),(2784740165056463374514190348952/1111018892544855087890625:ℝ)],
![(817329337368364182888013492021/666611335526913052734375:ℝ),(29288357976262923783594465623/8229769574406333984375:ℝ),(2293964216455600193600327848613/666611335526913052734375:ℝ),(246309895674871369058073625057/222203778508971017578125:ℝ)]]
theorem row041_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (246309895674871369058073625057/3313742922721035288576000000000:ℝ) row041_coefficients (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row041_coefficients,Fin.sum_univ_succ]
 ring
theorem row041_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row041_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row041_coefficients]
#print axioms row041_identity
#print axioms row041_pos
end
end LewkoStage1Finite
