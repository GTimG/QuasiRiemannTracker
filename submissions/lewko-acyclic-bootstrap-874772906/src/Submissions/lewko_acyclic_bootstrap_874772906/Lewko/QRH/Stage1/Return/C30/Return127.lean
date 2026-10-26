/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Return.C30
noncomputable section
def row127_coefficients : Fin 3 → Fin 4 → ℝ := ![![(35813226225510754884666279694181504452/7463799609551734993913671875:ℝ), (525700761784611972538290905645133971708/37318998047758674969568359375:ℝ), (514299172262329220592534967572219503836/37318998047758674969568359375:ℝ), (167664364749973899739795497897993054388/37318998047758674969568359375:ℝ)],
![(355671580415247297277556367156453522472/37318998047758674969568359375:ℝ), (1043897288180665188978801248429411510008/37318998047758674969568359375:ℝ), (40838921669182301388380336069135378072/1492759921910346998782734375:ℝ), (332746978014870750409440557955426464264/37318998047758674969568359375:ℝ)],
![(176725662122095216752874623836175045812/37318998047758674969568359375:ℝ), (4148449258084784992253410401900442732/298551984382069399756546875:ℝ), (507032495950082647742004738862970013364/37318998047758674969568359375:ℝ), (165201821710523557161896571836589717676/37318998047758674969568359375:ℝ)]]
theorem row127_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (41300455427630889290474142959147429419/18236743240204669735206672924672000000000:ℝ) row127_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row127_coefficients,Fin.sum_univ_succ]
 ring
theorem row127_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
 rw [row127_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row127_coefficients]
#print axioms row127_identity
#print axioms row127_pos
end
end LewkoStage1Return.C30
