/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row187_coefficients : Fin 3 → Fin 4 → ℝ := ![![(190775326254385459435216788305710857437/2376113659008987562010296875000000:ℝ),(74559002666468535979401770508568086913/475222731801797512402059375000000:ℝ),(5828696170424811413157735002932550267/74253551844030861312821777343750:ℝ),(68080880510907774856105983777971194/37126775922015430656410888671875:ℝ)],
![(113584496808533923044083087327119452403/594028414752246890502574218750000:ℝ),(235157151190229632093739535745121110987/594028414752246890502574218750000:ℝ),(1705907316391424466546669300586793278/7425355184403086131282177734375:ℝ),(926616057350172901495558352272729916/37126775922015430656410888671875:ℝ)],
![(2803394731287047300097073731881933093/23761136590089875620102968750000:ℝ),(154280442094954568726366229961717654277/594028414752246890502574218750000:ℝ),(6369408546671465802485646928835470144/37126775922015430656410888671875:ℝ),(1104760141312786007681013292298520022/37126775922015430656410888671875:ℝ)]]
theorem row187_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (34040440255453887428052991888985597/1107349224937336951921115136000000000000:ℝ) row187_coefficients (63/128:ℝ) (33/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newTop,edgeC_newTop,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row187_coefficients,Fin.sum_univ_succ]
 ring
theorem row187_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row187_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row187_coefficients]
#print axioms row187_identity
#print axioms row187_pos
end
end LewkoStage2Finite
