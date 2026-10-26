/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row100_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1386827454518875111711937017956821729152/36725025273689068814410716796875:ℝ),(3981334937985937932027600381812844355456/36725025273689068814410716796875:ℝ),(3805209204281546713168088810484978323456/36725025273689068814410716796875:ℝ),(1210690385728438381826575446628955697152/36725025273689068814410716796875:ℝ)],
![(2716048140619496450242977288532768841312/36725025273689068814410716796875:ℝ),(7782107151162034692178447965997672406624/36725025273689068814410716796875:ℝ),(7422253506944814820591994143521359552512/36725025273689068814410716796875:ℝ),(94246850379035331242141238642258239488/1469001010947562752576428671875:ℝ)],
![(53755564645610154402412288415568140062/1469001010947562752576428671875:ℝ),(3844529103171990759936794322797302706158/36725025273689068814410716796875:ℝ),(3660554410047408167754508350775225565696/36725025273689068814410716796875:ℝ),(1159902514090894702856487582117126361088/36725025273689068814410716796875:ℝ)]]
theorem row100_identity (δ p : ℝ) : rowMargin .oldSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (283179324729222339564572163602814053/136920818138253472075162779648000000000:ℝ) row100_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row100_coefficients,Fin.sum_univ_succ]
 ring
theorem row100_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .C δ p := by
 rw [row100_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row100_coefficients]
#print axioms row100_identity
#print axioms row100_pos
end
end LewkoStage1Finite
