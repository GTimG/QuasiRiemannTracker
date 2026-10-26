/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row215_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6954265187880078184669466214194149/3233702467151457072517715625000:ℝ),(15418560134054029109333445721934167/3233702467151457072517715625000:ℝ),(10540072351499128793089105165117637/3233702467151457072517715625000:ℝ),(2064877472568697075529882844877619/3233702467151457072517715625000:ℝ)],
![(46364068660873660928770037423123537/8084256167878642681294289062500:ℝ),(105915322991829106355309593185041507/8084256167878642681294289062500:ℝ),(76079570381403691430947080047276743/8084256167878642681294289062500:ℝ),(16462916453909361247036067410358773/8084256167878642681294289062500:ℝ)],
![(75106610700642505905223958297133281/16168512335757285362588578125000:ℝ),(184156014431965176131280115065467843/16168512335757285362588578125000:ℝ),(146937526616256945238119160491701659/16168512335757285362588578125000:ℝ),(37809643369087613303217255473367097/16168512335757285362588578125000:ℝ)]]
theorem row215_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2064877472568697075529882844877619/1507014576975913889454371635200000000:ℝ) row215_coefficients (15/32:ℝ) (9/16:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row215_coefficients,Fin.sum_univ_succ]
 ring
theorem row215_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row215_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row215_coefficients]
#print axioms row215_identity
#print axioms row215_pos
end
end LewkoStage2Finite
