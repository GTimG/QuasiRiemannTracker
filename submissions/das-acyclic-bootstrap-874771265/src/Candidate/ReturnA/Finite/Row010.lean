/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row010_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1624617077911610399221057087/474319888593750000:ℝ),(4846594044167328286419633727/474319888593750000:ℝ),(301211087093855685329654528/29644993037109375:ℝ),(99837526702873317379743488/29644993037109375:ℝ)],
![(785155128509187143765136713/118579972148437500:ℝ),(2341886789543113860873876809/118579972148437500:ℝ),(582082207725740877954543616/29644993037109375:ℝ),(192899292467259198677358592/29644993037109375:ℝ)],
![(75843193058857882364849507/23715994429687500:ℝ),(1130885198046014238622864111/118579972148437500:ℝ),(281033251342010370014985728/29644993037109375:ℝ),(93115943154079163315331584/29644993037109375:ℝ)]]
theorem row010_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (181867076472810865850257/884196358225920000000000:ℝ) row010_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row010_coefficients,Fin.sum_univ_succ]
 ring
theorem row010_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row010_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row010_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row010_pos
