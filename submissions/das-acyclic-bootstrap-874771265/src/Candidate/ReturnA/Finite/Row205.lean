/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row205_coefficients : Fin 3 → Fin 4 → ℝ := ![![(69832184236667975912250844913965383175372/120851431573041206499533818359375:ℝ),(546961524787725484673666892737782389365716/362554294719123619498601455078125:ℝ),(466273555486061616633605583751159721744384/362554294719123619498601455078125:ℝ),(128806950583061905771076094410925825654784/362554294719123619498601455078125:ℝ)],
![(27387650941559907317179590265852764558896/24170286314608241299906763671875:ℝ),(1068189856020329938661511381863969575724432/362554294719123619498601455078125:ℝ),(905626317795328903869841198229378908217344/362554294719123619498601455078125:ℝ),(248247938903719984056942229476997675876352/362554294719123619498601455078125:ℝ)],
![(3213082568824688256075806762111779384048/5754830074906724119025419921875:ℝ),(524536404384606413059753697414389539268816/362554294719123619498601455078125:ℝ),(88530194108039900395231689342667317501952/72510858943824723899720291015625:ℝ),(120537113752396981728923902452723524435968/362554294719123619498601455078125:ℝ)]]
theorem row205_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (919625196475196698981658191320217319/5406801523760352262248754053120000000000:ℝ) row205_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row205_coefficients,Fin.sum_univ_succ]
 ring
theorem row205_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row205_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row205_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row205_pos
