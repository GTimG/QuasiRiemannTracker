/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row130_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5524041767242471758200340752752856723/9192647785859054417988281250:ℝ),(15861935095376937553876918882360938227/9192647785859054417988281250:ℝ),(216624370429133390152938074953404928/131323539797986491685546875:ℝ),(344697701743513751381249251111983104/656617698989932458427734375:ℝ)],
![(5491410648544953577870298908897220384/4596323892929527208994140625:ℝ),(15760226941557897525105804510421703456/4596323892929527208994140625:ℝ),(3011650552673040525155405266643812352/919264778585905441798828125:ℝ),(4789391411237110003631736981694578688/4596323892929527208994140625:ℝ)],
![(546245317533319724820819527379410432/919264778585905441798828125:ℝ),(1566947755729929565230520338922282496/919264778585905441798828125:ℝ),(1496369660402805332152760747487133696/919264778585905441798828125:ℝ),(475662687955614493009999935944261632/919264778585905441798828125:ℝ)]]
theorem row130_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (453627288776030056962966857857/214204218771220974342144000000000:ℝ) row130_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row130_coefficients,Fin.sum_univ_succ]
 ring
theorem row130_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
 rw [row130_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row130_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row130_pos
