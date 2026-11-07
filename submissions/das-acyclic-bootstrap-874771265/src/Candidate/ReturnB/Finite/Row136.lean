/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row136_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7656733778583686381824222201783886/191135956878830684794921875:ℝ),(4390846446665303883731514230570522/38227191375766136958984375:ℝ),(20954872856096954647706508670309712/191135956878830684794921875:ℝ),(2219104951294390225099391091309496/63711985626276894931640625:ℝ)],
![(15214476640624535367494914755864652/191135956878830684794921875:ℝ),(43566336807632034930351815218076612/191135956878830684794921875:ℝ),(41523212101824070927597617603027868/191135956878830684794921875:ℝ),(4390409978373329653382687328188636/63711985626276894931640625:ℝ)],
![(7636540116386867509841585298847766/191135956878830684794921875:ℝ),(21847190797476139153105640890512802/191135956878830684794921875:ℝ),(20802128315439942120247514207594906/191135956878830684794921875:ℝ),(439427676446746762698985438978658/12742397125255378986328125:ℝ)]]
theorem row136_identity (δ p : ℝ) : rowMargin .newSwitch .P δ p =
 Record12518109.Bernstein.bsum 2 3 (1097602494593332413345671832047159/486472701561033496838799360000000000:ℝ) row136_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row136_coefficients,Fin.sum_univ_succ]
 ring
theorem row136_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .P δ p := by
 rw [row136_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row136_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row136_pos
