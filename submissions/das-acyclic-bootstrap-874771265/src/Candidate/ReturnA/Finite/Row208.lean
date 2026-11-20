/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row208_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2500559164721930400807987908848504890308/4475978947149674314797548828125:ℝ),(523671811891835900728595588062143230718964/362554294719123619498601455078125:ℝ),(440569183662546457937493643540490091075584/362554294719123619498601455078125:ℝ),(119440988320658078285866135066071850221568/362554294719123619498601455078125:ℝ)],
![(133778735026195397220806950935348030303968/120851431573041206499533818359375:ℝ),(1034842722836558607059005605665500670071328/362554294719123619498601455078125:ℝ),(123915772438861063633901235249787035860992/51793470674160517071228779296875:ℝ),(46780103221173588571750676066779284373504/72510858943824723899720291015625:ℝ)],
![(66632301052890169102936112985487325711552/120851431573041206499533818359375:ℝ),(1035168982085965121533841500787846664512/729485502452965029172236328125:ℝ),(86027886328082640447947567088627312197632/72510858943824723899720291015625:ℝ),(115555653216948768015945012654476245860352/362554294719123619498601455078125:ℝ)]]
theorem row208_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (220404917177102600128068948086693279/1351700380940088065562188513280000000000:ℝ) row208_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row208_coefficients,Fin.sum_univ_succ]
 ring
theorem row208_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row208_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row208_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row208_pos
