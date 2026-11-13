/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row212_coefficients : Fin 3 → Fin 4 → ℝ := ![![(541470224372677305452141747794632903872/243161834150988343057412109375:ℝ),(2070930575375966996013860848138115111856448/362554294719123619498601455078125:ℝ),(344688042725774223284805338731244521750528/72510858943824723899720291015625:ℝ),(459834777633824672300788769611342656569344/362554294719123619498601455078125:ℝ)],
![(36009496331940417681407875472767317883616/8056762104869413766635587890625:ℝ),(4156556226681731112094261054817086875900896/362554294719123619498601455078125:ℝ),(3459003005522797868851770093468912167698432/362554294719123619498601455078125:ℝ),(131837162768231394070330424038001549508608/51793470674160517071228779296875:ℝ)],
![(38771486705724648159335502718089448925108/17264490224720172357076259765625:ℝ),(2088933724457766075152309414967174116954548/362554294719123619498601455078125:ℝ),(248408714303551281023952318863972422854656/51793470674160517071228779296875:ℝ),(66303069596504855662083138005902837743616/51793470674160517071228779296875:ℝ)]]
theorem row212_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (877065234439515442468240298483548463/5406801523760352262248754053120000000000:ℝ) row212_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row212_coefficients,Fin.sum_univ_succ]
 ring
theorem row212_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row212_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row212_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row212_pos
