/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row091_coefficients : Fin 3 → Fin 4 → ℝ := ![![(710017307806909058097566328364123462/4596323892929527208994140625:ℝ),(58401980233223664414298961312215874/131323539797986491685546875:ℝ),(1959529939635564844019495502644870144/4596323892929527208994140625:ℝ),(625472551314697445215829231956438016/4596323892929527208994140625:ℝ)],
![(1398208588036416250028204421671648342/4596323892929527208994140625:ℝ),(574406626439354180094228604253565626/656617698989932458427734375:ℝ),(549998254989797753507977352253251584/656617698989932458427734375:ℝ),(1227339073806677469317759829544450048/4596323892929527208994140625:ℝ)],
![(276011241188955246905842879073514007/1838529557171810883597656250:ℝ),(3964512923385740168288786418435163859/9192647785859054417988281250:ℝ),(270843764137358874410850855816238592/656617698989932458427734375:ℝ),(603672463237538745188938053398623232/4596323892929527208994140625:ℝ)]]
theorem row091_identity (δ p : ℝ) : rowMargin .oldSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (589523889880408930848572317772093/274181400027162847157944320000000000:ℝ) row091_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row091_coefficients,Fin.sum_univ_succ]
 ring
theorem row091_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .C δ p := by
 rw [row091_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row091_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row091_pos
