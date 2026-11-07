/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row166_coefficients : Fin 3 → Fin 4 → ℝ := ![![(19060433147465993680784819420522772749145733/20423110420492134169921875000000:ℝ),(19075446206674931554872389142295943150485787/10211555210246067084960937500000:ℝ),(299149212722620025430045765236381953001216/319111100320189596405029296875:ℝ),(860690683874783522772656964758478467072/319111100320189596405029296875:ℝ)],
![(38073163841255202622323683338725941159033951/20423110420492134169921875000000:ℝ),(38061269847227989219122708404153814250854529/10211555210246067084960937500000:ℝ),(594933672278922172896335000482736219452672/319111100320189596405029296875:ℝ),(411982400425590961682774977802334429184/319111100320189596405029296875:ℝ)],
![(15235443521296935058333498001757559390826729/16338488336393707335937500000000:ℝ),(3045306632174725068600698101896033449675531/1633848833639370733593750000000:ℝ),(297263367893482764438271696119053133775808/319111100320189596405029296875:ℝ),(44076409201413645912060861934334332928/319111100320189596405029296875:ℝ)]]
theorem row166_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (10760842090188878396499233870687093/4990099418374287615149998080000000000000000:ℝ) row166_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row166_coefficients,Fin.sum_univ_succ]
 ring
theorem row166_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row166_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row166_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row166_pos
