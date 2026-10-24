/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row186_coefficients : Fin 3 → Fin 4 → ℝ := ![![(163702384474366468994819112250221798031/33971638293041613890625000000000:ℝ),(348251505162243560197351203121951369321/33971638293041613890625000000000:ℝ),(8133543719768725940932705499294731997/1327017120821938042602539062500:ℝ),(231045132568795813754656626962848868/331754280205484510650634765625:ℝ)],
![(482822628238211201128819698006122647183/42464547866302017363281250000000:ℝ),(1080575915334682206612656106133794930409/42464547866302017363281250000000:ℝ),(224970700109829814966484921398399129/13270171208219380426025390625:ℝ),(954108327424316374865540047021211608/331754280205484510650634765625:ℝ)],
![(294737074117522920543873415103985931907/42464547866302017363281250000000:ℝ),(694597331956494942788708276776829684501/42464547866302017363281250000000:ℝ),(3974055365055596247385847587054199849/331754280205484510650634765625:ℝ),(850038710018255746816701278082233276/331754280205484510650634765625:ℝ)]]
theorem row186_identity (δ p : ℝ) : rowMargin .newTop .P δ p =
 Record12518109.Bernstein.bsum 2 3 (57761283142198953438664156740712217/1266554474480512118292480000000000000000:ℝ) row186_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row186_coefficients,Fin.sum_univ_succ]
 ring
theorem row186_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .P δ p := by
 rw [row186_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row186_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row186_pos
