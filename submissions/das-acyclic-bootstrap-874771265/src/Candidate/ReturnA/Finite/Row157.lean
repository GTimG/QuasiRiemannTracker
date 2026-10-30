/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row157_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1435856269066444320777665884397828247188231/16338698211411323910815625000000000:ℝ),(674727299221065859492462915606164433614757/3267739642282264782163125000000000:ℝ),(122466486011478959390889691011486794088119/816934910570566195540781250000000:ℝ),(255765420122338085690956725691513910125913/8169349105705661955407812500000000:ℝ)],
![(1403979164713015847531688413438985335689523/8169349105705661955407812500000000:ℝ),(3263938111253423942411524814682245356414577/8169349105705661955407812500000000:ℝ),(2325684889186895297019297337308182091081187/8169349105705661955407812500000000:ℝ),(465707047454416980053797680653627226606133/8169349105705661955407812500000000:ℝ)],
![(1422274106857602442436644406370748725944891/16338698211411323910815625000000000:ℝ),(660861290403115684787620012367645177727373/3267739642282264782163125000000000:ℝ),(13438050740250746475574947423405769472419/93363989779493279490375000000000:ℝ),(469607393801729621559462300484623432481351/16338698211411323910815625000000000:ℝ)]]
theorem row157_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (465707047454416980053797680653627226606133/7984261629408748680648923598028800000000000000:ℝ) row157_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row157_coefficients,Fin.sum_univ_succ]
 ring
theorem row157_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row157_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row157_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row157_pos
