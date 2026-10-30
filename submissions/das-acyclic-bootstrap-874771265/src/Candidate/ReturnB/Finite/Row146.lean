/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row146_coefficients : Fin 3 → Fin 4 → ℝ := ![![(44475514631120341526785814373251949607/1865040617588913826875000000000000:ℝ),(102162137978406889656577492474402057361/1865040617588913826875000000000000:ℝ),(36465976221756828341120236144495468547/932520308794456913437500000000000:ℝ),(253749046699654376684642371484117989/31084010293148563781250000000000:ℝ)],
![(8510413666450573697609745999595907567/186504061758891382687500000000000:ℝ),(1684467954094154339762552905537607087/16954914705353762062500000000000:ℝ),(217713651777426728051339238315389993/3390982941070752412500000000000:ℝ),(26013156420836180925433178543215723/2486720823451885102500000000000:ℝ)],
![(2185373306484094900216662728015436619/74601624703556553075000000000000:ℝ),(4971587697935857444487984205202122833/74601624703556553075000000000000:ℝ),(3485354307692924459854259692966265509/74601624703556553075000000000000:ℝ),(4231110216127402271360792209724723/452131058809433655000000000000:ℝ)]]
theorem row146_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (26013156420836180925433178543215723/74169337576444696838799360000000000000:ℝ) row146_coefficients (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row146_coefficients,Fin.sum_univ_succ]
 ring
theorem row146_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row146_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row146_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row146_pos
