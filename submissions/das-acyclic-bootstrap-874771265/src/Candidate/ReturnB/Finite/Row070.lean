/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row070_coefficients : Fin 3 → Fin 4 → ℝ := ![![(55185114660435736943781193901/213313754749607216718750000:ℝ),(8265882329344684893334128961/12928106348461043437500000:ℝ),(14850709577174114246789344403/28441833966614295562500000:ℝ),(29980486851151142155313149067/213313754749607216718750000:ℝ)],
![(2331836068714099940192267117/5925382076377978242187500:ℝ),(971827616637627215250703157/1066568773748036083593750:ℝ),(36688563266723750126476311091/53328438687401804179687500:ℝ),(1491963264000086926570259549/8888073114566967363281250:ℝ)],
![(4359250882741942788895056617/26664219343700902089843750:ℝ),(4729807039824191280470474041/13332109671850451044921875:ℝ),(3280135248089547795104386894/13332109671850451044921875:ℝ),(128721043289369702673898393/2424019940336445644531250:ℝ)]]
theorem row070_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (128721043289369702673898393/4412793633608036160000000000:ℝ) row070_coefficients (9/16:ℝ) (3/4:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row070_coefficients,Fin.sum_univ_succ]
 ring
theorem row070_pos {δ p : ℝ} (hd : δ∈Set.Icc (9/16:ℝ) (3/4:ℝ)) (hp : p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row070_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row070_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row070_pos
