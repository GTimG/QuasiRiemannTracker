/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row034_coefficients : Fin 3 → Fin 4 → ℝ := ![![(12248171398038528438562644624107/35552292458267869453125000:ℝ),(11515652169976734874873958570233/11850764152755956484375000:ℝ),(4052164465305648863350330835644/4444036557283483681640625:ℝ),(252947288501263949467046327464/888807311456696736328125:ℝ)],
![(243681431991929253051444417941/404003323389407607421875:ℝ),(7511995784799555091334713921351/4444036557283483681640625:ℝ),(777765503698725219081891996736/493781839698164853515625:ℝ),(722738402814947275074713382208/1481345519094494560546875:ℝ)],
![(387546061366417752086107731074/1481345519094494560546875:ℝ),(3233497720426478048095257688198/4444036557283483681640625:ℝ),(597588648493254533136947468416/888807311456696736328125:ℝ),(916988637799765052714677847104/4444036557283483681640625:ℝ)]]
theorem row034_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (14327947465621328948666841361/129441946585835727360000000000:ℝ) row034_coefficients (33/64:ℝ) (9/16:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row034_coefficients,Fin.sum_univ_succ]
 ring
theorem row034_pos {δ p : ℝ} (hd : δ∈Set.Icc (33/64:ℝ) (9/16:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row034_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row034_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row034_pos
