/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row006_coefficients : Fin 3 → Fin 4 → ℝ := ![![(30639203052830830840688440173307/8888073114566967363281250:ℝ),(8128531089616394880921973302913/808006646778815214843750:ℝ),(34776101297857238518307802361081/3555229245826786945312500:ℝ),(18777004906541260181694316079311/5925382076377978242187500:ℝ)],
![(2469598440897493395607434012691/404003323389407607421875:ℝ),(8785166035635508626659581729471/493781839698164853515625:ℝ),(3066699861651537395760297824122/177761462291339347265625:ℝ),(8255488745005727026445525975804/1481345519094494560546875:ℝ)],
![(177056180429626550391698895467/65837578626421980468750:ℝ),(13870810243446548105748670963427/1777614622913393472656250:ℝ),(13406510162825422066059390812777/1777614622913393472656250:ℝ),(1438730127702255938338759175653/592538207637797824218750:ℝ)]]
theorem row006_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1438730127702255938338759175653/8836570220259718987776000000000:ℝ) row006_coefficients (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row006_coefficients,Fin.sum_univ_succ]
 ring
theorem row006_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row006_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row006_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row006_pos
