/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row093_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1107491566010905502753899579927559792/61283917193750832919921875:ℝ),(9746358837649783445432346990556870672/183851751581252498759765625:ℝ),(9527174457941266475350212858188374016/183851751581252498759765625:ℝ),(620657356208295079959199554857836544/36770350316250499751953125:ℝ)],
![(2206841531727412796360506148065026088/61283917193750832919921875:ℝ),(19418264578028450395438141984781966744/183851751581252498759765625:ℝ),(18978728157600906845701470735501008896/183851751581252498759765625:ℝ),(6180981077801381219929716270226620416/183851751581252498759765625:ℝ)],
![(1099544239353464732441493357686902271/61283917193750832919921875:ℝ),(9673649262057840644368811485484829097/183851751581252498759765625:ℝ),(1890658459273194061407946639022703616/36770350316250499751953125:ℝ),(3078272192662510541396356682806583296/183851751581252498759765625:ℝ)]]
theorem row093_identity (δ p : ℝ) : rowMargin .oldSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (375765648518372868822797446631663/175474946745287948642549760000000000:ℝ) row093_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row093_coefficients,Fin.sum_univ_succ]
 ring
theorem row093_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .C δ p := by
 rw [row093_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row093_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row093_pos
