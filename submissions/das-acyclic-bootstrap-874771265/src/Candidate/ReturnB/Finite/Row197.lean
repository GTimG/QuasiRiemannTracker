/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row197_coefficients : Fin 3 → Fin 4 → ℝ := ![![(28202727311300841075256777496/15337260259537587890625:ℝ),(22924495369605918819218583304/5112420086512529296875:ℝ),(1979523287542662509303706368/568046676279169921875:ℝ),(2575273993226994473760219904/3067452051907517578125:ℝ)],
![(17453507177417588809736460724/5112420086512529296875:ℝ),(124325716971521600521701262108/15337260259537587890625:ℝ),(3704315515451058245346509824/613490410381503515625:ℝ),(6880897482335874013723621888/5112420086512529296875:ℝ)],
![(50384434153719174766030455227/30674520519075175781250:ℝ),(117260476270292185692471441467/30674520519075175781250:ℝ),(42213705684975598686123494464/15337260259537587890625:ℝ),(8775684626689093222903001344/15337260259537587890625:ℝ)]]
theorem row197_identity (δ p : ℝ) : rowMargin .newKink .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (34280018073004270401964849/114362901432212520960000000000:ℝ) row197_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row197_coefficients,Fin.sum_univ_succ]
 ring
theorem row197_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .capC δ p := by
 rw [row197_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row197_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row197_pos
