/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row112_coefficients : Fin 3 → Fin 4 → ℝ := ![![(20918397355333437744641147/9333115896796875000:ℝ),(59746632912261952517764049/9333115896796875000:ℝ),(56815899599432907548552857/9333115896796875000:ℝ),(3597532808500878555085991/1866623179359375000:ℝ)],
![(19516624893627610653939659/4666557948398437500:ℝ),(826493351841274165443899/69650118632812500:ℝ),(52281311562602655228774589/4666557948398437500:ℝ),(3284576376572979359594603/933311589679687500:ℝ)],
![(18780631164523605887879171/9333115896796875000:ℝ),(52985859474237766751547617/9333115896796875000:ℝ),(49714274854941707647456771/9333115896796875000:ℝ),(620361861809101871351533/373324635871875000:ℝ)]]
theorem row112_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (620361861809101871351533/178157455762312396800000000:ℝ) row112_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row112_coefficients,Fin.sum_univ_succ]
 ring
theorem row112_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
 rw [row112_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row112_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row112_pos
