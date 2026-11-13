/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row147_coefficients : Fin 3 → Fin 4 → ℝ := ![![(19195248534966936897244470168647/41470642490625000000000000:ℝ),(46316133579203675131665105760037/41470642490625000000000000:ℝ),(35391435177256420918690403647969/41470642490625000000000000:ℝ),(8270550133019682684269768056579/41470642490625000000000000:ℝ)],
![(17503372919749588397625560291807/20735321245312500000000000:ℝ),(40475422272545364612760916184149/20735321245312500000000000:ℝ),(1152003091199033713160184323767/829412849812500000000000:ℝ),(5828027927180066613869252201833/20735321245312500000000000:ℝ)],
![(18675212590948734862145338273187/41470642490625000000000000:ℝ),(8631263157513839890098392625913/8294128498125000000000000:ℝ),(7665330706602266117532871196677/10367660622656250000000000:ℝ),(618021962978859988178485993033/4147064249062500000000000:ℝ)]]
theorem row147_identity (δ p : ℝ) : rowMargin .newTop .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (5828027927180066613869252201833/19790561471260262400000000000000000:ℝ) row147_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row147_coefficients,Fin.sum_univ_succ]
 ring
theorem row147_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newTop .capP δ p := by
 rw [row147_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row147_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row147_pos
