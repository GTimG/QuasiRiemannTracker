/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row181_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1015702693404927784885073104893632447/37300812351778276537500000000000:ℝ),(204985633586960884234019756841709439/3390982941070752412500000000000:ℝ),(137429570394100294023395915376443197/3390982941070752412500000000000:ℝ),(18138842199559401477600473212546919/2486720823451885102500000000000:ℝ)],
![(6286739900009589326162149344708799999/93252030879445691343750000000000:ℝ),(14438605344604643375397006158842487249/93252030879445691343750000000000:ℝ),(25712216792571480748776488811117037/233130077198614228359375000000:ℝ),(14201685088921011753684120547212517/621680205862971275625000000000:ℝ)],
![(44477686979331187167547127113586583521/932520308794456913437500000000000:ℝ),(9872289267986851344278433404964904643/84774573526768810312500000000000:ℝ),(170434772282068752027704540571575616319/1865040617588913826875000000000000:ℝ),(2811288582998076361947928865265142081/124336041172594255125000000000000:ℝ)]]
theorem row181_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (18138842199559401477600473212546919/37084668788222348419399680000000000000:ℝ) row181_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row181_coefficients,Fin.sum_univ_succ]
 ring
theorem row181_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (33/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row181_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row181_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row181_pos
