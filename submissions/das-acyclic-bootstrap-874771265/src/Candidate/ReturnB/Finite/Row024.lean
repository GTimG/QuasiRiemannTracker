/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row024_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1117865108036934251369998118614484807/996646546239672178125000:ℝ),(83403188884276502839636556208054433871/24916163655991804453125000:ℝ),(34918936214059528258132424064289792/10486600865316416015625:ℝ),(1146284613771340093415360665312405504/1038173485666325185546875:ℝ)],
![(13907844159348275886823198771099381061/6229040913997951113281250:ℝ),(13835156573489996030083646964985897591/2076346971332650371093750:ℝ),(20643928084044469945572547362321362944/3114520456998975556640625:ℝ),(6845115170380016486302188164298457088/3114520456998975556640625:ℝ)],
![(2307086337722715404428202010126615037/2076346971332650371093750:ℝ),(20654887854452745920623315059099411799/6229040913997951113281250:ℝ),(2054622342865185330822992424985247744/622904091399795111328125:ℝ),(3406297226921885539084466873535205376/3114520456998975556640625:ℝ)]]
theorem row024_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (831615533916475961690543670296681/5945228224681588587233280000000000:ℝ) row024_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row024_coefficients,Fin.sum_univ_succ]
 ring
theorem row024_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row024_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row024_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row024_pos
