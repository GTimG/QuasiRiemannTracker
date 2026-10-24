/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row142_coefficients : Fin 3 → Fin 4 → ℝ := ![![(12562401243036597712225665534839879/1193625995256904849200000000000000:ℝ),(628461323985907327509587542937085749/29840649881422621230000000000000000:ℝ),(387459370717804038842684721025011799/29840649881422621230000000000000000:ℝ),(2761246219489979636204352470356921/1193625995256904849200000000000000:ℝ)],
![(22832068543535062288662479904734279/596812997628452424600000000000000:ℝ),(1112112710879406126982275301481011853/14920324940711310615000000000000000:ℝ),(651188767556061708046390479922949293/14920324940711310615000000000000000:ℝ),(20364785124781562362683433332058883/2984064988142262123000000000000000:ℝ)],
![(71297767692254482039499294274628679/1193625995256904849200000000000000:ℝ),(4071216894571051094293197982834935341/29840649881422621230000000000000000:ℝ),(278337081325235971780755833934670991/2712786352856601930000000000000000:ℝ),(151365500606131598669615705702432507/5968129976284524246000000000000000:ℝ)]]
theorem row142_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2761246219489979636204352470356921/543232452952475806924800000000000000:ℝ) row142_coefficients (3/8:ℝ) (3/4:ℝ) (0/1:ℝ) (1/4:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row142_coefficients,Fin.sum_univ_succ]
 ring
theorem row142_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (3/4:ℝ)) (hp : p∈Set.Icc (0/1:ℝ) (1/4:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row142_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row142_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row142_pos
