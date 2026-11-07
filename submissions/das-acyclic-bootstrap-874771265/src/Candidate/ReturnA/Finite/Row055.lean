/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row055_coefficients : Fin 3 → Fin 4 → ℝ := ![![(404317607121199896826696971615651866929/373744906889888469796875000000:ℝ),(120121702878291746697203717483074277321/37374490688988846979687500000:ℝ),(4758127507534871065739591364994806363709/1494979627559553879187500000000:ℝ),(14957423680494574148290750258423264177/14237901214852894087500000000:ℝ)],
![(4893159144069250792735979228681648197/2335905668061802936230468750:ℝ),(645947565160394637445798560399264179/103818029691635686054687500:ℝ),(16444346545920337499419952340108325537/2669606477784917641406250000:ℝ),(361763130188966429845681279412799163/177973765185661176093750000:ℝ)],
![(210488900534570254543120334665228631/207636059383271372109375000:ℝ),(160724153653592466824995181313561559/53392129555698352828125000:ℝ),(5567749401660390397226591686288157711/1868724534449442348984375000:ℝ),(3498673693024075687071034956762973/3559475303713223521875000:ℝ)]]
theorem row055_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (3498673693024075687071034956762973/54356728961308310717123788800000000:ℝ) row055_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row055_coefficients,Fin.sum_univ_succ]
 ring
theorem row055_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row055_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row055_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row055_pos
