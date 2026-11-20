/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row057_coefficients : Fin 3 → Fin 4 → ℝ := ![![(194387500930161903778835810655949818035351/1494979627559553879187500000000:ℝ),(580205496370477837277886961466108946428069/1494979627559553879187500000000:ℝ),(192418337609924326956682685294809005874927/498326542519851293062500000000:ℝ),(63812337300131953780315341991422629744021/498326542519851293062500000000:ℝ)],
![(192770116364052807826824705131245912777991/747489813779776939593750000000:ℝ),(575358689712639375477503530732655614329221/747489813779776939593750000000:ℝ),(572413571426169669957819591485645392052057/747489813779776939593750000000:ℝ),(189824992553781022694621210334235690500827/747489813779776939593750000000:ℝ)],
![(191162028949421504382306725301801034955711/1494979627559553879187500000000:ℝ),(570539748383859802425456400013609224761077/1494979627559553879187500000000:ℝ),(16217141977014659376701670219994078286261/42713703644558682262500000000:ℝ),(188222244202311927873113787212984550213769/1494979627559553879187500000000:ℝ)]]
theorem row057_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (188222244202311927873113787212984550213769/2922217748959934784152574885888000000000000:ℝ) row057_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row057_coefficients,Fin.sum_univ_succ]
 ring
theorem row057_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row057_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row057_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row057_pos
