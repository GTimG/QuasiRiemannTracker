/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row062_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6062312100999752479981609548347/4444036675863455039062500:ℝ),(52968180350315168192879657159123/13332110027590365117187500:ℝ),(51400317738350580343634160758123/13332110027590365117187500:ℝ),(5539645422204617621113319081347/4444036675863455039062500:ℝ)],
![(16227370305993639510636846908033/6666055013795182558593750:ℝ),(47117889498717464648043032489251/6666055013795182558593750:ℝ),(45579674659076769818801307230903/6666055013795182558593750:ℝ),(979266953299336418753320609979/444403667586345503906250:ℝ)],
![(577946264108991843838621296961/533284401103614604687500:ℝ),(1548435076402306177200376252577/493781852873717226562500:ℝ),(40296771997191415505072150741633/13332110027590365117187500:ℝ),(4312505084501585525507560198693/4444036675863455039062500:ℝ)]]
theorem row062_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (4312505084501585525507560198693/66274278420340597063680000000000:ℝ) row062_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row062_coefficients,Fin.sum_univ_succ]
 ring
theorem row062_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (33/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row062_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row062_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row062_pos
