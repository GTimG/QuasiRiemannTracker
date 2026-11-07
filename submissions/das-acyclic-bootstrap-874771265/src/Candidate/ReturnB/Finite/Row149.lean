/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row149_coefficients : Fin 3 → Fin 4 → ℝ := ![![(74671883273872358009894070511459/10367660622656250000000000:ℝ),(7147328564380206014569220163323/414706424906250000000000:ℝ),(268139502430920962492953682447117/20735321245312500000000000:ℝ),(4007789383977025185618721020259/1382354749687500000000000:ℝ)],
![(70491222267410192404924254258961/5183830311328125000000000:ℝ),(32920070386254552318085049961619/1036766062265625000000000:ℝ),(3701897424330177966188148962117/161994697229003906250000:ℝ),(811719597156770857750659041287/172794343710937500000000:ℝ)],
![(71899989077844325476586685172949/10367660622656250000000000:ℝ),(6688692459414396685226097421439/414706424906250000000000:ℝ),(119483313785420598142711962247381/10367660622656250000000000:ℝ),(1611066091860333765909747458957/691177374843750000000000:ℝ)]]
theorem row149_identity (δ p : ℝ) : rowMargin .newTop .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (1611066091860333765909747458957/10554966118005473280000000000000000:ℝ) row149_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row149_coefficients,Fin.sum_univ_succ]
 ring
theorem row149_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newTop .capP δ p := by
 rw [row149_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row149_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row149_pos
