/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row141_coefficients : Fin 3 → Fin 4 → ℝ := ![![(102170171801177046214947075818514353/29840838214035809480400000000000000:ℝ),(274055030783088270453359305703991059/29840838214035809480400000000000000:ℝ),(241599546162645402261877383952439059/29840838214035809480400000000000000:ℝ),(69714687180734178023465154066962353/29840838214035809480400000000000000:ℝ)],
![(14899727030548242475173444097515953/14920419107017904740200000000000000:ℝ),(37912843377595111802821425243557339/14920419107017904740200000000000000:ℝ),(34159097136021169190414419011790039/14920419107017904740200000000000000:ℝ),(11145980788974299862766437865748653/14920419107017904740200000000000000:ℝ)],
![(46992635116062676656999812376517553/29840838214035809480400000000000000:ℝ),(12509540280435110777910527954777083/5968167642807161896080000000000000:ℝ),(20476133187119317703386924988165509/29840838214035809480400000000000000:ℝ),(894119540053348621189254690797647/29840838214035809480400000000000000:ℝ)]]
theorem row141_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (894119540053348621189254690797647/1697612129509592717107200000000000000:ℝ) row141_coefficients (0/1:ℝ) (3/8:ℝ) (0/1:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row141_coefficients,Fin.sum_univ_succ]
 ring
theorem row141_pos {δ p : ℝ} (hd : δ∈Set.Icc (0/1:ℝ) (3/8:ℝ)) (hp : p∈Set.Icc (0/1:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row141_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row141_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row141_pos
