/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row001_coefficients : Fin 3 → Fin 4 → ℝ := ![![(14176050988594255564926257191/213313760441445841875000000:ℝ),(37282830741327536642318189653/213313760441445841875000000:ℝ),(32037508516872306589857607733/213313760441445841875000000:ℝ),(8930728764139025512465675271/213313760441445841875000000:ℝ)],
![(10096826349717854186843995327/106656880220722920937500000:ℝ),(24839541261262348068405796129/106656880220722920937500000:ℝ),(19815192439592388333639935777/106656880220722920937500000:ℝ),(202899101121915778083125399/4266275208828916837500000:ℝ)],
![(6870856752607236176261733463/213313760441445841875000000:ℝ),(3103467513748045163451149141/42662752088289168375000000:ℝ),(11158947053083349076331246571/213313760441445841875000000:ℝ),(2480776793893120557837234329/213313760441445841875000000:ℝ)]]
theorem row001_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2480776793893120557837234329/12135182816224474560000000000:ℝ) row001_coefficients (0/1:ℝ) (3/8:ℝ) (0/1:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row001_coefficients,Fin.sum_univ_succ]
 ring
theorem row001_pos {δ p : ℝ} (hd : δ∈Set.Icc (0/1:ℝ) (3/8:ℝ)) (hp : p∈Set.Icc (0/1:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row001_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row001_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row001_pos
