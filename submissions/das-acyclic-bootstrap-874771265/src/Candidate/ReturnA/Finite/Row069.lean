/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row069_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2101417277309036192127224134969/13332110027590365117187500:ℝ),(657744016177675355612229199087/1481345558621151679687500:ℝ),(2774382149545841468356334182967/6666055013795182558593750:ℝ),(86515957362622634411249297956/666605501379518255859375:ℝ)],
![(939539032200215382646654912234/3333027506897591279296875:ℝ),(2629589087680547507551793652934/3333027506897591279296875:ℝ),(815894424558464738527130670772/1111009168965863759765625:ℝ),(84171390897480338957673974624/370336389655287919921875:ℝ)],
![(139945449017410179399081576716/1111009168965863759765625:ℝ),(1166469424726861951752324837532/3333027506897591279296875:ℝ),(215429220329207981677581146104/666605501379518255859375:ℝ),(330463551179914472983450623136/3333027506897591279296875:ℝ)]]
theorem row069_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (10326985974372327280732831973/194162925059591592960000000000:ℝ) row069_coefficients (33/64:ℝ) (9/16:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row069_coefficients,Fin.sum_univ_succ]
 ring
theorem row069_pos {δ p : ℝ} (hd : δ∈Set.Icc (33/64:ℝ) (9/16:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row069_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row069_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row069_pos
