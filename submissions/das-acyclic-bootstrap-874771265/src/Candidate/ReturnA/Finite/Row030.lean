/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row030_coefficients : Fin 3 → Fin 4 → ℝ := ![![(528890777210941287875112357254340152/233590566806180293623046875:ℝ),(224391274125298912493892811424563208/33370080972311470517578125:ℝ),(222124522095337442126780917257534208/33370080972311470517578125:ℝ),(513023433777603352208135348085137152/233590566806180293623046875:ℝ)],
![(1019505926811507515973999080760639382/233590566806180293623046875:ℝ),(3026983580482590497051872264076130454/233590566806180293623046875:ℝ),(2995582406284250775356553258701568512/233590566806180293623046875:ℝ),(197620918040954425185886577577215488/46718113361236058724609375:ℝ)],
![(785522443159862040523387564875556883/373744906889888469796875000:ℝ),(11658031877782281018437216562746382559/1868724534449442348984375000:ℝ),(205960034657445510359165757051582208/33370080972311470517578125:ℝ),(475417701619944440507636273471250688/233590566806180293623046875:ℝ)]]
theorem row030_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (1857100396952907970732954193247073/13934220070647882385981440000000000:ℝ) row030_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row030_coefficients,Fin.sum_univ_succ]
 ring
theorem row030_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row030_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row030_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row030_pos
