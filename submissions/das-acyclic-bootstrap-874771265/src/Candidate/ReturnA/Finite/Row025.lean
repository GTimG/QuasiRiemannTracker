/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row025_coefficients : Fin 3 → Fin 4 → ℝ := ![![(66518763727437096789847505269531505839/1868724534449442348984375000:ℝ),(197506171859626627581316439668223454511/1868724534449442348984375000:ℝ),(4886612401216220637421215347037688832/46718113361236058724609375:ℝ),(8059634737774896322459862939258200576/233590566806180293623046875:ℝ)],
![(16475915666669078863900512773308865128/233590566806180293623046875:ℝ),(48916547289585705748458542561106626152/233590566806180293623046875:ℝ),(1383070326228281512355671091881050112/6674016194462294103515625:ℝ),(15966827275762502997399697178038992896/233590566806180293623046875:ℝ)],
![(1632281315622757862479561023831670144/46718113361236058724609375:ℝ),(4845857026049932863700803417763560832/46718113361236058724609375:ℝ),(4795081780578795927477496988422111232/46718113361236058724609375:ℝ),(1581505816636076468345234594490220544/46718113361236058724609375:ℝ)]]
theorem row025_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (6032965914291673539524973276101/43544437720774632456192000000000:ℝ) row025_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row025_coefficients,Fin.sum_univ_succ]
 ring
theorem row025_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row025_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row025_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row025_pos
