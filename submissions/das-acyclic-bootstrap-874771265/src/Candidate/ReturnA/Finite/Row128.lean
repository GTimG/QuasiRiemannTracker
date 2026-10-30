/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row128_coefficients : Fin 3 → Fin 4 → ℝ := ![![(27687498874717436619424140318977125904/1532107964309842402998046875:ℝ),(243660817361482432302890148449043778864/4596323892929527208994140625:ℝ),(238181167058114309148407618880348987392/4596323892929527208994140625:ℝ),(15516551577745664832574836115147317248/919264778585905441798828125:ℝ)],
![(55171457645276821079363457911638920856/1532107964309842402998046875:ℝ),(1210624204741644867449859614244163528/11462154346457673837890625:ℝ),(67781687664603265540405421045615067136/656617698989932458427734375:ℝ),(22075100437549349857096011717651808256/656617698989932458427734375:ℝ)],
![(27488815654538434931521265330376071177/1532107964309842402998046875:ℝ),(241843077168624920788354554958812936139/4596323892929527208994140625:ℝ),(47266822379545845009766571603805386752/919264778585905441798828125:ℝ),(76957392700081594605493961094310961152/4596323892929527208994140625:ℝ)]]
theorem row128_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (9394212976084179028990962047645381/4386902400434605554527109120000000000:ℝ) row128_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row128_coefficients,Fin.sum_univ_succ]
 ring
theorem row128_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
 rw [row128_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row128_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row128_pos
