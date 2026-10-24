/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row022_coefficients : Fin 3 → Fin 4 → ℝ := ![![(106614186167288778680141173043875824893/373744906889888469796875000:ℝ),(1590969757482420533759991361379646460147/1868724534449442348984375000:ℝ),(1582743561734518879077642862647993737099/1868724534449442348984375000:ℝ),(524844725199851532706965642612726401417/1868724534449442348984375000:ℝ)],
![(528128594198399399704135479518391637249/934362267224721174492187500:ℝ),(225166289054352198614069394510475130773/133480323889245882070312500:ℝ),(62718365100078184003269382187907871607/37374490688988846979687500:ℝ),(519923688368611253437945765705262512013/934362267224721174492187500:ℝ)],
![(523207785712313149030171846108023274633/1868724534449442348984375000:ℝ),(499655321550784254700035594804027383/597991851023821551675000:ℝ),(221891327082696552313174775701201663343/266960647778491764140625000:ℝ),(515024185430728095159083266285099346159/1868724534449442348984375000:ℝ)]]
theorem row022_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (515024185430728095159083266285099346159/3652772186199918480190718607360000000000:ℝ) row022_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row022_coefficients,Fin.sum_univ_succ]
 ring
theorem row022_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row022_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row022_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row022_pos
