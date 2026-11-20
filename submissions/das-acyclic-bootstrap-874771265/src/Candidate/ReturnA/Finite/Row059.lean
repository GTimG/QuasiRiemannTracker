/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row059_coefficients : Fin 3 → Fin 4 → ℝ := ![![(382581320152705634459482362510723604237457/747489813779776939593750000000:ℝ),(32624764566705970165665074001085750643131/21356851822279341131250000000:ℝ),(2958340125622105615838518120428181305088/1946588056718169113525390625:ℝ),(327011421448933278108943782751427042432/648862685572723037841796875:ℝ)],
![(38097393630366366772556624313008193472831/37374490688988846979687500000:ℝ),(63169443253199283707640315158137133014307/20763605938327137210937500000:ℝ),(17674862739462433494058772520620941897216/5839764170154507340576171875:ℝ),(5861174406079802698859179066849278467072/5839764170154507340576171875:ℝ)],
![(31614265662682881075338235000735899536771/62290817814981411632812500000:ℝ),(11322470906794291295817422679048142045681/7474898137797769395937500000:ℝ),(8799950802357917185958357564758522004224/5839764170154507340576171875:ℝ),(2918107725445727645221846319086776612608/5839764170154507340576171875:ℝ)]]
theorem row059_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (11398858302522373614147837183932721143/178358016904292894540562432000000000000:ℝ) row059_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row059_coefficients,Fin.sum_univ_succ]
 ring
theorem row059_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row059_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row059_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row059_pos
