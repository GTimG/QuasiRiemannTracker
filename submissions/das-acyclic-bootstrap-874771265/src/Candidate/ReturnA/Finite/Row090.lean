/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row090_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7624285175673465486465137053573958/183852955717181088359765625:ℝ),(549600070022006275080616131442028476/4596323892929527208994140625:ℝ),(1055487209049745335609480995360584879/9192647785859054417988281250:ℝ),(16071363514615807551005767075844087/437745132659954972285156250:ℝ)],
![(74245106208646720682399562855968192/919264778585905441798828125:ℝ),(1068292389908683143100742206946279456/4596323892929527208994140625:ℝ),(1023655241942628361279359821230865032/4596323892929527208994140625:ℝ),(15551696191344334547031285288782216/218872566329977486142578125:ℝ)],
![(36497302212998943314661664166161552/919264778585905441798828125:ℝ),(104853031469772870085267770824887856/919264778585905441798828125:ℝ),(100290637818964433498635464887591056/919264778585905441798828125:ℝ),(1520696436739485443200624201374512/43774513265995497228515625:ℝ)]]
theorem row090_identity (δ p : ℝ) : rowMargin .oldSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (95043527296217840200039012585907/41780022861281957662162944000000000:ℝ) row090_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row090_coefficients,Fin.sum_univ_succ]
 ring
theorem row090_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSwitch .C δ p := by
 rw [row090_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row090_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row090_pos
