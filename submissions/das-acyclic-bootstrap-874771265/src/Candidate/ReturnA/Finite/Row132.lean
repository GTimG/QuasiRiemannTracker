/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row132_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8964071637141044225211142979489/131166888930545703925781250:ℝ),(23625637549744705184828873840467/131166888930545703925781250:ℝ),(20536278385789045718423442304967/131166888930545703925781250:ℝ),(1957647093850727376234716314663/43722296310181901308593750:ℝ)],
![(1815096294069736180391767213813/13116688893054570392578125:ℝ),(23658071212239250822458104993251/65583444465272851962890625:ℝ),(20282460023091443684677913744057/65583444465272851962890625:ℝ),(44169937755072487372611829999/508398794304440712890625:ℝ)],
![(237294074403642026887546735487/3050392765826644277343750:ℝ),(5336414553088938453907610347487/26233377786109140785156250:ℝ),(11481426167412390100731850704436/65583444465272851962890625:ℝ),(1080380271143419984277878112063/21861148155090950654296875:ℝ)]]
theorem row132_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (44169937755072487372611829999/15163584686551416176640000000000:ℝ) row132_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row132_coefficients,Fin.sum_univ_succ]
 ring
theorem row132_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (33/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row132_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row132_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row132_pos
