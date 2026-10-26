/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row033_coefficients : Fin 3 → Fin 4 → ℝ := ![![(112884814482197543631075208329779/11110188688287570035156250:ℝ),(109200364743699376177108405667897/3703396229429190011718750:ℝ),(52785187960675030324882923847328/1851698114714595005859375:ℝ),(50997060086792040812301603142528/5555094344143785017578125:ℝ)],
![(105187793717249713690479301766522/5555094344143785017578125:ℝ),(451421483139173127929806004462/8229769398731533359375:ℝ),(11760843844229540224984032248704/222203773765751400703125:ℝ),(31499542067786225045617570407424/1851698114714595005859375:ℝ)],
![(9775768255021143537643997966318/1111018868828757003515625:ℝ),(9420736618504521805959330634762/370339622942919001171875:ℝ),(136069272765947631238883391938176/5555094344143785017578125:ℝ),(43636665358363402262394765998336/5555094344143785017578125:ℝ)]]
theorem row033_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (170455724056107040087479554681/1294430801556647448576000000000:ℝ) row033_coefficients (63/128:ℝ) (33/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row033_coefficients,Fin.sum_univ_succ]
 ring
theorem row033_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row033_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row033_coefficients]
#print axioms row033_identity
#print axioms row033_pos
end
end LewkoStage2Finite
