/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace RH20261023Return.C30
noncomputable section
def row033_coefficients : Fin 3 → Fin 4 → ℝ := ![![(22568776866255478504840862453/2222073240797970703125:ℝ), (65496383871947224828236494641/2222073240797970703125:ℝ), (63319106788284860795161432448/2222073240797970703125:ℝ), (1359423614903412276485949184/148138216053198046875:ℝ)],
![(8411826238164426170897778812/444414648159594140625:ℝ), (121837290128693409264269374076/2222073240797970703125:ℝ), (117563362551544486055485475072/2222073240797970703125:ℝ), (37784898632823448870611245056/2222073240797970703125:ℝ)],
![(19543736642344738272030011732/2222073240797970703125:ℝ), (11300349108912683546348038772/444414648159594140625:ℝ), (18135251047297995228356766208/740691080265990234375:ℝ), (17447584487801623057453866496/2222073240797970703125:ℝ)]]
theorem row033_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (34077313452737545034089583/258890296726996992000000000:ℝ) row033_coefficients (63/128:ℝ) (33/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
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
end RH20261023Return.C30
