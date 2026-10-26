/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row035_coefficients : Fin 3 → Fin 4 → ℝ := ![![(50170166823840183119125769623/88881509506300560281250000:ℝ),(14030971486322125595111052743/9875723278477840031250000:ℝ),(324332860016284436380903663/274325646624384445312500:ℝ),(7214109704053672968478520437/22220377376575140070312500:ℝ)],
![(944704365200840884520308253/1234465409809730003906250:ℝ),(10079873463210826250608632449/5555094344143785017578125:ℝ),(15647017163804274574192431199/11110188688287570035156250:ℝ),(658333183142669545797156763/1851698114714595005859375:ℝ)],
![(1344883541041263724826255963/5555094344143785017578125:ℝ),(583875307108484346629022649/1111018868828757003515625:ℝ),(2023034299661451701816591834/5555094344143785017578125:ℝ),(435337830048902773872734552/5555094344143785017578125:ℝ)]]
theorem row035_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (54417228756112846734091819/1264092579645163524000000000:ℝ) row035_coefficients (9/16:ℝ) (3/4:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row035_coefficients,Fin.sum_univ_succ]
 ring
theorem row035_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/16:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row035_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row035_coefficients]
#print axioms row035_identity
#print axioms row035_pos
end
end LewkoStage2Finite
