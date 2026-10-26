/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.C30.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Return.C30
noncomputable section
def row061_coefficients : Fin 3 → Fin 4 → ℝ := ![![(116717129273356841348428961/2222073240797970703125:ℝ), (332509216243932106219729883/2222073240797970703125:ℝ), (1892401839298223337075459173/13332439444787824218750:ℝ), (597614955903937201363278641/13332439444787824218750:ℝ)],
![(191499445376043620417142094/2222073240797970703125:ℝ), (180062210229443528324004286/740691080265990234375:ℝ), (1521155028339121833115237552/6666219722393912109375:ℝ), (95010447703451896733875052/1333243944478782421875:ℝ)],
![(78652429715539848222961883/2222073240797970703125:ℝ), (8767473719936421870375097/88882929631918828125:ℝ), (22562288975295913561593739/246897026755330078125:ℝ), (62517940717792232361678109/2222073240797970703125:ℝ)]]
theorem row061_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (62517940717792232361678109/1035561186907987968000000000:ℝ) row061_coefficients (15/32:ℝ) (9/16:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row061_coefficients,Fin.sum_univ_succ]
 ring
theorem row061_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row061_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row061_coefficients]
#print axioms row061_identity
#print axioms row061_pos
end
end Record1252270103Return.C30
