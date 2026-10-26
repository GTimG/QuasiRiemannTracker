/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row031_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3629540768895392910725518655415227818196/1617077351270005424145896484375:ℝ),(1540055384240705262546188658385812850124/231011050181429346306556640625:ℝ),(3557535435762875341071809636393152233698/539025783756668474715298828125:ℝ),(18633644611762119258805448228936479198/8555964821534420233576171875:ℝ)],
![(6993319545786386371108128387002600055032/1617077351270005424145896484375:ℝ),(20765731562507479076161041900373639496648/1617077351270005424145896484375:ℝ),(6850805261102673475064319498362843607248/539025783756668474715298828125:ℝ),(35873029787130796980856429995859742752/8555964821534420233576171875:ℝ)],
![(1122042511934537368505715772231047511172/539025783756668474715298828125:ℝ),(3330797511577861804364350639514360515244/539025783756668474715298828125:ℝ),(219708008248882611052327554897421862716/35935052250444564981019921875:ℝ),(5750608095231907896718306712582089612/2851988273844806744525390625:ℝ)]]
theorem row031_identity (δ p : ℝ) : rowMargin .oldSmall .P δ p =
 Record12518109.Bernstein.bsum 2 3 (1437652023807976974179576678145522403/10888174546434610797490470912000000000:ℝ) row031_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row031_coefficients,Fin.sum_univ_succ]
 ring
theorem row031_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .P δ p := by
 rw [row031_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row031_coefficients]
#print axioms row031_identity
#print axioms row031_pos
end
end LewkoStage2Finite
