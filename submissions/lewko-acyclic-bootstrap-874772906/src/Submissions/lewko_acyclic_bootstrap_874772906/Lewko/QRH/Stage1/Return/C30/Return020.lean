/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Return.C30
noncomputable section
def row020_coefficients : Fin 3 → Fin 4 → ℝ := ![![(60602433353862727715005347846695408/25288200993919306288359375:ℝ), (4500943435047767079147542378245500256/632205024847982657208984375:ℝ), (4456880175642818103633157154433404012/632205024847982657208984375:ℝ), (163444152625505911929120316372809884/70245002760886961912109375:ℝ)],
![(194888273792987377093633829893763584/42147001656532177147265625:ℝ), (8682380352857070247356701016100500736/632205024847982657208984375:ℝ), (8595142125165470648483698418846416192/632205024847982657208984375:ℝ), (315120607475669374483861650128041024/70245002760886961912109375:ℝ)],
![(281835286267810808925780925008797312/126441004969596531441796875:ℝ), (10331301604304025786095972058486656/1561000061353043598046875:ℝ), (828200575488639904878317735055646336/126441004969596531441796875:ℝ), (30355598839932802368591658147447168/14049000552177392382421875:ℝ)]]
theorem row020_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (237153115936975018504622329276931/1676111053141328940918374400000000:ℝ) row020_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row020_coefficients,Fin.sum_univ_succ]
 ring
theorem row020_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row020_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row020_coefficients]
#print axioms row020_identity
#print axioms row020_pos
end
end LewkoStage1Return.C30
