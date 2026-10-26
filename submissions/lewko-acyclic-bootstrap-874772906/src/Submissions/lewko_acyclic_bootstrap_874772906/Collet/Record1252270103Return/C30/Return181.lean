/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.C30.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Return.C30
noncomputable section
def row181_coefficients : Fin 3 → Fin 4 → ℝ := ![![(852000387128402794706697155503/414018492151783883592234375:ℝ), (263353468438023098521877050057529/51752311518972985449029296875:ℝ), (213284940080907742571977816714033/51752311518972985449029296875:ℝ), (56319874823575511348850536094379/51752311518972985449029296875:ℝ)],
![(175065790538430671046380237543062/51752311518972985449029296875:ℝ), (77580816666194255932064386952858/10350462303794597089805859375:ℝ), (265459486755049596059681385833894/51752311518972985449029296875:ℝ), (52342080936610282346771251112666/51752311518972985449029296875:ℝ)],
![(123549217688893519471476891933137/51752311518972985449029296875:ℝ), (283010653619378767887303553858661/51752311518972985449029296875:ℝ), (408874823933862224593188592695197/103504623037945970898058593750:ℝ), (89603060790518346387824721969149/103504623037945970898058593750:ℝ)]]
theorem row181_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (26171040468305141173385625556333/24118325245919385417867264000000000:ℝ) row181_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row181_coefficients,Fin.sum_univ_succ]
 ring
theorem row181_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row181_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row181_coefficients]
#print axioms row181_identity
#print axioms row181_pos
end
end Record1252270103Return.C30
