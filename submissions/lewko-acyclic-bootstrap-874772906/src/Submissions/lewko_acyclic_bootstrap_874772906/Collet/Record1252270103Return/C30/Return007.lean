/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.C30.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Return.C30
noncomputable section
def row007_coefficients : Fin 3 → Fin 4 → ℝ := ![![(11044580322279381928129/93693975000000:ℝ), (4426924969790677215173941/12648686625000000:ℝ), (876185030903130326807353/2529737325000000:ℝ), (1445018528232690979160239/12648686625000000:ℝ)],
![(155402855705421083165023/702704812500000:ℝ), (4150044629411524286655061/6324343312500000:ℝ), (91207716383730691778869/140540962500000:ℝ), (1352928309205146591879251/6324343312500000:ℝ)],
![(145448601073012316231351/1405409625000000:ℝ), (3881619619509184260149893/12648686625000000:ℝ), (3836267065028035078866031/12648686625000000:ℝ), (46803142784294876474011/468469875000000:ℝ)]]
theorem row007_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (140409428352884629422033/670687597428736000000000:ℝ) row007_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row007_coefficients,Fin.sum_univ_succ]
 ring
theorem row007_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row007_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row007_coefficients]
#print axioms row007_identity
#print axioms row007_pos
end
end Record1252270103Return.C30
