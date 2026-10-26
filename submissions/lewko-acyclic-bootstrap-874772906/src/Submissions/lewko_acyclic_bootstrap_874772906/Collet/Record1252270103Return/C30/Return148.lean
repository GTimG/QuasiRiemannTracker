/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.C30.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Return.C30
noncomputable section
def row148_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4836691416784839193822535432685967/3510782468510273437500000000:ℝ), (54589754324354684022045738173538443/17553912342551367187500000000:ℝ), (1162867828888578365986478524048841/548559760704730224609375000:ℝ), (212671040125125614332320367482947/548559760704730224609375000:ℝ)],
![(29369607893961818485516561408005541/11702608228367578125000000000:ℝ), (189994802730773158594069983011834863/35107824685102734375000000000:ℝ), (61480512246918818849270371047983/18285325356824340820312500:ℝ), (25244694476869420395435646287983/54855976070473022460937500:ℝ)],
![(336863654769713801963097307821931171/280862597480821875000000000000:ℝ), (46856303738557017322098232114852909/18724173165388125000000000000:ℝ), (790654859266638550336852180750183/548559760704730224609375000:ℝ), (25282803799399400979226655366687/182853253568243408203125000:ℝ)]]
theorem row148_identity (δ p : ℝ) : rowMargin .newTop .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (25282803799399400979226655366687/349043886241244774400000000000000000:ℝ) row148_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newTop,edgeC_newTop,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row148_coefficients,Fin.sum_univ_succ]
 ring
theorem row148_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .capC δ p := by
 rw [row148_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row148_coefficients]
#print axioms row148_identity
#print axioms row148_pos
end
end Record1252270103Return.C30
