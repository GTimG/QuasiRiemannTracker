/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace RH20261023Return.C30
noncomputable section
def row068_coefficients : Fin 3 → Fin 4 → ℝ := ![![(30927359196907275163058866567/6666219722393912109375:ℝ), (29918376910301219198108691233/2222073240797970703125:ℝ), (28926433043447249913797046424/2222073240797970703125:ℝ), (5590244905458121322026348928/1333243944478782421875:ℝ)],
![(11634128575264788571637910868/1333243944478782421875:ℝ), (56172481494269362523851161788/2222073240797970703125:ℝ), (162627585111436253947288535008/6666219722393912109375:ℝ), (17426716167707695604964451328/2222073240797970703125:ℝ)],
![(27332553615655718566089141148/6666219722393912109375:ℝ), (1756198217688306285615727292/148138216053198046875:ℝ), (76113686365102476557477871136/6666219722393912109375:ℝ), (24416987564778733860890534144/6666219722393912109375:ℝ)]]
theorem row068_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (95378857674916929144103649/1553341780361981952000000000:ℝ) row068_coefficients (63/128:ℝ) (33/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row068_coefficients,Fin.sum_univ_succ]
 ring
theorem row068_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row068_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row068_coefficients]
#print axioms row068_identity
#print axioms row068_pos
end
end RH20261023Return.C30
