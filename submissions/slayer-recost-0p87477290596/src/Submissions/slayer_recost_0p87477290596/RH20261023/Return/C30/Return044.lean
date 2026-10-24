/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace RH20261023Return.C30
noncomputable section
def row044_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2200249907560625940026884162987102076/1896615074543947971626953125:ℝ), (1307932919963555040570269222167438156/379323014908789594325390625:ℝ), (2159607604583963680729094007737834294/632205024847982657208984375:ℝ), (79237323895067333311471229643089414/70245002760886961912109375:ℝ)],
![(473699134855957309169221274106893288/210735008282660885736328125:ℝ), (4222857426788814573050406441147833032/632205024847982657208984375:ℝ), (4182586833283190283772428786173654272/632205024847982657208984375:ℝ), (153425172599586867434494296371833456/70245002760886961912109375:ℝ)],
![(2064532573462130366544521724348806116/1896615074543947971626953125:ℝ), (6133370376461472161029004786918010316/1896615074543947971626953125:ℝ), (2024464085952233299147725446165470028/632205024847982657208984375:ℝ), (74242742885647845269544658367674292/70245002760886961912109375:ℝ)]]
theorem row044_identity (δ p : ℝ) : rowMargin .oldPeak .weakC8 δ p =
 Record12518109.Bernstein.bsum 2 3 (18560685721411961317386164591918573/268177768502612630546939904000000000:ℝ) row044_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row044_coefficients,Fin.sum_univ_succ]
 ring
theorem row044_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldPeak .weakC8 δ p := by
 rw [row044_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row044_coefficients]
#print axioms row044_identity
#print axioms row044_pos
end
end RH20261023Return.C30
