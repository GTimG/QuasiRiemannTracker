/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace RH20261023Return.C30
noncomputable section
def row069_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2101573818903121759550116303/13332439444787824218750:ℝ), (5920127187802547631634646171/13332439444787824218750:ℝ), (2774579644465252714838982754/6666219722393912109375:ℝ), (173043961002824035260906064/1333243944478782421875:ℝ)],
![(1879066507305937952356906316/6666219722393912109375:ℝ), (5259121552851688793224783516/6666219722393912109375:ℝ), (4895290248820146405594919984/6666219722393912109375:ℝ), (1515053774180389159289542784/6666219722393912109375:ℝ)],
![(279862886480820962226382184/2222073240797970703125:ℝ), (86395727216146309644656584/246897026755330078125:ℝ), (143602456966802777173513952/444414648159594140625:ℝ), (73426879753838965555680896/740691080265990234375:ℝ)]]
theorem row069_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (573647498076866918403757/10787095696958208000000000:ℝ) row069_coefficients (33/64:ℝ) (9/16:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row069_coefficients,Fin.sum_univ_succ]
 ring
theorem row069_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row069_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row069_coefficients]
#print axioms row069_identity
#print axioms row069_pos
end
end RH20261023Return.C30
