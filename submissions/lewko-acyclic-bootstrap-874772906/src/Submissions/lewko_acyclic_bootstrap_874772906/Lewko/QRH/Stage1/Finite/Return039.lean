/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row039_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1727220703702733621151489464441/26664453421076522109375000:ℝ),(4957144878948512331745834266091/26664453421076522109375000:ℝ),(4737710598630202538671253824459/26664453421076522109375000:ℝ),(1507742450763281793881909022809/26664453421076522109375000:ℝ)],
![(1429400457030806206503415773593/13332226710538261054687500:ℝ),(4070716578866782046136847648363/13332226710538261054687500:ℝ),(3858967553018846677169486316947/13332226710538261054687500:ℝ),(405865488468814431597434814059/4444075570179420351562500:ℝ)],
![(235599863913226122362226069949/5332890684215304421875000:ℝ),(664466386581261670288291542047/5332890684215304421875000:ℝ),(207804214053754906623260755999/1777630228071768140625000:ℝ),(194532378049122286257779295899/5332890684215304421875000:ℝ)]]
theorem row039_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (194532378049122286257779295899/2485307192040776466432000000000:ℝ) row039_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row039_coefficients,Fin.sum_univ_succ]
 ring
theorem row039_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row039_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row039_coefficients]
#print axioms row039_identity
#print axioms row039_pos
end
end LewkoStage1Finite
