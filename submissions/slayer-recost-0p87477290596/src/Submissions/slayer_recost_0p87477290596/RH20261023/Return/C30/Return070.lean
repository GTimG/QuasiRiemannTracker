/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace RH20261023Return.C30
noncomputable section
def row070_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6898761727964689039465513/26664878889575648437500:ℝ), (11366745558171980003630273/17776585926383765625000:ℝ), (1856561991029258399863349/3555317185276753125000:ℝ), (3748117992425283564245221/26664878889575648437500:ℝ)],
![(582843701381099829613517/1481382160531980468750:ℝ), (242904254589555489167978/266648788895756484375:ℝ), (9170021872073638405440541/13332439444787824218750:ℝ), (13811205845830850546687/82299008918443359375:ℝ)],
![(1089198282591190025877842/6666219722393912109375:ℝ), (2363380269965348057289182/6666219722393912109375:ℝ), (1638855062607842581758488/6666219722393912109375:ℝ), (353677372566629675347148/6666219722393912109375:ℝ)]]
theorem row070_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (88419343141657418836787/3033870664769496000000000:ℝ) row070_coefficients (9/16:ℝ) (3/4:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row070_coefficients,Fin.sum_univ_succ]
 ring
theorem row070_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/16:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row070_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row070_coefficients]
#print axioms row070_identity
#print axioms row070_pos
end
end RH20261023Return.C30
