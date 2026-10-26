/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace RH20261023Return.C30
noncomputable section
def row175_coefficients : Fin 3 → Fin 4 → ℝ := ![![(633648151099377139364153215997323409/7894539956040956320710937500000:ℝ), (247449943204584909601067445633620041/1578907991208191264142187500000:ℝ), (38601341098815654825863870661825613/493408747252559770044433593750:ℝ), (423432907553424092847106702285016/246704373626279885022216796875:ℝ)],
![(376358093614578364984758354963884671/1973634989010239080177734375000:ℝ), (777898165740063897683779836932148259/1973634989010239080177734375000:ℝ), (11242522734081410462550618183273022/49340874725255977004443359375:ℝ), (5989328251306310287179956007246224/246704373626279885022216796875:ℝ)],
![(9275943758057860433344789774890329/78945399560409563207109375000:ℝ), (509578466007242253558200051958962189/1973634989010239080177734375000:ℝ), (4658936634341197494573034672247074/27411597069586653891357421875:ℝ), (2401441576292967412732226973740536/82234791208759961674072265625:ℝ)]]
theorem row175_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (52929113444178011605888337785627/1839561139765689292210176000000000000:ℝ) row175_coefficients (63/128:ℝ) (33/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newTop,edgeC_newTop,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row175_coefficients,Fin.sum_univ_succ]
 ring
theorem row175_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row175_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row175_coefficients]
#print axioms row175_identity
#print axioms row175_pos
end
end RH20261023Return.C30
