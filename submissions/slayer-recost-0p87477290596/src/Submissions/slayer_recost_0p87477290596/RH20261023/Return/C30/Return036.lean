/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace RH20261023Return.C30
noncomputable section
def row036_coefficients : Fin 3 → Fin 4 → ℝ := ![![(12684231195693187383398017/426638062233210375000000:ℝ), (11119970742430706066188337/142212687411070125000000:ℝ), (1061745587685358305442073/15801409712341125000000:ℝ), (7991449835905743431768977/426638062233210375000000:ℝ)],
![(8520994453245469326645949/213319031116605187500000:ℝ), (7049837591615211742930091/71106343705535062500000:ℝ), (17045275146177403492709699/213319031116605187500000:ℝ), (11778018198872633574841/568850749644280500000:ℝ)],
![(6064309959730592769893881/426638062233210375000000:ℝ), (910404947169136454097979/28442537482214025000000:ℝ), (9853804449008618667952027/426638062233210375000000:ℝ), (2218057390533945126376223/426638062233210375000000:ℝ)]]
theorem row036_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2218057390533945126376223/24270965318155968000000000:ℝ) row036_coefficients (0:ℝ) (3/8:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row036_coefficients,Fin.sum_univ_succ]
 ring
theorem row036_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row036_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row036_coefficients]
#print axioms row036_identity
#print axioms row036_pos
end
end RH20261023Return.C30
