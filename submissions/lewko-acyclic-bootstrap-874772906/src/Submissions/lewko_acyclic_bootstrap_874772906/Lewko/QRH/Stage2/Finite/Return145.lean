/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row145_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7960020624779538459363470975897/1408920573243234375000000000:ℝ),(1407245209243030091241344281803877/105669042993242578125000000000:ℝ),(1069404985251552564580434277117403/105669042993242578125000000000:ℝ),(259161322866987857791350318505801/105669042993242578125000000000:ℝ)],
![(633888986516213167223743932970793/70446028662161718750000000000:ℝ),(3953554811120354146631180661510211/211338085986485156250000000000:ℝ),(600699596958574504075219017874187/52834521496621289062500000000:ℝ),(87727634065645842835231802224729/52834521496621289062500000000:ℝ)],
![(5048963059037781989673551538785251/1127136458594587500000000000000:ℝ),(5866462913575989917185983473157397/676281875156752500000000000000:ℝ),(468020228232031990119666338479589/105669042993242578125000000000:ℝ),(24725684770575627091251877559863/105669042993242578125000000000:ℝ)]]
theorem row145_identity (δ p : ℝ) : rowMargin .newTop .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (24725684770575627091251877559863/196981373201213030400000000000000000:ℝ) row145_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newTop,edgeC_newTop,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row145_coefficients,Fin.sum_univ_succ]
 ring
theorem row145_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .capC δ p := by
 rw [row145_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row145_coefficients]
#print axioms row145_identity
#print axioms row145_pos
end
end LewkoStage2Finite
