/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def row077_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5803638511184604214811217509/2592534012574218750000:ℝ), (16575521836716080326754001103/2592534012574218750000:ℝ), (15761745043976564493543369479/2592534012574218750000:ℝ), (332657447896339225440039059/172835600838281250000:ℝ)],
![(5415164638925126606163281173/1296267006287109375000:ℝ), (5121302802171157441475279717/432089002095703125000:ℝ), (14504842881407021134095587683/1296267006287109375000:ℝ), (911219822763735083166605941/259253401257421875000:ℝ)],
![(1737201247521446075562181279/864178004191406250000:ℝ), (14702879420930204144015255999/2592534012574218750000:ℝ), (1532711589319997081564861493/288059334730468750000:ℝ), (172125145020564312670201651/103701360502968750000:ℝ)]]
theorem row077_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (172125145020564312670201651/49488216878995210240000000000:ℝ) row077_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row077_coefficients,Fin.sum_univ_succ]
 ring
theorem row077_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
 rw [row077_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row077_coefficients]
#print axioms row077_identity
#print axioms row077_pos
end
end Record1252270103Finite
