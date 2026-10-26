/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row192_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2113473192340000854226862390609233/16168512335757285362588578125000:ℝ),(4756507276393422804291200867343011/16168512335757285362588578125000:ℝ),(687144994711838570602355181135251/3233702467151457072517715625000:ℝ),(261323647766862089543747726314159/5389504111919095120862859375000:ℝ)],
![(2366222958093158904861233519876713/8084256167878642681294289062500:ℝ),(960164924052020914959788975593807/1616851233575728536258857812500:ℝ),(2884336487473914829692714151428289/8084256167878642681294289062500:ℝ),(145551635333064069426903806111989/2694752055959547560431429687500:ℝ)],
![(5318588498600820631948854181103053/16168512335757285362588578125000:ℝ),(2467566958196258318476013010729391/3233702467151457072517715625000:ℝ),(4635964977413440703475864704002739/8084256167878642681294289062500:ℝ),(93044324311864375804545061373399/673688013989886890107857421875:ℝ)]]
theorem row192_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (145551635333064069426903806111989/78490342550828848409081856000000000:ℝ) row192_coefficients (3/8:ℝ) (9/16:ℝ) (1/4:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row192_coefficients,Fin.sum_univ_succ]
 ring
theorem row192_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (3/8:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row192_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row192_coefficients]
#print axioms row192_identity
#print axioms row192_pos
end
end LewkoStage2Finite
