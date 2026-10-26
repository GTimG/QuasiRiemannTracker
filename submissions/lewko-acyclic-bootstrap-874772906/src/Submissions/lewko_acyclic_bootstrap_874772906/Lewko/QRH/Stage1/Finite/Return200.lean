/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row200_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5629205344736091698803022850397312906/12934813280758459682407787109375:ℝ),(13412672035169973831641319858178874242/12934813280758459682407787109375:ℝ),(10058403603954023294614930752212568881/12934813280758459682407787109375:ℝ),(454861466659796309419203726025264009/2586962656151691936481557421875:ℝ)],
![(11340193310947638510805836255297151196/12934813280758459682407787109375:ℝ),(26656026135014349932010773576347297652/12934813280758459682407787109375:ℝ),(19544160258789259757525555240864625916/12934813280758459682407787109375:ℝ),(845400400535600355819654062150395892/2586962656151691936481557421875:ℝ)],
![(1288651861532741336533926070313419718/2586962656151691936481557421875:ℝ),(162289531008075602977562132735262566/136155929271141680867450390625:ℝ),(2327501542783651879032359879938588354/2586962656151691936481557421875:ℝ),(532512796000372910863937258907019318/2586962656151691936481557421875:ℝ)]]
theorem row200_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (211350100133900088954913515537598973/617273333563600560125288801894400000000:ℝ) row200_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row200_coefficients,Fin.sum_univ_succ]
 ring
theorem row200_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row200_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row200_coefficients]
#print axioms row200_identity
#print axioms row200_pos
end
end LewkoStage1Finite
