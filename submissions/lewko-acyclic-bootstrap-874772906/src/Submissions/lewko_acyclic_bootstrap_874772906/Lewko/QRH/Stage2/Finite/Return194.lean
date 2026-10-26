/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row194_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7589962383245268985621192/1198393308239642578125:ℝ),(55056931198861727230312424/3595179924718927734375:ℝ),(43365106791204671747351512/3595179924718927734375:ℝ),(11078062742078751473902664/3595179924718927734375:ℝ)],
![(12269429837806208831337092/1198393308239642578125:ℝ),(80247114062046424192511692/3595179924718927734375:ℝ),(53480317564335267264943568/3595179924718927734375:ℝ),(10041493015707469566443152/3595179924718927734375:ℝ)],
![(24149289673697040583260799/4793573232958570312500:ℝ),(148092989539003100567190173/14380719698875710937500:ℝ),(21572399274590986960601728/3595179924718927734375:ℝ),(2661119145112992256249784/3595179924718927734375:ℝ)]]
theorem row194_identity (δ p : ℝ) : rowMargin .newKink .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (332639893139124032031223/837737641053794304000000000:ℝ) row194_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row194_coefficients,Fin.sum_univ_succ]
 ring
theorem row194_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .capC δ p := by
 rw [row194_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row194_coefficients]
#print axioms row194_identity
#print axioms row194_pos
end
end LewkoStage2Finite
