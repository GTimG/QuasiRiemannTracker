/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row223_coefficients : Fin 3 → Fin 4 → ℝ := ![![(116573899196188324424402592597662209/17246417707677946243210382812500:ℝ),(701588568042221436919529203419983923/51739253123033838729631148437500:ℝ),(19727002111505871943621239727797664/2586962656151691936481557421875:ℝ),(10457270210707173511915236052551496/12934813280758459682407787109375:ℝ)],
![(2917827237809209274797634467663466/172464177076779462432103828125:ℝ),(463872639929225431961479397885496494/12934813280758459682407787109375:ℝ),(293169594401893737618207206717087728/12934813280758459682407787109375:ℝ),(47673584071832302441945434968851184/12934813280758459682407787109375:ℝ)],
![(47857728107700472802890211099274124/4311604426919486560802595703125:ℝ),(17025888014715769123661313014032348/680779646355708404337251953125:ℝ),(228135848795338552750431250632087848/12934813280758459682407787109375:ℝ),(47966026346189431177934231788295608/12934813280758459682407787109375:ℝ)]]
theorem row223_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1307158776338396688989404506568937/3014029949041018359986761728000000000:ℝ) row223_coefficients (33/64:ℝ) (9/16:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row223_coefficients,Fin.sum_univ_succ]
 ring
theorem row223_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row223_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row223_coefficients]
#print axioms row223_identity
#print axioms row223_pos
end
end LewkoStage1Finite
