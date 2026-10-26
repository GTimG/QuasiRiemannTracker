/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row010_coefficients : Fin 3 → Fin 4 → ℝ := ![![(247728649196770640621377941554245556446/98232407669574213883576171875:ℝ),(13985225830359080630285991851406526787194/1866415745721910063787947265625:ℝ),(13850428497899616975596408818988948128256/1866415745721910063787947265625:ℝ),(4572046460012501833086516888363086913536/1866415745721910063787947265625:ℝ)],
![(9091864018102350127694992283109544460504/1866415745721910063787947265625:ℝ),(1421454135714420697119570772879722536648/98232407669574213883576171875:ℝ),(26740691717891871698844365803797875218432/1866415745721910063787947265625:ℝ),(8824926043575162960016536277192691482624/1866415745721910063787947265625:ℝ)],
![(46186384216985492346192007326539506328/19646481533914842776715234375:ℝ),(685813931391428004539687226852516230392/98232407669574213883576171875:ℝ),(678859288401388586814816324341068519424/98232407669574213883576171875:ℝ),(223977247990967351539846509121249820672/98232407669574213883576171875:ℝ)]]
theorem row010_identity (δ p : ℝ) : rowMargin .oldSmall .weakC7 δ p =
 Record12518109.Bernstein.bsum 2 3 (13670486327573690889883209785232533/91559240092916845241942016000000000:ℝ) row010_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row010_coefficients,Fin.sum_univ_succ]
 ring
theorem row010_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .weakC7 δ p := by
 rw [row010_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row010_coefficients]
#print axioms row010_identity
#print axioms row010_pos
end
end LewkoStage1Finite
