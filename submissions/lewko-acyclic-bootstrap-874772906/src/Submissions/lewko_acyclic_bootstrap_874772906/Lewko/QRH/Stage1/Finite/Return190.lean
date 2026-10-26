/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row190_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2892144433261946640532611600893641/827828049968541419674098375000000:ℝ),(7754187030667892907863353901854603/827828049968541419674098375000000:ℝ),(6831940761549945894128873001028283/827828049968541419674098375000000:ℝ),(1969898164143999626798130700067321/827828049968541419674098375000000:ℝ)],
![(456189054619185742077232995521797/413914024984270709837049187500000:ℝ),(1158355381596637013977182429720949/413914024984270709837049187500000:ℝ),(1033512686269914226543597631765207/413914024984270709837049187500000:ℝ),(66269271858492590928729639513211/82782804996854141967409837500000:ℝ)],
![(1331545875850590522318247890149953/827828049968541419674098375000000:ℝ),(360355243875962392889404222717391/165565609993708283934819675000000:ℝ),(618354288670264008540478527501281/827828049968541419674098375000000:ℝ),(36508615073964063477169804064279/827828049968541419674098375000000:ℝ)]]
theorem row190_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (36508615073964063477169804064279/47094217953765911874793152000000000:ℝ) row190_coefficients (0:ℝ) (3/8:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row190_coefficients,Fin.sum_univ_succ]
 ring
theorem row190_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row190_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row190_coefficients]
#print axioms row190_identity
#print axioms row190_pos
end
end LewkoStage1Finite
