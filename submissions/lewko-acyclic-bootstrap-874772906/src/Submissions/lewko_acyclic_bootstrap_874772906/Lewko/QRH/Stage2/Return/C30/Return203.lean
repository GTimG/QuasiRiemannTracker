/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Return.C30
noncomputable section
def row203_coefficients : Fin 3 → Fin 4 → ℝ := ![![(91387178180333202768970819375213/41401849215178388359223437500:ℝ), (204051934983158175885210760573039/41401849215178388359223437500:ℝ), (141193341661200051412643354564189/41401849215178388359223437500:ℝ), (28389028345425725746919194616363/41401849215178388359223437500:ℝ)],
![(601001180580378749638001189522489/103504623037945970898058593750:ℝ), (1376494122731363391654624148771259/103504623037945970898058593750:ℝ), (992797382663625514130231186543551/103504623037945970898058593750:ℝ), (216467101434944756816702914794781/103504623037945970898058593750:ℝ)],
![(965000372425144276484883477480713/207009246075891941796117187500:ℝ), (2366568725452658250878629171284923/207009246075891941796117187500:ℝ), (1888679518192407806432808509177107/207009246075891941796117187500:ℝ), (486106358271658493682776440372897/207009246075891941796117187500:ℝ)]]
theorem row203_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (28389028345425725746919194616363/19294660196735508334293811200000000:ℝ) row203_coefficients (15/32:ℝ) (9/16:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row203_coefficients,Fin.sum_univ_succ]
 ring
theorem row203_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row203_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row203_coefficients]
#print axioms row203_identity
#print axioms row203_pos
end
end LewkoStage2Return.C30
