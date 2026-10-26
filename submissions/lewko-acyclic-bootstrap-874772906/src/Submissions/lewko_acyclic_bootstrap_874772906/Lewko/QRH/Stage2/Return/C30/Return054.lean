/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Return.C30
noncomputable section
def row054_coefficients : Fin 3 → Fin 4 → ℝ := ![![(252339999933398412650448592594431139388/1896615074543947971626953125:ℝ), (753254467089019480934574792760425485884/1896615074543947971626953125:ℝ), (749496986468631635432047150760988911104/1896615074543947971626953125:ℝ), (248582512708716652748086653719994564608/1896615074543947971626953125:ℝ)],
![(500496797061983023465531710653498525024/1896615074543947971626953125:ℝ), (1493973004149128514299690955512659363168/1896615074543947971626953125:ℝ), (1486471767278332213246460312353079947264/1896615074543947971626953125:ℝ), (98599109379476439588591438498783821824/379323014908789594325390625:ℝ)],
![(82722872731732640947617913845902741312/632205024847982657208984375:ℝ), (82305996401179476360904528422684733376/210735008282660885736328125:ℝ), (49134011911492823130682982821093351424/126441004969596531441796875:ℝ), (9052771206192202959954510298146144256/70245002760886961912109375:ℝ)]]
theorem row054_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (8633395391647532424883375452181/130946176026666323509248000000000:ℝ) row054_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row054_coefficients,Fin.sum_univ_succ]
 ring
theorem row054_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row054_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row054_coefficients]
#print axioms row054_identity
#print axioms row054_pos
end
end LewkoStage2Return.C30
