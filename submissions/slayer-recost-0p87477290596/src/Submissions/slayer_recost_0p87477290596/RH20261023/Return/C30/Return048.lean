/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace RH20261023Return.C30
noncomputable section
def row048_coefficients : Fin 3 → Fin 4 → ℝ := ![![(65688919795636656716442755077043473282/1896615074543947971626953125:ℝ), (65370360766690311935191118753231246978/632205024847982657208984375:ℝ), (195157388424349144989123093989911524422/1896615074543947971626953125:ℝ), (1438560540714120017272634284605805706/42147001656532177147265625:ℝ)],
![(25848772199542048923165865390225096372/379323014908789594325390625:ℝ), (128609039873178311029370686652762010628/632205024847982657208984375:ℝ), (42658516211243472600675737324230963532/210735008282660885736328125:ℝ), (127343384062023964553542477910918121764/1896615074543947971626953125:ℝ)],
![(63566794879814672157215109668090942578/1896615074543947971626953125:ℝ), (2530020877059873269726925252785022578/25288200993919306288359375:ℝ), (188804753326015726700557689748083454066/1896615074543947971626953125:ℝ), (62619980796501875804044558582297703294/1896615074543947971626953125:ℝ)]]
theorem row048_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (31309990398250937902022279291148851647/463411183972514625585112154112000000000:ℝ) row048_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row048_coefficients,Fin.sum_univ_succ]
 ring
theorem row048_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row048_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row048_coefficients]
#print axioms row048_identity
#print axioms row048_pos
end
end RH20261023Return.C30
