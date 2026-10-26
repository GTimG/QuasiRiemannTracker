/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.arvi_repeated_marks_on_sil_face_20261025.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def row005_coefficients : Fin 3 → Fin 4 → ℝ := ![![(34520250150928488807349/6840239207985070312500:ℝ), (45442053230859227316541/3420119603992535156250:ℝ), (78207462470651442844117/6840239207985070312500:ℝ), (1820300513321789751532/570019933998755859375:ℝ)],
![(43705545013274365209259/13680478415970140625000:ℝ), (205673302910615357148697/27360956831940281250000:ℝ), (7886023665300096930217/1368047841597014062500:ℝ), (13152753473978437291387/9120318943980093750000:ℝ)],
![(29386958375297950094561/13680478415970140625000:ℝ), (86284889963854498582619/27360956831940281250000:ℝ), (31182707949838223393497/27360956831940281250000:ℝ), (0:ℝ)]]
theorem row005_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (5726892183190977926441/389133608276484000000000:ℝ) row005_coefficients (0:ℝ) (3/8:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row005_coefficients,Fin.sum_univ_succ] <;> ring
theorem row005_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row005_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row005_coefficients]
def row006_coefficients : Fin 3 → Fin 4 → ℝ := ![![(31401218784625422450481/10944382732776112500000:ℝ), (290944561193514932787721/54721913663880562500000:ℝ), (180740197165482382409477/54721913663880562500000:ℝ), (13152753473978437291387/18240637887960187500000:ℝ)],
![(187142837397770182212131/27360956831940281250000:ℝ), (128920519105304286402131/13680478415970140625000:ℝ), (85385139759156890592131/27360956831940281250000:ℝ), (0:ℝ)],
![(436167235527935502171857/54721913663880562500000:ℝ), (713033541027928132753303/54721913663880562500000:ℝ), (72522850281143102221207/10944382732776112500000:ℝ), (18791356004361960174863/18240637887960187500000:ℝ)]]
theorem row006_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (6356877043592511537367/3113068866211872000000000:ℝ) row006_coefficients (3/8:ℝ) (3/4:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row006_coefficients,Fin.sum_univ_succ] <;> ring
theorem row006_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row006_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row006_coefficients]
end
end QRH.RepeatedMarks.Return
