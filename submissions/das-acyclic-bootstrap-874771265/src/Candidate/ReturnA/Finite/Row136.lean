/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row136_coefficients : Fin 3 → Fin 4 → ℝ := ![![(191419717390508955679093447348667507/4778429025739399645517578125:ℝ),(109771948386247389195813791636813249/955685805147879929103515625:ℝ),(523875577229585993601837227276871494/4778429025739399645517578125:ℝ),(55478021334096765497087117720074252/1592809675246466548505859375:ℝ)],
![(380364725213905361178295494983178574/4778429025739399645517578125:ℝ),(1089166471601919017817166896037983194/4778429025739399645517578125:ℝ),(1038087982681815989621041078037850766/4778429025739399645517578125:ℝ),(2552582839548914403512672762465474/37042085470848059267578125:ℝ)],
![(190914955652022108670957348517795567/4778429025739399645517578125:ℝ),(546183934465175169838779326060042749/4778429025739399645517578125:ℝ),(520057181216374431189336437439572897/4778429025739399645517578125:ℝ),(10985776014146725686784325451488381/318561935049293309701171875:ℝ)]]
theorem row136_identity (δ p : ℝ) : rowMargin .newSwitch .P δ p =
 Record12518109.Bernstein.bsum 2 3 (1276291419774457201756336381232737/565669495725970403339796480000000000:ℝ) row136_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row136_coefficients,Fin.sum_univ_succ]
 ring
theorem row136_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .P δ p := by
 rw [row136_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row136_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row136_pos
