/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row031_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2177731158108280671610040545535839482068/970248603849384323245376953125:ℝ),(6468252579424655912215435914729332748436/970248603849384323245376953125:ℝ),(6403583625500916207486660697405203062438/970248603849384323245376953125:ℝ),(140870791417262957425525647922447319738/64683240256625621549691796875:ℝ)],
![(220842349901706159278173917686192884264/51065715992072859118177734375:ℝ),(12459477451238669896392607606121398666184/970248603849384323245376953125:ℝ),(493259509436221622985147880782488069104/38809944153975372929815078125:ℝ),(1356004750235940496126123387326155954144/323416201283128107748458984375:ℝ)],
![(2019682749298314101324975882776509105548/970248603849384323245376953125:ℝ),(315550214777345521509571718977747155052/51065715992072859118177734375:ℝ),(5932134659350895816930506333587051324812/970248603849384323245376953125:ℝ),(652120992838574429703373206095454828124/323416201283128107748458984375:ℝ)]]
theorem row031_identity (δ p : ℝ) : rowMargin .oldSmall .P δ p =
 Record12518109.Bernstein.bsum 2 3 (163030248209643607425843301523863707031/1234721784451189741651551584256000000000:ℝ) row031_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row031_coefficients,Fin.sum_univ_succ]
 ring
theorem row031_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .P δ p := by
 rw [row031_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row031_coefficients]
#print axioms row031_identity
#print axioms row031_pos
end
end LewkoStage1Finite
