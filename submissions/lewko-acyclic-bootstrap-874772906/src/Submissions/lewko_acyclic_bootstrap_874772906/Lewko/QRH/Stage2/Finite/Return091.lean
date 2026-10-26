/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row091_coefficients : Fin 3 → Fin 4 → ℝ := ![![(832707062064333029308207054202359772264/5400727842363000016521919921875:ℝ),(19177190425168501301406774068648127112/43205822738904000132175359375:ℝ),(2297872338293373270093088526193059547136/5400727842363000016521919921875:ℝ),(29336970349233620439094718372576137216/216029113694520000660876796875:ℝ)],
![(126141724337354285594530834409287112392/415440603258692308963224609375:ℝ),(4715451426607609432784270446042595825704/5400727842363000016521919921875:ℝ),(4514807736771576363863817581841164761088/5400727842363000016521919921875:ℝ),(287837177412563518843236324123860279296/1080145568472600003304383984375:ℝ)],
![(809292470414946672930171359770733235578/5400727842363000016521919921875:ℝ),(464947488477338324951031923771252743858/1080145568472600003304383984375:ℝ),(2223333925916492997178278054300054926848/5400727842363000016521919921875:ℝ),(707882451896968244598231829589524443136/5400727842363000016521919921875:ℝ)]]
theorem row091_identity (δ p : ℝ) : rowMargin .oldSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (172822864232658262841365192770879991/80541491172033779275726061568000000000:ℝ) row091_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row091_coefficients,Fin.sum_univ_succ]
 ring
theorem row091_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .C δ p := by
 rw [row091_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row091_coefficients]
#print axioms row091_identity
#print axioms row091_pos
end
end LewkoStage2Finite
