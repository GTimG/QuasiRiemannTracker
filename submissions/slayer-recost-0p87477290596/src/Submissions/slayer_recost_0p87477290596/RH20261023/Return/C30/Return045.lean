/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace RH20261023Return.C30
noncomputable section
def row045_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2169217501419271365688893099367406494/1896615074543947971626953125:ℝ), (2149017664253336117688727516992986378/632205024847982657208984375:ℝ), (6386695655699834075792829631856126336/1896615074543947971626953125:ℝ), (702953262677057769487481101748191232/632205024847982657208984375:ℝ)],
![(4202098859846709081430924425047487944/1896615074543947971626953125:ℝ), (4161991731203853535484603940913336984/632205024847982657208984375:ℝ), (4122048000746532757227797177619213824/632205024847982657208984375:ℝ), (4082266895476849252702791635165118464/1896615074543947971626953125:ℝ)],
![(81374535720987795980649414497247928/75864602981757918865078125:ℝ), (2014453387167602154656663792192934056/632205024847982657208984375:ℝ), (5983878145143102964351373953570817536/1896615074543947971626953125:ℝ), (1974880979720125119216630439423213568/1896615074543947971626953125:ℝ)]]
theorem row045_identity (δ p : ℝ) : rowMargin .oldPeak .weakC6 δ p =
 Record12518109.Bernstein.bsum 2 3 (60268584586185458960468458234351/883886688179997683687424000000000:ℝ) row045_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row045_coefficients,Fin.sum_univ_succ]
 ring
theorem row045_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .weakC6 δ p := by
 rw [row045_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row045_coefficients]
#print axioms row045_identity
#print axioms row045_pos
end
end RH20261023Return.C30
