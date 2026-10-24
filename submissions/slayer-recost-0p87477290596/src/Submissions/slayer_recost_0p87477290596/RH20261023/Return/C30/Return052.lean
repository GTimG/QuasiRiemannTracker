/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace RH20261023Return.C30
noncomputable section
def row052_coefficients : Fin 3 → Fin 4 → ℝ := ![![(21537531860339374205352159433977293672/632205024847982657208984375:ℝ), (64296322627700282202014499953466502888/632205024847982657208984375:ℝ), (38388431085925215615416359129921253876/379323014908789594325390625:ℝ), (63665781497705326262885927216138641732/1896615074543947971626953125:ℝ)],
![(42371639974651781643571282996306721776/632205024847982657208984375:ℝ), (126484649235215916861004575893422124048/632205024847982657208984375:ℝ), (377567171610092356149197334877300775104/1896615074543947971626953125:ℝ), (125228140526390439580318493685954568288/1896615074543947971626953125:ℝ)],
![(87188532804293314605977557156202536/2645209308987375134765625:ℝ), (12440033885504893461596727872010084392/126441004969596531441796875:ℝ), (20628945781071099595079409671956756936/210735008282660885736328125:ℝ), (20524726698432808448401063316152254952/632205024847982657208984375:ℝ)]]
theorem row052_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (2565590837304101056050132914519031869/38617598664376218798759346176000000000:ℝ) row052_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row052_coefficients,Fin.sum_univ_succ]
 ring
theorem row052_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row052_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row052_coefficients]
#print axioms row052_identity
#print axioms row052_pos
end
end RH20261023Return.C30
