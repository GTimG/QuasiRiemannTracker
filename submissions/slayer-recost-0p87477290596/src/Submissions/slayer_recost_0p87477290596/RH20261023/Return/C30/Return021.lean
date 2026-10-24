/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace RH20261023Return.C30
noncomputable section
def row021_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5865984340177175535505780666012197872/632205024847982657208984375:ℝ), (3484480160302978536065941509713289008/126441004969596531441796875:ℝ), (17247549401101420730011979544874532864/632205024847982657208984375:ℝ), (70260890574264685743128273608892416/7805000306765217990234375:ℝ)],
![(11520150120398186982272739644907978352/632205024847982657208984375:ℝ), (34211126695533131945791716754475169392/632205024847982657208984375:ℝ), (33863208857213269043542258483734192128/632205024847982657208984375:ℝ), (11172230654985686665675118874167001088/632205024847982657208984375:ℝ)],
![(1131015926873303278072182318346764556/126441004969596531441796875:ℝ), (16791468090970721947484677472071758652/632205024847982657208984375:ℝ), (5539467408703182331217743565095794688/210735008282660885736328125:ℝ), (5482012945528941720289049189949448192/632205024847982657208984375:ℝ)]]
theorem row021_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (669191033389763393589971824945001/4714062336959987646332928000000000:ℝ) row021_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row021_coefficients,Fin.sum_univ_succ]
 ring
theorem row021_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row021_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row021_coefficients]
#print axioms row021_identity
#print axioms row021_pos
end
end RH20261023Return.C30
