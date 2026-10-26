/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.C30.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Return.C30
noncomputable section
def row104_coefficients : Fin 3 → Fin 4 → ℝ := ![![(963313891948369558015684219/87445837638147199218750:ℝ), (6700974520288355357839513993/262337512914441597656250:ℝ), (494185292876527532584118624/26233751291444159765625:ℝ), (563267007095334615110299952/131168756457220798828125:ℝ)],
![(211042289270065171617229484/8744583763814719921875:ℝ), (7348339834343055969958343188/131168756457220798828125:ℝ), (5426377658708167077394575296/131168756457220798828125:ℝ), (1238996450545514777882174368/131168756457220798828125:ℝ)],
![(615977534230274781836643848/43722918819073599609375:ℝ), (4365003035879391871928998904/131168756457220798828125:ℝ), (3308611991082825352184283376/131168756457220798828125:ℝ), (788991169055762969140216016/131168756457220798828125:ℝ)]]
theorem row104_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (35204187943458413444393747/15282267774542972928000000000:ℝ) row104_coefficients (33/64:ℝ) (9/16:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row104_coefficients,Fin.sum_univ_succ]
 ring
theorem row104_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row104_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row104_coefficients]
#print axioms row104_identity
#print axioms row104_pos
end
end Record1252270103Return.C30
