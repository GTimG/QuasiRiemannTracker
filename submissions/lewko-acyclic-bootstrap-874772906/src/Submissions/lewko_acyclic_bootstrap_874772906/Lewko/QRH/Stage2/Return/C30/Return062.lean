/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Return.C30
noncomputable section
def row062_coefficients : Fin 3 → Fin 4 → ℝ := ![![(18189737911633485950322194617/13332439444787824218750:ℝ), (52976302189517870123196611851/13332439444787824218750:ℝ), (5712018059640771437053890539/1481382160531980468750:ℝ), (1846828979177691174963677513/1481382160531980468750:ℝ)],
![(1803192714827404718579971169/740691080265990234375:ℝ), (15707253675116628826972447129/2222073240797970703125:ℝ), (15194443633476593995993135237/2222073240797970703125:ℝ), (326447847058108132661123441/148138216053198046875:ℝ)],
![(23117881505070675215478497/21331903111660518750:ℝ), (41807650746380245440959370923/13332439444787824218750:ℝ), (13432175470274175247671534707/4444146481595941406250:ℝ), (479162418337356040990552549/493794053510660156250:ℝ)]]
theorem row062_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (479162418337356040990552549/7363990662456803328000000000:ℝ) row062_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row062_coefficients,Fin.sum_univ_succ]
 ring
theorem row062_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row062_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row062_coefficients]
#print axioms row062_identity
#print axioms row062_pos
end
end LewkoStage2Return.C30
