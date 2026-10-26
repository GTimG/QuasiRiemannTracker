/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row062_coefficients : Fin 3 → Fin 4 → ℝ := ![![(18187216097748981246240600010337/13332226710538261054687500:ℝ),(1961815850840408492402371289593/493786174464380039062500:ℝ),(51401172380257096637447547482011/13332226710538261054687500:ℝ),(5539741030291326577321582557779/4444075570179420351562500:ℝ)],
![(16227739496462326338213336308881/6666113355269130527343750:ℝ),(2479947401881640764211770424753/350848071329954238281250:ℝ),(45580788136201505552719637344471/6666113355269130527343750:ℝ),(979291722735165441890934872203/444407557017942035156250:ℝ)],
![(21406086719940293292638309747/19751446978575201562500:ℝ),(41809101275541773618372405383603/13332226710538261054687500:ℝ),(40298123401166353517645477387881/13332226710538261054687500:ℝ),(4312654796703528185001362444501/4444075570179420351562500:ℝ)]]
theorem row062_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (4312654796703528185001362444501/66274858454420705771520000000000:ℝ) row062_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
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
end LewkoStage1Finite
