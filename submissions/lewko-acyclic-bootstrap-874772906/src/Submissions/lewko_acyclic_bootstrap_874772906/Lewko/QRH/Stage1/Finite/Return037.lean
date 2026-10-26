/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row037_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3418151405881315011966173477/26664453421076522109375000:ℝ),(9120619462411237659424776859/26664453421076522109375000:ℝ),(16157146258792540382903744249/53328906842153044218750000:ℝ),(949342713617988162722307497/10665781368430608843750000:ℝ)],
![(2191045775307250362208232753/13332226710538261054687500:ℝ),(1352057692388461887719061289/3333056677634565263671875:ℝ),(4388280843620035151721421853/13332226710538261054687500:ℝ),(7770661811537891257856063/88881511403588407031250:ℝ)],
![(1817202654207634419950292029/26664453421076522109375000:ℝ),(4154681978238032288178601603/26664453421076522109375000:ℝ),(341158758524285136541943441/2962717046786280234375000:ℝ),(144391269480531962379836279/5332890684215304421875000:ℝ)]]
theorem row037_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (144391269480531962379836279/2427057804727320768000000000:ℝ) row037_coefficients (3/8:ℝ) (3/4:ℝ) (0:ℝ) (1/4:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row037_coefficients,Fin.sum_univ_succ]
 ring
theorem row037_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/4:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row037_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row037_coefficients]
#print axioms row037_identity
#print axioms row037_pos
end
end LewkoStage1Finite
