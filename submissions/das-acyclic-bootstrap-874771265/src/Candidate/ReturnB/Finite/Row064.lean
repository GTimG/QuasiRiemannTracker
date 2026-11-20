/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row064_coefficients : Fin 3 → Fin 4 → ℝ := ![![(250381963245145984306755636287215019009/239195171097521322750000000000:ℝ),(743740497014981065707446235418568482307/239195171097521322750000000000:ℝ),(81818694569417848700925327491937272363/26577241233057924750000000000:ℝ),(27001073451763555803733749810675776441/26577241233057924750000000000:ℝ)],
![(80778498958444563225850109740735191787/39865861849586887125000000000:ℝ),(239884438498774223174548855869540569729/39865861849586887125000000000:ℝ),(47488910297480016880030902326888688221/7973172369917377425000000000:ℝ),(26112864238325708868164761835212687721/13288620616528962375000000000:ℝ)],
![(106580006618655419821758597166046560951/108725077771600601250000000000:ℝ),(139225209188233988926040253827456512919/47839034219504264550000000000:ℝ),(37035372430461650719137557652486671233/12859955435350608750000000000:ℝ),(25245315187530199052691073996030217159/26577241233057924750000000000:ℝ)]]
theorem row064_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (25245315187530199052691073996030217159/405860913471596447555125248000000000000:ℝ) row064_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row064_coefficients,Fin.sum_univ_succ]
 ring
theorem row064_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row064_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row064_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row064_pos
