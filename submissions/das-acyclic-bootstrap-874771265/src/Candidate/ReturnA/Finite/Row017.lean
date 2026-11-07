/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row017_coefficients : Fin 3 → Fin 4 → ℝ := ![![(34884916439898450752667580657740141391/467181133612360587246093750:ℝ),(104128927836240056824077888806216611039/467181133612360587246093750:ℝ),(5920236937662615267394204164166178051/26696064777849176414062500:ℝ),(68720268851216397926168375089488292489/934362267224721174492187500:ℝ)],
![(34256360284163767529292906299807143189/233590566806180293623046875:ℝ),(102245915789650389341074152832636442347/233590566806180293623046875:ℝ),(101723793975282459751711442798615097452/233590566806180293623046875:ℝ),(33734237875024603559378014187660798294/233590566806180293623046875:ℝ)],
![(33633186166418645061569920014528926137/467181133612360587246093750:ℝ),(20075810276996671826645636971590264791/93436226722472117449218750:ℝ),(99859590618840538600623608514575029049/467181133612360587246093750:ℝ),(33113724797780288403211185202402631231/467181133612360587246093750:ℝ)]]
theorem row017_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (33113724797780288403211185202402631231/228298261637494905011919912960000000000:ℝ) row017_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row017_coefficients,Fin.sum_univ_succ]
 ring
theorem row017_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row017_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row017_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row017_pos
