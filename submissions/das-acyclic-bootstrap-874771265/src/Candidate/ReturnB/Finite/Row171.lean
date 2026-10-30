/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row171_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5199061093815805664089603992824211153176067673/1361540694699475611328125000000:ℝ),(1950048735365559861472317642721017325077322967/255288880256151677124023437500:ℝ),(7869243732671849286153932413293384659058688/2058781292388319976806640625:ℝ),(140359412675020546685124453282394224459776/63822220064037919281005859375:ℝ)],
![(2079600585525783971066929576535398170304955683/272308138939895122265625000000:ℝ),(3899798970927338264260393581798865917445185697/255288880256151677124023437500:ℝ),(487760640204098123780987091930490011280818176/63822220064037919281005859375:ℝ),(217282241866681397410035951847869396287488/63822220064037919281005859375:ℝ)],
![(104000369795160739982720448823121612555501431469/27230813893989512226562500000000:ℝ),(39007116522994865423824276083585540810468180547/5105777605123033542480468750000:ℝ),(1219827375216855953779493424276736964689129472/319111100320189596405029296875:ℝ),(636919908595414631609552231459300784996352/319111100320189596405029296875:ℝ)]]
theorem row171_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (25902061684928106952909940701469111/31936636277595440736959987712000000000000000:ℝ) row171_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row171_coefficients,Fin.sum_univ_succ]
 ring
theorem row171_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row171_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row171_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row171_pos
