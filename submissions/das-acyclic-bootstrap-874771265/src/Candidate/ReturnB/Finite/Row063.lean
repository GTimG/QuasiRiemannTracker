/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row063_coefficients : Fin 3 → Fin 4 → ℝ := ![![(14772890487992993398220704036788089393/414453470575314183750000000000:ℝ),(43508492836861180562282472069224789779/414453470575314183750000000000:ℝ),(128116234034858173901246728856102542937/1243360411725942551250000000000:ℝ),(3809941511539697187865402250799312889/113032764702358413750000000000:ℝ)],
![(13880478713360302819018994618211298193/207226735287657091875000000000:ℝ),(3712892983425189347399726008612508249/18838794117059735625000000000:ℝ),(120148402996993324321522353110432136577/621680205862971275625000000000:ℝ),(39264296804660193804719278680853258939/621680205862971275625000000000:ℝ)],
![(13029441538052925851563737532743443753/414453470575314183750000000000:ℝ),(38298848566329123165343855712113001731/414453470575314183750000000000:ℝ),(2501119338983510285168277997098522439/27630231371687612250000000000:ℝ),(12247357198692480285359866777108278607/414453470575314183750000000000:ℝ)]]
theorem row063_identity (δ p : ℝ) : rowMargin .oldPeak .P δ p =
 Record12518109.Bernstein.bsum 2 3 (12247357198692480285359866777108278607/197784900203852524903464960000000000000:ℝ) row063_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row063_coefficients,Fin.sum_univ_succ]
 ring
theorem row063_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldPeak .P δ p := by
 rw [row063_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row063_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row063_pos
