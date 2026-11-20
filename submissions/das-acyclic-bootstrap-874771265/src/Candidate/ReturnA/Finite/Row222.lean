/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row222_coefficients : Fin 3 → Fin 4 → ℝ := ![![(940029683695084400624397822429025333/10346337641668186053995097656250:ℝ),(388468687928193180513640153914023177/2069267528333637210799019531250:ℝ),(561170385995617526943201428285906848/5173168820834093026997548828125:ℝ),(59705901568891530469026075926299072/5173168820834093026997548828125:ℝ)],
![(1091291184919225435739545999856608054/5173168820834093026997548828125:ℝ),(2345582667320274327946715972206980166/5173168820834093026997548828125:ℝ),(295502338480199880518425830800610304/1034633764166818605399509765625:ℝ),(222575701239638567427813911808929408/5173168820834093026997548828125:ℝ)],
![(26315083036694664244676497741566458/206926752833363721079901953125:ℝ),(1481946897617771856209152646396122586/5173168820834093026997548828125:ℝ),(1021663490805648061548283900336900672/5173168820834093026997548828125:ℝ),(197256069278412746097539032323689536/5173168820834093026997548828125:ℝ)]]
theorem row222_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (932904712013930163578532436348423/4821742817311048826557317120000000000:ℝ) row222_coefficients (63/128:ℝ) (33/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row222_coefficients,Fin.sum_univ_succ]
 ring
theorem row222_pos {δ p : ℝ} (hd : δ∈Set.Icc (63/128:ℝ) (33/64:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row222_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row222_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row222_pos
