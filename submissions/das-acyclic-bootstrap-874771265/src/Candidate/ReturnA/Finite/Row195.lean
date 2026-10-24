/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row195_coefficients : Fin 3 → Fin 4 → ℝ := ![![(283307492867021021932177866012416291/10346337641668186053995097656250:ℝ),(134770793387529729620242693537886321/2069267528333637210799019531250:ℝ),(254540452580526632111827078175879131/5173168820834093026997548828125:ℝ),(19736905466880006277671358370269658/1724389606944697675665849609375:ℝ)],
![(53740705860913955425115663933510251/1034633764166818605399509765625:ℝ),(609368444899126034423958683233576381/5173168820834093026997548828125:ℝ),(425040454125462923107275876091486247/5173168820834093026997548828125:ℝ),(28083328292100147718302058081403707/1724389606944697675665849609375:ℝ)],
![(331939888714941952299650285479045919/10346337641668186053995097656250:ℝ),(773657279013692852722688293753215757/10346337641668186053995097656250:ℝ),(565136897002112071172607736647606257/10346337641668186053995097656250:ℝ),(41093334214229196674304969353645473/3448779213889395351331699218750:ℝ)]]
theorem row195_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (28083328292100147718302058081403707/51431923384651187483278049280000000000:ℝ) row195_coefficients (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row195_coefficients,Fin.sum_univ_succ]
 ring
theorem row195_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row195_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row195_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row195_pos
