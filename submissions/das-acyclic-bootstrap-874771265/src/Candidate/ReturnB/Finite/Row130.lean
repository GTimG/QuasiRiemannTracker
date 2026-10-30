/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row130_coefficients : Fin 3 → Fin 4 → ℝ := ![![(220959992965767692860091886473837129/367703503162504997519531250:ℝ),(634472582263022946021080789023825121/367703503162504997519531250:ℝ),(60654362434992872048233312425756928/36770350316250499751953125:ℝ),(1440516745914913286168668134828032/2744055993750037294921875:ℝ)],
![(219654746844429065274695808379195232/183851751581252498759765625:ℝ),(630404253612653350849023984079573088/183851751581252498759765625:ℝ),(120465099358746236188280027017527296/36770350316250499751953125:ℝ),(191574187660651461933368621887258624/183851751581252498759765625:ℝ)],
![(704827242719919885045748672595456/1186140332782274185546875:ℝ),(62677427186208105429848699274603008/36770350316250499751953125:ℝ),(59854324566374506879772616466628608/36770350316250499751953125:ℝ),(19026360534435572383579526042484736/36770350316250499751953125:ℝ)]]
theorem row130_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (18144951376376697906093145411/8568112634047263117312000000000:ℝ) row130_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row130_coefficients,Fin.sum_univ_succ]
 ring
theorem row130_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
 rw [row130_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row130_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row130_pos
