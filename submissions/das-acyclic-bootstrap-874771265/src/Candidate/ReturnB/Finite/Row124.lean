/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row124_coefficients : Fin 3 → Fin 4 → ℝ := ![![(285140802179152359037938468828791087/61283917193750832919921875:ℝ),(2512724477951589334795949715426010873/183851751581252498759765625:ℝ),(2459635549784630687563150098020185088/183851751581252498759765625:ℝ),(802332627312800871149790893572734976/183851751581252498759765625:ℝ)],
![(565045162389360980492909694465919576/61283917193750832919921875:ℝ),(4977761277192578255700524485127736296/183851751581252498759765625:ℝ),(4871029140190468702495970798797201408/183851751581252498759765625:ℝ),(317680327413837724978522605350944768/36770350316250499751953125:ℝ)],
![(280098633847166060289858015186564464/61283917193750832919921875:ℝ),(2466780320920162615267591260961458448/183851751581252498759765625:ℝ),(482626437422433590324259203715579904/36770350316250499751953125:ℝ),(786646905658992475005460320051134464/183851751581252498759765625:ℝ)]]
theorem row124_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (6001639600059451866191561279687/2741796042895124197539840000000000:ℝ) row124_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row124_coefficients,Fin.sum_univ_succ]
 ring
theorem row124_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
 rw [row124_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row124_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row124_pos
