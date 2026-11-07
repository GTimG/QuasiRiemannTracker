/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row155_coefficients : Fin 3 → Fin 4 → ℝ := ![![(30261192733793669015366575521102014410199/25529215955330193610649414062500:ℝ),(344141283676401891542220830508283194773503/127646079776650968053247070312500:ℝ),(58736544422135892599069733930390004921472/31911519944162742013311767578125:ℝ),(2105514490930553851502406137261866332544/6382303988832548402662353515625:ℝ)],
![(221647855104931561482208931847414451849669/102116863821320774442597656250000:ℝ),(2439874005914502447410927115147228876058301/510584319106603872212988281250000:ℝ),(13925997374933055464994791940998326246528/4558788563451820287615966796875:ℝ),(2850905035189575653738284866380512023296/6382303988832548402662353515625:ℝ)],
![(1649250396162268255236871837245037017491471/1633869821141132391081562500000000:ℝ),(17606067868796576793961847633554596068607607/8169349105705661955407812500000000:ℝ),(5865552196728655631118546052152729079496/4558788563451820287615966796875:ℝ),(899388144984029176157065925256637419136/6382303988832548402662353515625:ℝ)]]
theorem row155_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (7026469882687727938727077541067479837/779713049746948113344621445120000000000000:ℝ) row155_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row155_coefficients,Fin.sum_univ_succ]
 ring
theorem row155_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row155_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row155_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row155_pos
