/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row159_coefficients : Fin 3 → Fin 4 → ℝ := ![![(251389437669355734875398974992323759879001/1089246547427421594054375000000000:ℝ),(1519564660767895382691572584047435318158659/3267739642282264782163125000000000:ℝ),(1531984888186296794034820697927273605942/6382303988832548402662353515625:ℝ),(5291517357335122115792782486678981472/911757712690364057523193359375:ℝ)],
![(62148635309956491221808891233107533506909/136155818428427699256796875000000:ℝ),(2126843847390713191175809724565850425217/2334099744487331987259375000000:ℝ),(2921994746167659796643925581449434683504/6382303988832548402662353515625:ℝ),(19563950212505733903673425899096956672/6382303988832548402662353515625:ℝ)],
![(77848308568583640756663806534342592128437/340389546071069248141992187500000:ℝ),(92985120516515964934633406879709697819723/204233727642641548885195312500000:ℝ),(7239660832223699627427301601969777085152/31911519944162742013311767578125:ℝ),(1773028801785800833272348009593052416/6382303988832548402662353515625:ℝ)]]
theorem row159_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (6925893756975784504970109412472861/48732065609184257084038840320000000000000:ℝ) row159_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row159_coefficients,Fin.sum_univ_succ]
 ring
theorem row159_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row159_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row159_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row159_pos
