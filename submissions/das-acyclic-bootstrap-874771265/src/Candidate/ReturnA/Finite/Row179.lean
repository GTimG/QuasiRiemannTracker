/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row179_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2014556387576744310347632246922428144265719/32677396422822647821631250000000000:ℝ),(4029516149126209149730014821130708996925351/32677396422822647821631250000000000:ℝ),(573748752804658632309410623109375011693/9117577126903640575231933593750:ℝ),(8046230037025156288530881377168390234/6382303988832548402662353515625:ℝ)],
![(12883330584515930680708189633164153535681/102116863821320774442597656250000:ℝ),(25966594127950247440160020630575101754001/102116863821320774442597656250000:ℝ),(120899142546640636971863738183798851292/911757712690364057523193359375:ℝ),(28527498565902987352531971157284648524/6382303988832548402662353515625:ℝ)],
![(414189924041573686429047226887256359881/6382303988832548402662353515625:ℝ),(843202792920193095370444177341337404293/6382303988832548402662353515625:ℝ),(451931810445082926252991940509009673458/6382303988832548402662353515625:ℝ),(3269640148600867325931377102824625578/911757712690364057523193359375:ℝ)]]
theorem row179_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (4023115018512578144265440688584195117/779713049746948113344621445120000000000000:ℝ) row179_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row179_coefficients,Fin.sum_univ_succ]
 ring
theorem row179_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row179_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row179_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row179_pos
