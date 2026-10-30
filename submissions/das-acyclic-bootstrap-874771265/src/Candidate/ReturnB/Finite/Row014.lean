/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row014_coefficients : Fin 3 → Fin 4 → ℝ := ![![(59411868953848829771464927591334880649/24916163655991804453125000:ℝ),(59261379485448826554516183604157135753/8305387885330601484375000:ℝ),(177333110311982073888923517433303890971/24916163655991804453125000:ℝ),(2183734840276256627886458098969161643/922820876147844609375000:ℝ)],
![(19624393794131352348026813923171558979/4152693942665300742187500:ℝ),(176169211287095379064925098763308945691/12458081827995902226562500:ℝ),(175719319383752286951200529814349312171/12458081827995902226562500:ℝ),(6491476595135852286327885424783893713/1384231314221766914062500:ℝ)],
![(212133784511134491045311316245695579/90604231476333834375000:ℝ),(5631005651390595683611382006530304533/803747214709413046875000:ℝ),(174112419807283847817879161023966935521/24916163655991804453125000:ℝ),(6432003914566776825119783017781253247/2768462628443533828125000:ℝ)]]
theorem row014_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (6432003914566776825119783017781253247/43291830770303621072546693120000000000:ℝ) row014_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (255/512:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row014_coefficients,Fin.sum_univ_succ]
 ring
theorem row014_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (255/512:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row014_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row014_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row014_pos
