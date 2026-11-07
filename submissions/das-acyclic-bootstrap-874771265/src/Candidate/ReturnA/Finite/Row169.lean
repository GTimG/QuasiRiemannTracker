/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row169_coefficients : Fin 3 → Fin 4 → ℝ := ![![(872276262229040238146327393875504493700992579/3647030850761456230092773437500:ℝ),(15285556600116176393348113766289002010708643423/31911519944162742013311767578125:ℝ),(7676370259222682292498911875329265821600677888/31911519944162742013311767578125:ℝ),(7433855919639501108677583790947131981824/10211686382132077444259765625:ℝ)],
![(697607394742959488093152710731373825236887561/1458812340304582492037109375000:ℝ),(12221391834585905490015175077870336387732189533/12764607977665096805324707031250:ℝ),(613259709826082537099509750022990593980645376/1276460797766509680532470703125:ℝ),(7634922280914784627115870805275652465360896/6382303988832548402662353515625:ℝ)],
![(2790728858799581556858232461409783599657148231/11670498722436659936296875000000:ℝ),(1396789611216657103182233407521128189622214321/2917624680609164984074218750000:ℝ),(43797628490536377507027130725693805043468288/182351542538072811504638671875:ℝ),(103415328677420761079244676894711688462336/182351542538072811504638671875:ℝ)]]
theorem row169_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (197249085764733812483300546445296647/22812176084024996230425495994368000000000000:ℝ) row169_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row169_coefficients,Fin.sum_univ_succ]
 ring
theorem row169_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row169_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row169_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row169_pos
