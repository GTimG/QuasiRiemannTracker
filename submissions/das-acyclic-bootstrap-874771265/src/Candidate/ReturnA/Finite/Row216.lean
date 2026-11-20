/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row216_coefficients : Fin 3 → Fin 4 → ℝ := ![![(31242487983174837886564591857068327/1034633764166818605399509765625:ℝ),(71511225236411213242067519302812781/1034633764166818605399509765625:ℝ),(50659187035253135087059463592251831/1034633764166818605399509765625:ℝ),(3458833125316467219630351371752459/344877921388939535133169921875:ℝ)],
![(375661239242120554039717884382177934/5173168820834093026997548828125:ℝ),(879401086478678950719404803547767186/5173168820834093026997548828125:ℝ),(129337662645836099787185299295727664/1034633764166818605399509765625:ℝ),(47598337175293721152306424989766356/1724389606944697675665849609375:ℝ)],
![(258368960812658074597230681175016149/5173168820834093026997548828125:ℝ),(636232138373167600497059404521450581/5173168820834093026997548828125:ℝ),(202184330003613827236593699570230071/2069267528333637210799019531250:ℝ),(85008831661211683901352906193385497/3448779213889395351331699218750:ℝ)]]
theorem row216_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (3458833125316467219630351371752459/5143192338465118748327804928000000000:ℝ) row216_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row216_coefficients,Fin.sum_univ_succ]
 ring
theorem row216_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (33/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row216_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row216_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row216_pos
