/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row191_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1776640189741498636647750800432731/165541402266690976863921562500000:ℝ),(3577391235133587253376770525887337/165541402266690976863921562500000:ℝ),(2228520177731849386976944185193331/165541402266690976863921562500000:ℝ),(16217939305279514159326128389549/6621656090667639074556862500000:ℝ)],
![(3179101375915696906714174858358779/82770701133345488431960781250000:ℝ),(6198626642786158476781727220484393/82770701133345488431960781250000:ℝ),(3633178802872771495621825033699649/82770701133345488431960781250000:ℝ),(113802447317352818604946034314807/16554140226669097686392156250000:ℝ)],
![(9878887434624006436426088916284827/165541402266690976863921562500000:ℝ),(22556058835789496617141821340936849/165541402266690976863921562500000:ℝ),(16953740841140471813142334465380617/165541402266690976863921562500000:ℝ),(837457368228777993473503408145719/33108280453338195372784312500000:ℝ)]]
theorem row191_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (16217939305279514159326128389549/3013589260819405516598323200000000:ℝ) row191_coefficients (3/8:ℝ) (3/4:ℝ) (0/1:ℝ) (1/4:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row191_coefficients,Fin.sum_univ_succ]
 ring
theorem row191_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (3/4:ℝ)) (hp : p∈Set.Icc (0/1:ℝ) (1/4:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row191_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row191_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row191_pos
