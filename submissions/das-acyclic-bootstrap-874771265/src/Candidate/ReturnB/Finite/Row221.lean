/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row221_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3639529907565065615071201889137990999/502554893439173299983228515625:ℝ),(4874517884419051583865453957196382383/279197163021762944435126953125:ℝ),(33357436560807694140927255351144829184/2512774467195866499916142578125:ℝ),(7683643451125919388605867039762655232/2512774467195866499916142578125:ℝ)],
![(40341415123382519094627649675568973532/2512774467195866499916142578125:ℝ),(32982466848759088346423283626798161444/837591489065288833305380859375:ℝ),(77298447382070021694928809439340807168/2512774467195866499916142578125:ℝ),(6230286817531647688123030224890515456/837591489065288833305380859375:ℝ)],
![(23124915431946047930070860082867677612/2512774467195866499916142578125:ℝ),(3866863704819442614344346239163780164/167518297813057766661076171875:ℝ),(15616702353225789963875218860295881728/837591489065288833305380859375:ℝ),(11971246635473559425939423838329870336/2512774467195866499916142578125:ℝ)]]
theorem row221_identity (δ p : ℝ) : rowMargin .newKink .P δ p =
 Record12518109.Bernstein.bsum 2 3 (3751779028870077826467708515509109/18736604442413318478336491520000000000:ℝ) row221_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row221_coefficients,Fin.sum_univ_succ]
 ring
theorem row221_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .P δ p := by
 rw [row221_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row221_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row221_pos
