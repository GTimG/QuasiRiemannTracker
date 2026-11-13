/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row038_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1161242932801348944271468852681/426627509499214433437500000:ℝ),(647669429200962157234837863503/85325501899842886687500000:ℝ),(1001219900511038672639681832929/142209169833071477812500000:ℝ),(102931065004143979962369448217/47403056611023825937500000:ℝ)],
![(852041514045419033418022189961/213313754749607216718750000:ℝ),(2319323061756727940755276177283/213313754749607216718750000:ℝ),(232898996582796966109067488487/23701528305511912968750000:ℝ),(23279465429456527893031607743/7900509435170637656250000:ℝ)],
![(7909240336643308951764148361/5267006290113758437500000:ℝ),(562866372475788264849348140317/142209169833071477812500000:ℝ),(490633009605786459542116808743/142209169833071477812500000:ℝ),(47061399583366256374716891391/47403056611023825937500000:ℝ)]]
theorem row038_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (47061399583366256374716891391/690357048457790545920000000000:ℝ) row038_coefficients (3/8:ℝ) (9/16:ℝ) (1/4:ℝ) (3/8:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row038_coefficients,Fin.sum_univ_succ]
 ring
theorem row038_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (9/16:ℝ)) (hp : p∈Set.Icc (1/4:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row038_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row038_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row038_pos
