/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
One fixed reserve pays every actual buffered HIGH density. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalBufferedPaidSome
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalBufferedPaidNatural
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalPaidBudget
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open LocalMoment Cycle61InitialMass Record12518109Natural

def bufferedPaidBudget (N I J:ℕ)(δ B τ upper Z e omega err errv fee reserve other pref:ℝ)
    (C profileCost geometry profileControl box:ℝ)(p:BufferIndex e):ℝ :=
  (C*Z^pref*profileCost)*((max 1 profileCost)^2*(geometry*
    cofactorRestorationCost δ B Z*profileControl*box*(1+rawGeometryHeight Z τ I)^J*
    Z^(((1-unmarkedDensity (2*bufferValue e p-1))*omega+
      unmarkedDensity (2*bufferValue e p-1)*err+errv)-(fee+reserve)+
      (2*bufferValue e p-1)*(3*(N:ℝ)*Real.logb Z upper)+other)))

theorem buffered_density_bounds (e q:ℝ)(hq:1/2≤q)(p:BufferIndex e)
    (hp:p∈BufferedSelectedPaidSome.highBins e q):
    0≤2*bufferValue e p-1 ∧ 2*bufferValue e p-1≤3/4 ∧
      0≤unmarkedDensity (2*bufferValue e p-1) ∧ unmarkedDensity (2*bufferValue e p-1)≤1 := by
  have ha:=(Finset.mem_filter.mp hp).2
  have hν0:0≤2*bufferValue e p-1:=by linarith only [ha.1,hq]
  have hν1:2*bufferValue e p-1≤3/4:=by linarith only [ha.2]
  exact ⟨hν0,hν1,(by linarith only [unmarkedDensity_ge_two_sevenths hν1]),unmarkedDensity_le_one hν0 hν1⟩

/-- The finite factor is fixed with the buffered partition. No individual
row or density bound is an analytic input to this scalar payment. -/
theorem buffered_paid_sum (N I J:ℕ)(δ B τ upper Z e q omega err errv fee reserve other pref saving:ℝ)
    (C profileCost geometry profileControl box:ℝ)
    (hZ:1<Z)(hτ:0≤τ)(hu:1≤upper)(hq:1/2≤q)
    (hC:0≤C)(hp:0≤profileCost)(hg:0≤geometry)(hc:0≤profileControl)(hb:0≤box)
    (homega:0≤omega)(herr:0≤err)
    (hbudget:pref+2*δ+τ*(J:ℝ)+omega+err+errv+other+saving≤fee+reserve):
    (∑p∈BufferedSelectedPaidSome.highBins e q,
      bufferedPaidBudget N I J δ B τ upper Z e omega err errv fee reserve other pref C profileCost geometry profileControl box p)≤
    ((BufferedSelectedPaidSome.highBins e q).card:ℝ)*
      (C*profileCost*(max 1 profileCost)^2*cofactorFixedRestoration δ B*
        bufferedHeightConstant I J*upper^(3*N)*box)*geometry*profileControl*Z^(-saving) := by
  let constant:=(C*profileCost*(max 1 profileCost)^2*cofactorFixedRestoration δ B*
    bufferedHeightConstant I J*upper^(3*N)*box)*geometry*profileControl*Z^(-saving)
  have hone (p:BufferIndex e)(hpm:p∈BufferedSelectedPaidSome.highBins e q):
      bufferedPaidBudget N I J δ B τ upper Z e omega err errv fee reserve other pref C profileCost geometry profileControl box p≤constant := by
    have hd:=buffered_density_bounds e q hq p hpm
    have hpaid:=high_error_ledger _ omega err errv fee reserve other pref δ τ J saving
      hd.2.2.1 hd.2.2.2 homega herr hbudget
    have h:=paid_high_reserve N I J δ B τ upper Z (2*bufferValue e p-1)
      (((1-unmarkedDensity (2*bufferValue e p-1))*omega+
        unmarkedDensity (2*bufferValue e p-1)*err+errv)-(fee+reserve)+other)
      pref saving C profileCost geometry profileControl box hZ hτ hu
      (hd.2.1.trans (by norm_num)) hC hp hg hc hb hpaid
    convert h using 1 <;> dsimp only [bufferedPaidBudget,constant]
    congr 2
    congr 1
    ring
  calc
    _≤∑_p∈BufferedSelectedPaidSome.highBins e q,constant:=Finset.sum_le_sum hone
    _=_:=by simp only [Finset.sum_const,nsmul_eq_mul];dsimp only [constant];ring

theorem high_bins_natural_eq (e q:ℝ):
    BufferedSelectedPaidNatural.highBins e q=BufferedSelectedPaidSome.highBins e q := rfl
end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.buffered_density_bounds
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.buffered_paid_sum
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.high_bins_natural_eq
