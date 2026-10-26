/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Erasure retains the exact subset fiber on which the actual rounded source
budget holds. The two supported positive corners keep separate fibers. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalPositiveCornerSplit
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.LowErasure.Partition
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily ConcretePrimeRowBridge CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentSecondHeightFamily CenteredMomentHeckeExpansion
open QRH.Record1252270103Low QRH.Record1252270103KernelMass LowErasure
local notation "O"=>HeckeFamily.O

theorem restricted_varying_retained_norm {Row Slot:Type*}(rows:Finset Row)
    (weight:Row→ℝ)(D:Row→ℂ)(slot:Row→Slot→ℂ)(T:Finset Slot)
    (select:Row→Finset Slot)(hs:∀r∈rows,select r⊆T)
    (hw:∀r∈rows,0≤weight r)(Z q pay:ℝ)(w:Slot→ℝ)(hZ:0<Z)
    (hslot:∀r∈rows,weight r≠0→∀j∈T\select r,‖slot r j‖^2≤pay*Z^(q*w j)):
    retainedNorm rows weight D slot T≤
      ∑F∈T.powerset,erasurePayment Z q pay w T F*
        retainedNorm (rows.filter (fun r=>select r=F)) weight D slot F := by
  have he:=sum_original_subset_partition rows T select hs
    (fun r=>‖D r*∏j∈T,slot r j‖^2*weight r)
  change retainedNorm rows weight D slot T=
    ∑F∈T.powerset,retainedNorm (rows.filter (fun r=>select r=F)) weight D slot T at he
  rw [he]
  apply Finset.sum_le_sum
  intro F hF
  apply fixed_retained_norm _ weight D slot T F (Finset.mem_powerset.mp hF)
    (fun r hr=>hw r (Finset.mem_filter.mp hr).1) Z q pay w hZ
  intro r hr hn j hj
  obtain ⟨hr,he⟩:=Finset.mem_filter.mp hr
  exact hslot r hr hn j (by simpa only [he] using hj)

/-- Positive-corner zero filtering and subset selection precede ordinary
source admission. Neither restriction is dropped from the source family. -/
theorem centered_newton_erasure_partition {Row Slot:Type*}(rows:Finset Row)
    (ι:Row→Type*)[∀r,Fintype (ι r)](s:∀r,Input (ι r))
    (A₁ A₂ R:Row→Ideal O)(b:Row→ℝ)(S A:Finset (Ideal O))
    (τ:Row→Character)(t:Row→ℝ)(z:Row→O)(slot:Row→Slot→ℂ)(T:Finset Slot)
    (weight:Row→ℝ)(hw:∀r∈rows,0≤weight r)(hb:∀r∈rows,0≤b r)
    (hb₁:∀r∈rows,(s r).b₁≤b r)(hb₂:∀r∈rows,(s r).b₂≤b r)
    (hd:GoodPair (newtonDivisorPair S A))
    (select:Bool→Row→Finset Slot)(hs:∀side r,r∈rows→select side r⊆T)
    (Z q pay:ℝ)(w:Slot→ℝ)(hZ:0<Z)
    (hslot:∀side r,r∈rows→weight r≠0→∀j∈T\select side r,‖slot r j‖^2≤pay*Z^(q*w j)):
    let D:=fun side r=>positiveNewtonCofactorPlain side (s r) (A₁ r) (A₂ r) (R r) (b r) S A (τ r) (t r) (z r)
    let live:=fun side=>rows.filter (fun r=>D side r*(∏j∈T,slot r j)≠0)
    let budget:=fun side=>∑F∈T.powerset,erasurePayment Z q pay w T F*
      retainedNorm ((live side).filter (fun r=>select side r=F)) weight (D side) slot F
    (∑r∈rows,‖newtonCofactorPlain (s r) (A₁ r) (A₂ r) (R r) (b r) S A (τ r) (t r) (z r)*
      (∏j∈T,slot r j)‖^2*weight r)≤2*(budget false+budget true) := by
  intro D live budget
  have hbase:=centered_newton_positive_corner_family rows ι s A₁ A₂ R b S A τ t z
    (fun r=>∏j∈T,slot r j) weight hw hb hb₁ hb₂ hd
  have he (side:Bool):retainedNorm (live side) weight (D side) slot T≤budget side := by
    apply restricted_varying_retained_norm _ weight (D side) slot T (select side)
      (fun r hr=>hs side r (Finset.mem_filter.mp hr).1)
      (fun r hr=>hw r (Finset.mem_filter.mp hr).1) Z q pay w hZ
    intro r hr hn j hj
    exact hslot side r (Finset.mem_filter.mp hr).1 hn j hj
  exact hbase.trans (mul_le_mul_of_nonneg_left (add_le_add (he false) (he true)) (by norm_num))

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.restricted_varying_retained_norm
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.centered_newton_erasure_partition
