/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Partition by original retained subsets, then remove only the row restriction. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.LowErasure.Finite
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.LowErasure
noncomputable section
open scoped Classical BigOperators

theorem sum_original_subset_partition {Row Slot : Type*} (rows : Finset Row)
    (T : Finset Slot) (select : Row→Finset Slot) (hs : ∀r∈rows,select r⊆T)
    (g : Row→ℝ) :
    (∑r∈rows,g r)=∑F∈T.powerset,∑r∈rows.filter (fun r=>select r=F),g r := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  have hm : select r∈T.powerset := Finset.mem_powerset.mpr (hs r hr)
  simp only [Finset.sum_ite_eq,hm,ite_true]

/-- Each right-hand norm uses the full original row set and one fixed full
canonical subset. A row-dependent coefficient subset is never passed onward. -/
theorem varying_retained_norm {Row Slot : Type*} (rows : Finset Row)
    (weight : Row→ℝ) (D : Row→ℂ) (slot : Row→Slot→ℂ) (T : Finset Slot)
    (select : Row→Finset Slot) (hs : ∀r∈rows,select r⊆T)
    (hw : ∀r∈rows,0≤weight r) (Z q pay : ℝ) (w : Slot→ℝ)
    (hZ : 0<Z) (hpay : 0≤pay)
    (hslot : ∀r∈rows,weight r≠0 → ∀j∈T\select r,‖slot r j‖^2≤pay*Z^(q*w j)) :
    retainedNorm rows weight D slot T ≤
      ∑F∈T.powerset, erasurePayment Z q pay w T F * retainedNorm rows weight D slot F := by
  have he := sum_original_subset_partition rows T select hs
    (fun r=>‖D r*∏j∈T,slot r j‖^2*weight r)
  change retainedNorm rows weight D slot T=
    ∑F∈T.powerset,retainedNorm (rows.filter (fun r=>select r=F)) weight D slot T at he
  rw [he]
  apply Finset.sum_le_sum
  intro F hF
  have hsub : F⊆T := Finset.mem_powerset.mp hF
  have hr : rows.filter (fun r=>select r=F)⊆rows := Finset.filter_subset _ _
  have hlocal := fixed_retained_norm (rows.filter (fun r=>select r=F)) weight D slot T F hsub
    (fun r h=>hw r (hr h)) Z q pay w hZ
    (by
      intro r h hn j hj
      obtain ⟨hmem,heq⟩ := Finset.mem_filter.mp h
      exact hslot r hmem hn j (by simpa only [heq] using hj))
  exact hlocal.trans (mul_le_mul_of_nonneg_left
    (retainedNorm_mono_rows rows _ hr weight D slot F hw)
    (erasurePayment_nonneg Z q pay w T F hZ.le hpay))

/-- The finite partition cost depends only on the original ambient slot cap. -/
theorem original_subsets_payment {Slot : Type*} (T : Finset Slot) (N : ℕ)
    (hN : T.card≤N) (payment : Finset Slot→ℝ) (E : ℝ) (hE : 0≤E)
    (hpayment : ∀F∈T.powerset,payment F≤E) :
    (∑F∈T.powerset,payment F)≤(2:ℝ)^N*E := by
  calc
    _≤∑F∈T.powerset,E := Finset.sum_le_sum hpayment
    _=(2:ℝ)^T.card*E := by simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    _≤(2:ℝ)^N*E := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hN) hE
end
end QRH.Record1252270103Source.LowErasure
#print axioms QRH.Record1252270103Source.LowErasure.sum_original_subset_partition
#print axioms QRH.Record1252270103Source.LowErasure.varying_retained_norm
#print axioms QRH.Record1252270103Source.LowErasure.original_subsets_payment
