/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Fixed contribution of an original, filled, admissible frame at its actual
dual radius, after the native row extraction and before the first signed sum. -/
import Candidate.C092.transport.FixedFrameHorizon

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge CenteredExceptionalProfile
open QRH.SilDensitySplit.CubeFree
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
namespace QRH.Cycle092.FixedFramePacking
local notation "O" => HeckeFamily.O
variable {L mesh Z : ℝ} {θ : GData L}

theorem fixed_filled_admissible (r:GSrc θ mesh Z) (η:Character) (Q:Ideal O)
    (hQ₀ : Q ≠ 0) (hQt : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72:O)})
    (m:O) (hm:m≠0) (hlam:goodLambda∣m) (ht:(2:O)∣m)
    (labels:Finset (GLabel θ mesh Z)) (rows:GLabel θ mesh Z→Finset O)
    (E:GLabel θ mesh Z→O→ℝ) (H Mmin Mmax ε A A₀ c u' Lf err:ℝ)
    (adm:Second.AdmissibleGroup (gFrame L θ mesh η Z) Mmin Mmax mesh ε Z r labels H)
    (hZ₂:2≤Z) (hmsh:mesh≤1) (hA:0≤A)
    (hroot:A₀≤9179599/10000000) (hu:u'≤(QRH.SourceCertificate.u:ℝ))
    (ha:r.colLog≤A₀-c-u'+err) (hfill:1-6*u'≤H+err) (hmesh:0 ≤ mesh)
    (hmin:max 0 (115/1000-c)≤Real.logb Z (max 1 Lf)+err)
    (num:∀ x∈labels,∀ z∈rows x,Fits η r x ∧ z≠0 ∧ FixedInducingRow (x.char r) Q m 1 z)
    (support:∀ x∈labels,∀ z∈rows x,((Ideal.span {z}).absNorm:ℝ)≤
      2*CenteredMomentSectorLocalization.dyadicScale (x.n 1))
    (h15:∀ x∈labels,∀ z∈rows x,E x z≤A*r.vol^2/(prefixNorm x*max 1 Lf)) :
    ∑ x∈labels,gWeight x*(prefixNorm x*r.norm*∑ z∈rows x,E x z) ≤
      (Fintype.card DictIdx:ℝ)*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*A*
      Z^(r.colLog+r.twistLog+u' -(3036/100000)+3*mesh+Real.logb Z 2+(17/6)*err+ε/8) := by
  classical
  let S := labels.filter (fun x=>(rows x).Nonempty)
  have hsub : S⊆labels := Finset.filter_subset _ _
  have hfit : ∀ x∈S,Fits η r x := by
    intro x hx
    obtain ⟨z,hz⟩ := (Finset.mem_filter.mp hx).2
    exact (num x (hsub hx) z hz).1
  have he : ∀ x∈S, |gEnvelope r x-H| ≤ mesh := fun x hx=>adm.2.2.1 x (hsub hx)
  have hZ:=zero_lt_one.trans r.hZ
  have hl2 : 0≤Real.logb Z 2 := Real.logb_nonneg r.hZ (by norm_num)
  have hl2' : Real.logb Z 2≤1 := by
    rw [←Real.logb_self_eq_one r.hZ]
    exact Real.logb_le_logb_of_le r.hZ (by norm_num) hZ₂
  have hM : horizon Z H mesh≤Mmax+2 := by unfold horizon;linarith [adm.2.1]
  have hfib := fun (y:O) (hy:y≠0) (hyR:((Ideal.span {y}).absNorm:ℝ)≤Z^(horizon Z H mesh))=>
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset_filter (fun x:GLabel θ mesh Z=>x.twist∣y) hsub)
      (fun x _ _=>gWeight_nonneg x))
      (adm.2.2.2.2 y hy (hyR.trans (Real.rpow_le_rpow_of_exponent_le r.hZ.le hM)))
  have heq : (∑ x∈labels,gWeight x*(prefixNorm x*r.norm*∑ z∈rows x,E x z)) =
      ∑ x∈S,gWeight x*(prefixNorm x*r.norm*∑ z∈rows x,E x z) := by
    symm
    apply Finset.sum_subset hsub
    intro x hx hn
    have hn' : ¬(rows x).Nonempty := fun hh=>hn (Finset.mem_filter.mpr ⟨hx,hh⟩)
    simp [Finset.not_nonempty_iff_eq_empty.mp hn']
  rw [heq]
  rcases S.eq_empty_or_nonempty with hs|⟨x,hx⟩
  · rw [hs,Finset.sum_empty];positivity
  have H17 := native_fixed_price r η Q hQ₀ hQt hQ72 m hm hlam ht S hfit rows E A (Z^(ε/8)) (horizon Z H mesh) Lf
    hA (Real.rpow_nonneg hZ.le _) hfib (fun x hx z hz=>(num x (hsub hx) z hz).2)
    (fun x hx z hz=>native_row_cap r x (hfit x hx) H (he x hx) z (support x (hsub hx) z hz))
    (fun x hx=>h15 x (hsub hx))
  apply H17.trans
  have hf : 1-6*u'≤horizon Z H mesh+err := by unfold horizon;linarith
  have h18:=native_frame_excess r x (hfit x hx) (he x hx) hroot hu ha hf hmin
  have hl:0 < max 1 Lf:=zero_lt_one.trans_le (le_max_left _ _)
  let k:ℝ:=(Fintype.card DictIdx:ℝ)*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*A
  change k*Z^(ε/8)*Z^_/max 1 Lf ≤ k*Z^_
  calc
    _ = k*Z^((ε/8+(r.kLog+horizon Z H mesh/6))-Real.logb Z (max 1 Lf)) := by
      rw [Real.rpow_sub hZ,Real.rpow_add hZ (ε/8) (r.kLog+horizon Z H mesh/6),Real.rpow_logb hZ r.hZ.ne' hl];ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by dsimp [k];positivity)
      apply Real.rpow_le_rpow_of_exponent_le r.hZ.le
      linarith

#print axioms fixed_filled_admissible
end QRH.Cycle092.FixedFramePacking
