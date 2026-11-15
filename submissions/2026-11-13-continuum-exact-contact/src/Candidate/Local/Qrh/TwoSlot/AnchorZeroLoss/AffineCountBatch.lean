/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Explicit-line batch counts, adapted from Sil's PR137 ImprovedBatch
(copyright (c) 2026 Sil, Apache-2.0) and Hailey Collet's batch/(envelope (line := line))
count theorems (Apache-2.0). -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.AffineCountFiber
import Submissions.hailey_collet_1252270103.Record1252270103Return.WindowBatch
import Submissions.hailey_collet_1252270103.Cycle25.Assembly.Count.Adaptive

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Qrh.TwoSlot.AnchorZeroLoss.Affine.Return
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter OAI OAI.SevenEighths QRH.Record12518109Count QRH.Record1252270103Return
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst Cycle25DetectorRowCount
open HeckeDetectorFixedAmplitudeCount
variable {line : Line} [CapacityBounds line]

/-- Batch counts at a native and at an improved window (one amplifier). -/
theorem fixed_amplitude_windows_count
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠU : ℝ in atTop,
      (∀naturalκ:ℝ,7/10≤naturalκ → naturalκ≤3/4 → ∀w:AdmittedWindow naturalκ,
      ∀(a ε T allowance ν C height q:ℝ) (i:ℕ),
      1<U → 51/100<a → 2*a-1≤3/4 → 0≤ε → ε≤1/10000000 →
      0<ν → ν≤1/10000000 → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      w.Available (2*a-1) (q/(2*a-1)) →
      ∀{Label Slot:Type} [Fintype Label]
      (B:Batch M H Label Slot U a ε (w.cutoff (2*a-1) (q/(2*a-1))) T allowance i),
      (∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u:FreeRow=>u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀bin j J K,∀hne:(B.fiberRows bin j J K).Nonempty,
        Cycle25DetectorRawFiber.Moments (B.fiber bin j J K hne) naturalκ c κ C height εm) →
      (∀bin j J K,∀hne:(B.fiberRows bin j J K).Nonempty,
        AffineMarkedMoment (B.fiber bin j J K hne) w.face C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2*fiberConstant C height K₀*
        (Fintype.card B.Bin:ℝ)*U^(w.value (2*a-1) (q/(2*a-1))+159*ε+εm+B.mesh+7*ν)) ∧
      (∀naturalκ:ℝ,7/10≤naturalκ → naturalκ≤3/4 → ∀w:ImprovedWindow line naturalκ,
      ∀(a ε T allowance ν C height q:ℝ) (i:ℕ),
      1<U → 51/100<a → 2*a-1≤3/4 → 0≤ε → ε≤1/10000000 →
      0<ν → ν≤1/10000000 → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      w.Available (2*a-1) (q/(2*a-1)) →
      ∀{Label Slot:Type} [Fintype Label]
      (B:Batch M H Label Slot U a ε (w.cutoff (2*a-1) (q/(2*a-1))) T allowance i),
      (∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u:FreeRow=>u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀bin j J K,∀hne:(B.fiberRows bin j J K).Nonempty,
        Cycle25DetectorRawFiber.Moments (B.fiber bin j J K hne) naturalκ c κ C height εm) →
      (∀bin j J K,∀hne:(B.fiberRows bin j J K).Nonempty,
        AffineMarkedMoment (B.fiber bin j J K hne) w.face C height εm) →
      (∀bin j J K,∀hne:(B.fiberRows bin j J K).Nonempty,
        ImprovedMoments line (B.fiber bin j J K hne) ν C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2*fiberConstant C height K₀*
        (Fintype.card B.Bin:ℝ)*U^(w.value (2*a-1) (q/(2*a-1))+159*ε+εm+B.mesh+7*ν)) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ := count_fiber_at_windows (line := line)
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hcount] with U hcount
  constructor
  · intro naturalκ hk hk1 w a ε T allowance ν C height q i hU ha hd hε hεhi hν hνhi hC hh hf hAvail
      Label Slot _ B hq moments affine
    have hb := B.card_bound (fiberConstant C height K₀)
      (fun _=>w.value (2*a-1) (q/(2*a-1))+159*ε+εm+B.mesh+7*ν)
      (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU) (by
        intro bin j J K hne
        have hc' := hcount.1 naturalκ hk hk1 w a ε _ T allowance ν C height i
          hU ha hd hε hεhi hν hνhi hC hh hf (B.fiber bin j J K hne)
        rw [fiber_mean_eq B q hq bin j J K hne] at hc'
        exact hc' hAvail rfl (moments bin j J K hne) (affine bin j J K hne))
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hb
  · intro naturalκ hk hk1 w a ε T allowance ν C height q i hU ha hd hε hεhi hν hνhi hC hh hf hAvail
      Label Slot _ B hq moments affine imp
    have hb := B.card_bound (fiberConstant C height K₀)
      (fun _=>w.value (2*a-1) (q/(2*a-1))+159*ε+εm+B.mesh+7*ν)
      (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU) (by
        intro bin j J K hne
        have hc' := hcount.2 naturalκ hk hk1 w a ε _ T allowance ν C height i
          hU ha hd hε hεhi hν hνhi hC hh hf (B.fiber bin j J K hne)
        rw [fiber_mean_eq B q hq bin j J K hne] at hc'
        exact hc' hAvail rfl (moments bin j J K hne) (affine bin j J K hne) (imp bin j J K hne))
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hb

namespace ImprovedCount
variable [scheme:ImprovedCountScheme line]

/-- The count at the extended (envelope (line := line)) for any attaining choice. -/
theorem fixed_amplitude_envelope_count
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃ co κo Ko ca κa Ka : ℝ,
      0<co ∧ co≤1 ∧ 0<κo ∧ 0≤Ko ∧ 0<ca ∧ ca≤1 ∧ 0<κa ∧ 0≤Ka ∧
      ∀ᶠ U : ℝ in atTop,
      ∀ (κplain a ε T allowance ν C height q : ℝ) (i : ℕ),
      1<U → 51/100<a → 2*a-1≤3/4 → 0≤ε → ε≤1/10000000 →
      7/10≤κplain → κplain≤3/4 → 0<ν → ν≤1/10000000 → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      ∀ choice : (Choice (line := line)), choice.Available (2*a-1) (q/(2*a-1)) →
      choice.value κplain (2*a-1) (q/(2*a-1))=(envelope (line := line)) κplain (2*a-1) (q/(2*a-1)) →
      ∀ {Label Slot : Type} [Fintype Label]
        (B : Batch M H Label Slot U a ε (choice.cutoff κplain (2*a-1) (q/(2*a-1))) T allowance i),
      B.rows.Nonempty →
      (∀ u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
        Cycle25DetectorRawFiber.Moments (B.fiber bin label left right hne) κplain co κo C height εm) →
      (∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
        Cycle25DetectorRawFiber.Moments (B.fiber bin label left right hne) scheme.naturalκ ca κa C height εm) →
      (∀ w∈scheme.windows, ∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
        AffineMarkedMoment (B.fiber bin label left right hne) w.face C height εm) →
      (∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
        ImprovedMoments line (B.fiber bin label left right hne) ν C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2*
        max (fiberConstant C height Ko) (fiberConstant C height Ka)*(Fintype.card B.Bin:ℝ)*
        U^((envelope (line := line)) κplain (2*a-1) (q/(2*a-1))+159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨co,κo,Ko,hco,hco1,hκo,hKo,hold⟩ :=
    Cycle25ProbeHighRowFamily.balanced_adaptive_count_from_raw_moments
      M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  obtain ⟨ca,κa,Ka,hca,hca1,hκa,hKa,hnew⟩ := fixed_amplitude_windows_count (line := line)
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨co,κo,Ko,ca,κa,Ka,hco,hco1,hκo,hKo,hca,hca1,hκa,hKa,?_⟩
  filter_upwards [hold,hnew] with U hold hnew
  intro κplain a ε T allowance ν C height q i hU ha hd hε hεsmall hk hkhi hν hνhi hC hh hf
    choice hAvail hvalue Label Slot _ B hne hq oldmom newmom rawmom impmom
  have promote (K R : ℝ)
      (hK : fiberConstant C height K≤max (fiberConstant C height Ko) (fiberConstant C height Ka))
      (hR : R=(envelope (line := line)) κplain (2*a-1) (q/(2*a-1)))
      (hc : (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2*
        fiberConstant C height K*(Fintype.card B.Bin:ℝ)*U^(R+159*ε+εm+B.mesh+7*ν)) :
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2*
        max (fiberConstant C height Ko) (fiberConstant C height Ka)*(Fintype.card B.Bin:ℝ)*
        U^((envelope (line := line)) κplain (2*a-1) (q/(2*a-1))+159*ε+εm+B.mesh+7*ν) := by
    rw [hR] at hc
    apply hc.trans
    have h1 := mul_le_mul_of_nonneg_left hK
      (show 0≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2 by positivity)
    have h2 := mul_le_mul_of_nonneg_right h1 (show 0≤(Fintype.card B.Bin:ℝ) by positivity)
    exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (zero_lt_one.trans hU).le _)
  cases choice with
  | old =>
    have hb := hold a ε T allowance κplain ν C height q i hU ha hd hε
      (by linarith) hk hkhi hν hC hh hf B hne hq oldmom
    rw [← QRH.Record12518109Return.countingR_eq_actual hk] at hb
    exact promote Ko _ (le_max_left _ _) hvalue hb
  | affine w =>
    have hb := hnew.1 scheme.naturalκ scheme.natural_lo scheme.natural_hi w a ε T allowance ν C
      height q i hU ha hd hε hεsmall hν hνhi hC hh hf hAvail.2 B hq newmom (rawmom w hAvail.1)
    exact promote Ka _ (le_max_right _ _) hvalue hb
  | improved w =>
    obtain ⟨v,hv,hface⟩ := scheme.improved_face w hAvail.1
    have haff : ∀ bin j J K, ∀ hne : (B.fiberRows bin j J K).Nonempty,
        AffineMarkedMoment (B.fiber bin j J K hne) w.face C height εm := by
      intro bin j J K hne
      rw [← hface]
      exact rawmom v hv bin j J K hne
    have hb := hnew.2 scheme.naturalκ scheme.natural_lo scheme.natural_hi w a ε T allowance ν C
      height q i hU ha hd hε hεsmall hν hνhi hC hh hf hAvail.2 B hq newmom haff impmom
    exact promote Ka _ (le_max_right _ _) hvalue hb

/-- **Selected envelope count** (`fixed_amplitude_selected_envelope_count` for the extended
envelope): the cutoff is the selected choice's; the only new input is `ImprovedMoments`. -/
theorem fixed_amplitude_selected_envelope_count
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃ co κo Ko ca κa Ka : ℝ,
      0<co ∧ co≤1 ∧ 0<κo ∧ 0≤Ko ∧ 0<ca ∧ ca≤1 ∧ 0<κa ∧ 0≤Ka ∧
      ∀ᶠ U : ℝ in atTop,
      ∀ (κplain a ε T allowance ν C height q : ℝ) (i : ℕ),
      1<U → 51/100<a → 2*a-1≤3/4 → 0≤ε → ε≤1/10000000 →
      7/10≤κplain → κplain≤3/4 → 0<ν → ν≤1/10000000 → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      ∀ {Label Slot : Type} [Fintype Label]
        (B : Batch M H Label Slot U a ε (selectedCutoff (line := line) κplain (2*a-1) (q/(2*a-1))) T allowance i),
      B.rows.Nonempty →
      (∀ u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
        Cycle25DetectorRawFiber.Moments (B.fiber bin label left right hne) κplain co κo C height εm) →
      (∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
        Cycle25DetectorRawFiber.Moments (B.fiber bin label left right hne) scheme.naturalκ ca κa C height εm) →
      (∀ w∈scheme.windows, ∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
        AffineMarkedMoment (B.fiber bin label left right hne) w.face C height εm) →
      (∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
        ImprovedMoments line (B.fiber bin label left right hne) ν C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2*
        max (fiberConstant C height Ko) (fiberConstant C height Ka)*(Fintype.card B.Bin:ℝ)*
        U^((envelope (line := line)) κplain (2*a-1) (q/(2*a-1))+159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨co,κo,Ko,ca,κa,Ka,hco,hco1,hκo,hKo,hca,hca1,hκa,hKa,hcount⟩ :=
    fixed_amplitude_envelope_count (line := line) M H hH S φ hφ hφc hφp hφ0 hφne
      a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨co,κo,Ko,ca,κa,Ka,hco,hco1,hκo,hKo,hca,hca1,hκa,hKa,?_⟩
  filter_upwards [hcount] with U hcount
  intro κplain a ε T allowance ν C height q i hU ha hd hε hεsmall hk hkhi hν hνhi hC hh hf
    Label Slot _ B hne hq oldmom newmom rawmom impmom
  exact hcount κplain a ε T allowance ν C height q i hU ha hd hε hεsmall hk hkhi
    hν hνhi hC hh hf ((selectedChoice (line := line)) κplain (2*a-1) (q/(2*a-1)))
    ((selectedChoice_available (line := line)) _ _ _) ((selectedChoice_value (line := line)) _ _ _) B hne hq oldmom newmom rawmom impmom

end ImprovedCount
end
end Qrh.TwoSlot.AnchorZeroLoss.Affine.Return
#print axioms Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCount.fixed_amplitude_selected_envelope_count
