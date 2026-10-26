/- Repeated marks: fork of Collet's generic return module PhysicalDirect.SourceCountInitial (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The finite minimum chooses the cutoff before the Batch. Both inverse amplifier
parameter pairs are saved globally; the actual moment sums remain explicit. -/
import Submissions.runbo_li_arvi_face_8746074_20261026.ReturnD.Schedule
import Submissions.runbo_li_arvi_face_8746074_20261026.ReturnD.PhysicalDirect.CountParameters
import Submissions.hailey_collet_1252270103.Cycle25.Assembly.Count.SourceParametersCount
set_option autoImplicit false
open QRH.Record1252270103Return

namespace QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [Geometry.BoundsR] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open QRH.Record12518109Count
open QRH.Record1252270103Return.GenericCount
noncomputable section
set_option maxHeartbeats 200000
open scoped Classical BigOperators ContDiff
open Set Filter OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst Cycle25DetectorRowCount
open HeckeDetectorFixedAmplitudeCount

theorem selected_source_count
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (εm : ℝ)
    (counts : CountParameters M H εm)
    (Label : Type) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth : ℝ)
    (hdmin : 0<dmin) (hdmax : 0<dmax) (hτ : 0<τ)
    (hl : 0<logCost) (hh : τ<heightCost) (hb : 0<binWidth) :
    ∃ K : ℝ, 0<K ∧
      ∀ᶠ Z : ℝ in atTop,
      ∀ d : ℝ, dmin≤d → d≤dmax →
      ∀ (κplain a ε ν C q : ℝ) (i : ℕ), i≤n →
      51/100<a → 2*a-1≤3/4 → a≤1 → 0≤ε → ε≤1/10000000 →
      7/10≤κplain → κplain≤3/4 → 0<ν → ν≤1/10000000 → 0≤C →
      ∀ {Slot : Type}
        (B : Batch M H Label Slot (Z^d) a ε (GenericCount.selectedCutoff κplain (2*a-1) (q/(2*a-1))) (Z^τ) ((Z^d)^(τ/(2*dmax))) i),
      B.slots.card≤N → B.binWidth=binWidth →
      B.rows.Nonempty →
      (∀ u∈B.rows,rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external (Z^d)) u=q) →
      (∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
        Cycle25DetectorRawFiber.Moments (B.fiber bin label left right hne) κplain counts.co counts.κo (C*Z^momentCost) (Z^heightCost) εm) →
      (∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
        Cycle25DetectorRawFiber.Moments (B.fiber bin label left right hne) scheme.naturalκ counts.ca counts.κa (C*Z^momentCost) (Z^heightCost) εm) →
      (∀ w∈scheme.windows, ∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
        AffineMarkedMoment (B.fiber bin label left right hne) w.face (C*Z^momentCost) (Z^heightCost) εm) →
      (B.rows.card:ℝ) ≤ K*C*Z^(logCost+heightCost+momentCost)*
        (Z^d)^(GenericCount.envelope κplain (2*a-1) (q/(2*a-1))+159*ε+εm+B.mesh+7*ν) := by
  let Ko := counts.Ko
  let Ka := counts.Ka
  have hcount := counts.counted
  obtain ⟨Ko',hKo',ho⟩ := ProbeHighRowFamily.source_count_prefactor_eventually (Label:=Label)
    N dmin dmax logCost heightCost momentCost binWidth Ko hdmin hdmax hl (by linarith) hb
  obtain ⟨Ka',hKa',haff⟩ := ProbeHighRowFamily.source_count_prefactor_eventually (Label:=Label)
    N dmin dmax logCost heightCost momentCost binWidth Ka hdmin hdmax hl (by linarith) hb
  refine ⟨Ko'+Ka',by positivity,?_⟩
  filter_upwards [ProbeHighRowFamily.eventually_all_rpow_ge hcount dmin hdmin,ho,haff,
    ProbeHighRowFamily.source_count_frequency_eventually n dmax τ heightCost hdmax hτ hh,
    ProbeHighRowFamily.eventually_all_rpow_ge (eventually_gt_atTop (1:ℝ)) dmin hdmin,
    eventually_ge_atTop (1:ℝ)] with Z hcount ho haff hfreq hU hZ
  intro d hd hd' κplain a ε ν C q i hi ha haδ ha' hε hεsmall hk hkhi hν hνhi hC
    Slot B hslots hbin hne hq oldmom newmom rawmom
  have hc := hcount d hd κplain a ε (Z^τ) ((Z^d)^(τ/(2*dmax))) ν
    (C*Z^momentCost) (Z^heightCost) q i (hU d hd) ha haδ hε hεsmall hk hkhi
    hν hνhi (by positivity) (by positivity) (hfreq d hd' i hi) B hne hq oldmom newmom rawmom
  have hpref : (Fintype.card Label:ℝ)*(dyadicLength (Z^d):ℝ)^2*
      max (fiberConstant (C*Z^momentCost) (Z^heightCost) Ko)
        (fiberConstant (C*Z^momentCost) (Z^heightCost) Ka)*(Fintype.card B.Bin:ℝ) ≤
      (Ko'+Ka')*C*Z^(logCost+heightCost+momentCost) := by
    have ho' := ho d hd hd' C a ε _ _ _ i hC ha' B hslots hbin
    have haff' := haff d hd hd' C a ε _ _ _ i hC ha' B hslots hbin
    rcases le_total (fiberConstant (C*Z^momentCost) (Z^heightCost) Ko)
        (fiberConstant (C*Z^momentCost) (Z^heightCost) Ka) with hx | hx
    · rw [max_eq_right hx]
      apply haff'.trans
      gcongr
      linarith
    · rw [max_eq_left hx]
      apply ho'.trans
      gcongr
      linarith
  exact hc.trans (mul_le_mul_of_nonneg_right hpref (Real.rpow_nonneg (by positivity) _))
end
end QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect
