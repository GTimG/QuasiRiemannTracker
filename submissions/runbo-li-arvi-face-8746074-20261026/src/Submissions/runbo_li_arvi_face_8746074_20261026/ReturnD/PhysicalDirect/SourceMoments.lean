/- Repeated marks: fork of Collet's generic return module PhysicalDirect.SourceMoments (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Genuine retained source moments for both saved inverse amplifiers.
Adapted Gao Target830 SourceMoments and original Cycle25 fields, Apache-2.0.
The only new analytic input is the literal RAW affine source transport. -/
import Submissions.runbo_li_arvi_face_8746074_20261026.ReturnD.Schedule
import Submissions.hailey_collet_1252270103.Record12518109Count.PhysicalDirect.InverseFields
import Submissions.runbo_li_arvi_face_8746074_20261026.ReturnD.PhysicalDirect.MomentGates
import Submissions.hailey_collet_1252270103.Record12518109Count.InitialTransport
import Mathlib.Order.Filter.Finite
import Mathlib.Data.List.Basic
import Submissions.hailey_collet_1252270103.Cycle25.Energy.Endpoint
import Submissions.hailey_collet_1252270103.Cycle25.Assembly.Count.PlainInput
import Submissions.hailey_collet_1252270103.Cycle25.Assembly.Count.ActualMoments
import Submissions.hailey_collet_1252270103.Cycle25.Assembly.Count.MomentDetectorPlainUnmarkedRestrictedField
set_option autoImplicit false
open QRH.Record1252270103Return

namespace QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [Geometry.BoundsR] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
noncomputable section
set_option maxHeartbeats 200000
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths
open QRH.Record12518109Count
open QRH.Record1252270103Return.GenericCount
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorBatch
open CenteredMomentEnergyBands ProbeHighRowFamily ProbeFinalAssembly
open Cycle25ProbeFinalAssembly Cycle25ProbeDetectorPlainMarkedFineField Cycle25ProbeDetectorPlainUnmarkedField
open CenteredMomentNaturalFixedRaySource Cycle25CenteredMomentNaturalFixedRaySource
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open QRH.Record1252270103Return.GenericPhysical (baselineSource)

theorem source_moments_from_initial_fields (D : BaselineData) (F : BaselineSourceData D)
    (counts : CountParameters F.modulus ⊤ D.t)
    (fineMesh : ℝ) (hmesh : 0<fineMesh) (hfine : ∀j,D.length j≤fineMesh/200)
    (hpositive : weighted_PositiveFineSourceInput F D.momentKappa fineMesh)
    (hpositive0 : weighted_PositiveFineSourceInput F scheme.naturalκ fineMesh)
    (hzero : ∃degree : ℕ, ∃control : Finset (ℕ×ℕ), ∀η₀ : Character, ∃A : ℝ, 0<A ∧ ∀ᶠU : ℝ in atTop,
      ZeroAt (internalQ (weighted_sourceFixedIdeal F) η₀) (1/4) (9/4) weighted_radialSupportUpper
        0 1 2 (D.t/4) U degree control A)
    (haffine : ∀w∈scheme.windows, WeightedAffineFineInput F w.face) :
    ∀η : Character, ∃J : ℝ, 0≤J ∧ ∃C : ℝ, 0<C ∧
      ∀τ : ℝ, 0<τ → τ≤1 → ∀ᶠZ : ℝ in atTop,
        SourceMomentBound D (baselineSource D F) counts η Z τ
          (C*(1+Z^(2*τ))^J) (Z^(2*τ)) := by
  obtain ⟨Ji,hi⟩ := QRH.Record12518109Count.PhysicalDirect.InverseFields.weighted_source_batch_inverse_fields F.modulus ⊤ le_top F
    counts.co counts.κo counts.co_pos counts.κo_pos
  obtain ⟨Ja,ha⟩ := QRH.Record12518109Count.PhysicalDirect.InverseFields.weighted_source_batch_inverse_fields F.modulus ⊤ le_top F
    counts.ca counts.κa counts.ca_pos counts.κa_pos
  obtain ⟨Jm,hm⟩ := weighted_source_batch_plain_marked_fine F D.momentKappa fineMesh hmesh hfine hpositive
  obtain ⟨Jm0,hm0⟩ := weighted_source_batch_plain_marked_fine F scheme.naturalκ fineMesh hmesh hfine hpositive0
  obtain ⟨Ju,hu⟩ := Cycle25ProbeDetectorPlainUnmarkedRestrictedField.weighted_source_batch_plain_unmarked
    D.toMomentData F hzero
  intro η
  obtain ⟨Ci,hCi,hi⟩ := hi η
  obtain ⟨Ca,hCa,ha⟩ := ha η
  obtain ⟨Cm,hCm,hm⟩ := hm η
  obtain ⟨Cm0,hCm0,hm0⟩ := hm0 η
  obtain ⟨Cu,hCu,hu⟩ := hu η
  choose Jr Cr hCr hr using
    (fun j : Fin scheme.windows.length => haffine (scheme.windows.get j) (List.get_mem _ j) η)
  let Jsum : ℕ := Ji+Ja+Jm+Jm0+Ju+∑j,Jr j
  let Csum : ℝ := Ci+Ca+Cm+Cm0+Cu+1+∑j,Cr j
  have hCrSum : 0 ≤ ∑j,Cr j := Finset.sum_nonneg (fun j _=>(hCr j).le)
  have hCsum : 0<Csum := by dsimp [Csum];linarith
  have hCr_le (j : Fin scheme.windows.length) : Cr j ≤ Csum := by
    have hs := Finset.single_le_sum (fun k _=>(hCr k).le) (Finset.mem_univ j)
    dsimp [Csum];linarith
  have hJr_le (j : Fin scheme.windows.length) : Jr j ≤ Jsum := by
    have hs := Finset.single_le_sum (fun k _=>Nat.zero_le (Jr k)) (Finset.mem_univ j)
    dsimp [Jsum];omega
  have hrAll := Filter.eventually_all.mpr hr
  refine ⟨(Jsum:ℕ),by positivity,Csum,hCsum,?_⟩
  intro τ hτ hτhi
  filter_upwards [hi,ha,hm,hm0,hu,hrAll] with Z hi ha hm hm0 hu hr
  have hZ : 0<Z := zero_lt_one.trans hi.1
  let height : ℝ := Z^(2*τ)
  have hh : 0≤height := Real.rpow_nonneg hZ.le _
  have hbase : 1≤1+height := by linarith
  have promote (K : ℝ) (j : ℕ) (hK : K≤Csum) (hj : j≤Jsum) :
      K*(1+height)^j≤Csum*(1+height)^Jsum :=
    mul_le_mul hK (pow_le_pow_right₀ hbase hj) (by positivity) hCsum.le
  have hCi' := promote Ci Ji (by dsimp [Csum]; linarith) (by dsimp [Jsum]; omega)
  have hCa' := promote Ca Ja (by dsimp [Csum]; linarith) (by dsimp [Jsum]; omega)
  have hCm' := promote Cm Jm (by dsimp [Csum]; linarith) (by dsimp [Jsum]; omega)
  have hCm0' := promote Cm0 Jm0 (by dsimp [Csum]; linarith) (by dsimp [Jsum]; omega)
  have hCu' := promote Cu Ju (by dsimp [Csum]; linarith) (by dsimp [Jsum]; omega)
  have hCr' (j : Fin scheme.windows.length) := promote (Cr j) (Jr j) (hCr_le j) (hJr_le j)
  simp only [Real.rpow_natCast]
  intro rows d a hd hdmax ha' hamax hrows i z hz hzim q B hB hdata hreverse hslots hwidth
    hprofile hupper hexternal hslotMesh hbinWidth hfamily bin label left right hne
  have hrows' : ∀u∈rows,Z^(1/100:ℝ)≤rowNorm u := fun u hu=>(hrows u hu).2.1
  have hext : ∀s,(B.external s).re=17/50 := by intro s;rw [hexternal];exact hz
  have hheight : ∀s,|(B.external s).im|≤height := by intro s;rw [hexternal];exact hzim
  have hinv := hi.2 d hd a D.ε _ _ _ i B hdata hprofile hupper hwidth hext
    bin label left right hne height hh
  have hinvA := ha.2 d hd a D.ε _ _ _ i B hdata hprofile hupper hwidth hext
    bin label left right hne height hh
  have hmarked := hm.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    (fun s=>by rw [hupper]) hext bin label left right hne height hh hheight
  have hmarked0 := hm0.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    (fun s=>by rw [hupper]) hext bin label left right hne height hh hheight
  have hunmarked := hu.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    bin label left right hne height hh
  have hU : 0≤Z^d := Real.rpow_nonneg hZ.le _
  refine ⟨?_,?_,?_⟩
  · apply Cycle25DetectorRawFiber.Moments.of_fields (B.fiber bin label left right hne) D.momentKappa_hi
    · constructor
      · intro n hn σ hσ t ht
        exact ⟨rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).1 hCi',
          rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).2 hCi'⟩
      · intro selected hselected hfirst hsecond n hn σ hσ t ht
        exact (hinv.2 selected hselected hfirst hsecond n hn σ hσ t ht).trans
          (mul_le_mul_of_nonneg_right hCi' (Real.rpow_nonneg hU _))
      · intro j k hjk σ hσ t ht
        exact (hunmarked j k hjk σ hσ t ht).1.trans
          (mul_le_mul_of_nonneg_right hCu' (Real.rpow_nonneg hU _))
    · intro selected hselected hcap j k hjk σ hσ t ht
      exact (hmarked selected hselected hcap j k hjk σ hσ t ht).trans
        (mul_le_mul_of_nonneg_right hCm' (Real.rpow_nonneg hU _))
  · apply Cycle25DetectorRawFiber.Moments.of_fields (B.fiber bin label left right hne) scheme.natural_hi
    · constructor
      · intro n hn σ hσ t ht
        exact ⟨rawMoment_mono_constant (hinvA.1 n hn σ hσ t ht).1 hCa',
          rawMoment_mono_constant (hinvA.1 n hn σ hσ t ht).2 hCa'⟩
      · intro selected hselected hfirst hsecond n hn σ hσ t ht
        exact (hinvA.2 selected hselected hfirst hsecond n hn σ hσ t ht).trans
          (mul_le_mul_of_nonneg_right hCa' (Real.rpow_nonneg hU _))
      · intro j k hjk σ hσ t ht
        exact (hunmarked j k hjk σ hσ t ht).1.trans
          (mul_le_mul_of_nonneg_right hCu' (Real.rpow_nonneg hU _))
    · intro selected hselected hcap j k hjk σ hσ t ht
      exact (hmarked0 selected hselected hcap j k hjk σ hσ t ht).trans
        (mul_le_mul_of_nonneg_right hCm0' (Real.rpow_nonneg hU _))
  · intro w hw
    obtain ⟨wi,rfl⟩ := List.mem_iff_get.mp hw
    have hraw := (hr wi).2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
      (fun s=>by rw [hupper]) hext bin label left right hne height hh hheight
    intro hmlo hmhi selected hsel h1 h2 h3 j k hjk σ hσ t ht
    exact (hraw hmlo hmhi selected hsel h1 h2 h3 j k hjk σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right (hCr' wi) (Real.rpow_nonneg hU _))

theorem actual_source_moments (D : BaselineData) (F : BaselineSourceData D)
    (counts : CountParameters F.modulus ⊤ D.t)
    (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤D.momentKappa)
    (hκ0beta : 2*HeckeZeroSupremum.beta-1≤scheme.naturalκ)
    (hfine : ∀j,D.length j≤Cycle25.sourceMesh D.t/200)
    (haffine : ∀w∈scheme.windows, WeightedAffineFineInput F w.face) :
    ∀η : Character, ∃J : ℝ, 0≤J ∧ ∃C : ℝ, 0<C ∧
      ∀τ : ℝ, 0<τ → τ≤1 → ∀ᶠZ : ℝ in atTop,
        SourceMomentBound D (baselineSource D F) counts η Z τ
          (C*(1+Z^(2*τ))^J) (Z^(2*τ)) :=
  source_moments_from_initial_fields D F counts (Cycle25.sourceMesh D.t)
    (Cycle25.sourceMesh_pos D.t_pos) hfine
    (terminal_plain_input F D.momentKappa D.momentKappa_lo D.momentKappa_hi hbeta hκbeta)
    (terminal_plain_input F scheme.naturalκ scheme.natural_lo scheme.natural_hi hbeta hκ0beta)
    (terminal_zero_input F D.momentKappa D.momentKappa_lo D.momentKappa_hi hbeta hκbeta) haffine
end
end QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect
