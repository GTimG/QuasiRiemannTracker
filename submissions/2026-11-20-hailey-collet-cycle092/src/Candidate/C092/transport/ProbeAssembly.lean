/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The literal probe, numerator and Euler correction are inherited from the
credited OpenAI / Collet / Levy / Gao development and Joseph Bebel's positive
transport fork. The final continuation is the original Cycle25 continuation. -/
import Candidate.C092.UpstreamPrivate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.Transport.FinalSourceProbe
import Candidate.C092.UpstreamPrivate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.Transport.Transport.HighApproximation
import Candidate.C092.Intake.QRH.Target

/-!
An interface for the *actual* finite numerator and masked Hecke signal, without
an instance of the historical conductor/cap bounds. Transport and finite-sum
estimates remain explicit inputs. Their positive savings may differ: the common
saving is their minimum, fixed before the live character. Thus this assembly
also applies at the Q conductor .817584..., once those inputs are constructed.

No physical source, count moment, selected-row estimate or numerator estimate
is asserted to exist here. In particular `ActualFiniteInput` is open for Q.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open Filter Asymptotics
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open OAI.SevenEighths.ProbePhysical OAI.SevenEighths.PrincipalSignalComparison
open OAI.SevenEighths.BoundaryDensitySplitReturn.TransportHighTransport
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.FinalAssembly

namespace QRH.Cycle092.ProbeAssembly

/-- An auxiliary geometry used only to reuse the Euler-product theorem. The
Euler correction and its half-plane depend on theta, not on the conductor,
lengths or cap. This is not a replacement for Q's physical geometry. -/
@[instance_reducible] private def correctionParameters : Geometry.Parameters where
  theta := QRH.Cycle090.theta
  ell := 11/3 - 4*QRH.Cycle090.theta
  x := 1 + (11/3 - 4*QRH.Cycle090.theta) - 163/200
  y := 163/200 - 2*(11/3 - 4*QRH.Cycle090.theta)
  ell_pos := by norm_num [QRH.Cycle090.theta]
  sixth_lt_ell := by norm_num [QRH.Cycle090.theta]
  ell_lt_fifth := by norm_num [QRH.Cycle090.theta]
  ell_lt_x := by norm_num [QRH.Cycle090.theta]
  x_lt_y := by norm_num [QRH.Cycle090.theta]
  y_lt_half := by norm_num [QRH.Cycle090.theta]
  x_add_y := by norm_num [QRH.Cycle090.theta]
  dilation_gap := by norm_num [QRH.Cycle090.theta]
  tuple_margin_neg := by norm_num [QRH.Cycle090.theta]
  signal_boundary := by norm_num [QRH.Cycle090.theta]

private theorem correctionBounds :
    @Qrh.JointDetector.BoundaryPhysical.Return.Geometry.CoreBounds correctionParameters := by
  refine @Qrh.JointDetector.BoundaryPhysical.Return.Geometry.CoreBounds.mk
    correctionParameters ?_ ?_ ?_ ?_ ?_
  · change (873/1000 : ℝ) < QRH.Cycle090.theta ∧ QRH.Cycle090.theta < 7/8
    norm_num [QRH.Cycle090.theta]
  · change (793/1000 : ℝ) < 1+(11/3-4*QRH.Cycle090.theta)-(1+(11/3-4*QRH.Cycle090.theta)-163/200) ∧
      1+(11/3-4*QRH.Cycle090.theta)-(1+(11/3-4*QRH.Cycle090.theta)-163/200) < 816/1000
    norm_num [QRH.Cycle090.theta]
  · change (458/1000 : ℝ) < 163/200 - 2*(11/3 - 4*QRH.Cycle090.theta) ∧
      163/200 - 2*(11/3 - 4*QRH.Cycle090.theta) < 473/1000
    norm_num [QRH.Cycle090.theta]
  · change (1672/10000 : ℝ) < 11/3 - 4*QRH.Cycle090.theta ∧
      11/3 - 4*QRH.Cycle090.theta < 175/1000
    norm_num [QRH.Cycle090.theta]
  · change (7/100 : ℝ) < (163/200 - 2*(11/3 - 4*QRH.Cycle090.theta))/2 -
      (1+(11/3-4*QRH.Cycle090.theta)-(1+(11/3-4*QRH.Cycle090.theta)-163/200))*(17/50 - 1/6) - 1/50
    norm_num [QRH.Cycle090.theta]

/-- Genuine analytic continuation and the half-bound for the *same* source
correction at the exact Q boundary. No physical conductor premise is used. -/
theorem actual_correction_at_Q (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) :
    AnalyticOnNhd ℂ (sourceCorrection η S) {s : ℂ | QRH.Cycle090.theta < s.re} ∧
    ∀ s : ℂ, QRH.Cycle090.theta < s.re → ‖sourceCorrection η S s - 1‖ ≤ 1/2 := by
  have h := @Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Transport.actual_source_analytic
    correctionParameters correctionBounds S hS η
  exact h.2

variable [Geometry.Parameters]

abbrev shift : ℝ :=
  Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly.signalShift

/-- The authentic finite nonfloor cube, including the real source weights. -/
def numerator (D : BaselineData) (F : BaselineSourceData D)
    (padding tau : ℝ) (η : Character) (Z : ℝ)
    (idx grid : HeckeInverseAmplification.FreeRow → ℕ) : ℂ :=
  finiteNonfloorNumerator F.modulus ⊤ F.S F.exclusions F.maximal D.length
    1 2 padding D.e tau (fun _ => F.w) F.W F.W η Z idx grid

/-- The exact normalizer accompanying that finite numerator. -/
def normalizer (D : BaselineData) (F : BaselineSourceData D) (Z : ℝ) : ℂ :=
  letI : NeZero (∏ P ∈ F.S, P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  actualNormalizer F.modulus ⊤ F.S D.length 1 2 (fun _ => F.w) F.W F.W Z

def selected (D : BaselineData) (F : BaselineSourceData D)
    (padding tau : ℝ) (n : ℕ) (η : Character) (Z : ℝ)
    (idx grid : HeckeInverseAmplification.FreeRow → ℕ) : Prop :=
  ActualBufferedSelection F.modulus ⊤ le_top F.S F.exclusions F.maximal
    η padding D.e tau n Z idx grid

/-- The actual signal uses the finite-prime-deleted character and the original
Euler correction, rather than a substitute signal or an assumed L-function. -/
def residual (D : BaselineData) (F : BaselineSourceData D) (η : Character)
    (Z : ℝ) : ℂ :=
  sourceProbe D F η Z - HeckeSignal.signal
    (η.excludePrimes F.S F.exclusions.prime) (sourceCorrection η F.S) shift Z

/-- The authentic low probe estimate needs only the actual parameter record.
We reprove its signal-shift identification algebraically, avoiding the unused
historical coarse-bounds instance retained by the old adapter theorem. -/
theorem actual_low (D : BaselineData) (F : BaselineSourceData D)
    (loss : ℝ) (hloss : 0 < loss) (η : Character) :
    sourceProbe D F η =O[atTop] (fun Z : ℝ => Z ^ (Geometry.theta + shift + loss)) := by
  have hh := Record1252270103Low.normalizedProbe_low F.modulus ⊤ le_top F.S F.exclusions F.maximal
    1 2 1 loss (by norm_num) (by norm_num) hloss D.length D.slots_pos
    D.slots_injective D.slots_sum
    (fun _ => F.w) (fun _ => F.smooth) (fun _ => F.compact) (fun _ => F.support)
    (fun _ => F.bounded) (fun _ => F.nonzero) F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
    F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative
    F.complex_nonzero F.complex_nonzero η
  have hshift : Geometry.signalShift = shift := by
    dsimp [Geometry.signalShift, shift,
      Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly.signalShift,
      Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Assembly.signalShift]
    change -(4 + Geometry.y - Geometry.x)/6 = -(5/6 - Geometry.x/3 - Geometry.ell/6)
    linarith [Geometry.x_add_y]
  simpa only [sourceProbe, Geometry.signal, hshift] using hh

/-- Buffered transport selects rows and compares the actual probe with their
literal finite numerator. This is an explicit analytic obligation. -/
def SelectedTransport (D : BaselineData) (F : BaselineSourceData D)
    (padding tau saving : ℝ) (n : ℕ) (η : Character) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
    normalizer D F Z ≠ 0 ∧ ∃ idx grid : HeckeInverseAmplification.FreeRow → ℕ,
      selected D F padding tau n η Z idx grid ∧
      ‖residual D F η Z - numerator D F padding tau η Z idx grid / normalizer D F Z‖ ≤
        C * Z ^ (HeckeZeroSupremum.beta + shift - saving)

/-- A bound on the finite numerator, uniform before the buffered selection. -/
def FiniteNumeratorBound (D : BaselineData) (F : BaselineSourceData D)
    (padding tau saving : ℝ) (n : ℕ) (η : Character) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
    ∀ idx grid : HeckeInverseAmplification.FreeRow → ℕ,
      selected D F padding tau n η Z idx grid →
      ‖numerator D F padding tau η Z idx grid‖ ≤
        C * ‖normalizer D F Z‖ * Z ^ (HeckeZeroSupremum.beta + shift - saving)

/-- The two independently proved savings give their positive common minimum.
There is no conductor bound, physical cap, floor estimate or count premise
inside this algebraic/analytic passage. -/
theorem actual_high_of_finite (D : BaselineData) (F : BaselineSourceData D)
    (padding tau transportSaving numeratorSaving : ℝ) (n : ℕ) (η : Character)
    (ht : SelectedTransport D F padding tau transportSaving n η)
    (hn : FiniteNumeratorBound D F padding tau numeratorSaving n η) :
    residual D F η =O[atTop] (fun Z : ℝ =>
      Z ^ (HeckeZeroSupremum.beta + shift - min transportSaving numeratorSaving)) := by
  obtain ⟨Ct, hCt, ht⟩ := ht
  obtain ⟨Cn, hCn, hn⟩ := hn
  apply Asymptotics.IsBigO.of_bound (Ct + Cn)
  filter_upwards [ht, hn, eventually_ge_atTop (1 : ℝ)] with Z ht hn hZ
  obtain ⟨hN, idx, grid, hsel, herr⟩ := ht
  have hraw := hn idx grid hsel
  let E := Z ^ (HeckeZeroSupremum.beta + shift - min transportSaving numeratorSaving)
  have het : Z ^ (HeckeZeroSupremum.beta + shift - transportSaving) ≤ E :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith [min_le_left transportSaving numeratorSaving])
  have hen : Z ^ (HeckeZeroSupremum.beta + shift - numeratorSaving) ≤ E :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith [min_le_right transportSaving numeratorSaving])
  have hnum : ‖numerator D F padding tau η Z idx grid / normalizer D F Z‖ ≤ Cn * E := by
    rw [norm_div]
    apply (div_le_iff₀ (norm_pos_iff.mpr hN)).mpr
    calc
      _ ≤ Cn * ‖normalizer D F Z‖ * E :=
        hraw.trans (mul_le_mul_of_nonneg_left hen (by positivity))
      _ = (Cn * E) * ‖normalizer D F Z‖ := by ring
  have hres : ‖residual D F η Z‖ ≤ (Ct + Cn) * E := by
    calc
      _ = ‖(residual D F η Z - numerator D F padding tau η Z idx grid / normalizer D F Z) +
          numerator D F padding tau η Z idx grid / normalizer D F Z‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ Ct * E + Cn * E := add_le_add
        (herr.trans (mul_le_mul_of_nonneg_left het hCt.le)) hnum
      _ = (Ct + Cn) * E := by ring
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ Z) _)] using hres

/-- The precise remaining interface. Source, padding and both positive savings
are chosen before the character; only height and finite buffer depend on it.
No instance of this finite transport/numerator input is constructed here. -/
def ActualFiniteInput : Prop :=
  Geometry.theta < HeckeZeroSupremum.beta →
    ∃ D : BaselineData, ∃ F : BaselineSourceData D,
    ∃ padding transportSaving numeratorSaving : ℝ,
      0 < padding ∧ 0 < transportSaving ∧ 0 < numeratorSaving ∧
      ∀ η : Character, ∃ tau : ℝ, 0 < tau ∧ ∃ n : ℕ, 0 < n ∧
        SelectedTransport D F padding tau transportSaving n η ∧
        FiniteNumeratorBound D F padding tau numeratorSaving n η

/-- The LOW estimate is the genuine physical probe theorem. The HIGH estimate
comes from the actual selected numerator above; the mask is an exact identity. -/
theorem common_probe_of_actual_finite
    (hboundary : Geometry.theta = QRH.Cycle090.theta) (hinput : ActualFiniteInput) :
    Cycle25.UniformCommonProbe Geometry.theta shift := by
  intro hgap
  obtain ⟨D, F, padding, st, sn, _hp, hst, hsn, hfinite⟩ := hinput hgap
  let omega := (HeckeZeroSupremum.beta - Geometry.theta) / 2
  have homega : 0 < omega := by dsimp [omega]; linarith
  refine ⟨omega, min st sn, homega, ?_, lt_min hst hsn, ?_⟩
  · dsimp [omega]; linarith
  · intro η _hprimitive
    have hcorrection := actual_correction_at_Q F.S F.exclusions η
    rw [← hboundary] at hcorrection
    obtain ⟨hH, hb⟩ := hcorrection
    obtain ⟨tau, _htau, n, _hn, ht, hn⟩ := hfinite η
    refine ⟨η.excludePrimes F.S F.exclusions.prime, sourceCorrection η F.S,
      sourceProbe D F η, excludePrimes_mask η F.S F.exclusions.prime, hH, hb, ?_, ?_⟩
    · exact actual_low D F omega homega η
    · exact actual_high_of_finite D F padding tau st sn n η ht hn

/-- Both exact targets follow from the displayed finite interface, at Q's
strict boundary and with the real principal-pole exception preserved. -/
theorem exact_targets_of_actual_finite
    (hboundary : Geometry.theta = QRH.Cycle090.theta)
    (hinput : ActualFiniteInput) :
    HeckeZeroSupremum.beta ≤ QRH.Cycle090.theta ∧
    (∀ (η : Character) (s : ℂ), QRH.Cycle090.theta < s.re →
      (s ≠ 1 ∨ η.residue ≠ 1) → LFunction η s ≠ 0) ∧
    QRH.Cycle090.OrdinaryTarget := by
  have hhalf : (1/2 : ℝ) ≤ Geometry.theta := by rw [hboundary]; norm_num [QRH.Cycle090.theta]
  have hupper : Geometry.theta ≤ (7/8 : ℝ) := by rw [hboundary]; norm_num [QRH.Cycle090.theta]
  have hcommon := common_probe_of_actual_finite hboundary hinput
  have hbeta := Cycle25.beta_le_of_common_probe hhalf hupper hcommon
  have hhecke : ∀ (η : Character) (s : ℂ), Geometry.theta < s.re →
      (s ≠ 1 ∨ η.residue ≠ 1) → LFunction η s ≠ 0 :=
    Cycle25.hecke_ne_zero_of_common_probe hhalf hupper hcommon
  refine ⟨by simpa only [hboundary] using hbeta, ?_, ?_⟩
  · simpa only [hboundary] using hhecke
  · intro q _hq χ s hs hpole
    exact Cycle25.dirichlet_of_hecke (by linarith : 0 < Geometry.theta) hhecke χ s
      (by simpa only [hboundary] using hs) hpole

end QRH.Cycle092.ProbeAssembly

#print axioms QRH.Cycle092.ProbeAssembly.actual_low
#print axioms QRH.Cycle092.ProbeAssembly.actual_high_of_finite
#print axioms QRH.Cycle092.ProbeAssembly.actual_correction_at_Q
#print axioms QRH.Cycle092.ProbeAssembly.common_probe_of_actual_finite
#print axioms QRH.Cycle092.ProbeAssembly.exact_targets_of_actual_finite
