/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Parameterized source-to-detector bridge, adapted from Sil's PR137 bridge
(copyright (c) 2026 Sil, Apache-2.0). The coefficient, profile, zero-mask and
common early-mesh arguments are retained; only the affine line is generalized. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.AffineFiber
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Interface.Bridge

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorZeroLoss.Affine
noncomputable section
open scoped Classical BigOperators ComplexConjugate ContDiff
open Filter Set OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorCoefficientTransfer DetectorDictionaryInverseRawInitialGates ProbeHighRowFamily
open Qrh.MarkedAnchor.Interface (anchorLeft anchorTop)
open Qrh.MarkedAnchor.Interface.Bridge
local notation "O" => HeckeFamily.O
local instance (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (line : Line)

/-- The same open-rectangle slack comparison for any nonnegative slope at most
one half. Its numerical cost is independent of the line intercept. -/
theorem slot_slack {ε δ r w : ℝ} (hδε : δ ≤ ε/4)
    (hw : w ≤ r+2*δ) (hrw : r+δ ≤ w) :
    markCap line r-ε ≤ (1-w)/2+(line.g0-line.g1*w)-δ := by
  unfold markCap
  have hδ : 0 ≤ δ := by linarith
  have hmul := mul_le_mul_of_nonneg_left (show w-r ≤ 2*δ by linarith) line.slope_nonneg
  have hbound := mul_le_mul_of_nonneg_right line.slope_le (show 0 ≤ 2*δ by positivity)
  nlinarith

theorem fiber_of_improved {hi : ℝ} (hhi : anchorTop < hi)
    (h : Qrh.MarkedAnchor.Interface.Contract.ImprovedMoments anchorLeft hi line.g0 line.g1) : ImprovedFiberMoments line := by
  intro ε hε
  have hδ : 0 < stepδ ε hi :=
    lt_min (by linarith) (lt_min (by linarith) (by norm_num))
  have hδε : stepδ ε hi ≤ ε/4 := min_le_left _ _
  have hδhi : stepδ ε hi ≤ (hi - anchorTop)/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ10 : stepδ ε hi ≤ 1/10 := (min_le_right _ _).trans (min_le_right _ _)
  set δ := stepδ ε hi with hδdef
  let ρ : Fin (gridN δ + 1) → Qrh.MarkedAnchor.Interface.Contract.AnchorRect := fun k =>
    Qrh.MarkedAnchor.Interface.Contract.anchorRect (gridPt δ k) (line.g0 - line.g1*gridPt δ k) δ
  have hsrc (k : Fin (gridN δ + 1)) :
      Qrh.MarkedAnchor.Interface.Contract.UniformInverseRectSource Qrh.MarkedAnchor.Interface.Contract.canonicalFamily (ρ k) ∧
        Qrh.MarkedAnchor.Interface.Contract.OrdinaryRectSource (ρ k) :=
    h.rect (grid_range hδ k).1 (by linarith [(grid_range hδ k).2]) hδ
  have hP (k : Fin (gridN δ + 1)) : 1/2 ≤ (ρ k).Pmax := by
    show 1/2 ≤ gridPt δ k - δ
    have := (grid_range hδ k).1
    norm_num [anchorLeft] at this
    linarith
  choose meshI hmeshI hI using fun k => (hsrc k).1 ε hε
  choose meshO hmeshO hO using fun k =>
    Qrh.MarkedAnchor.Interface.FiberBridge.OrdinaryRectSource.affine_input (hsrc k).2 (hP k) ε hε
  let mesh : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun k => min (meshI k) (meshO k))
  have hmeshpos : 0 < mesh :=
    (Finset.lt_inf'_iff _).2 (fun k _ => lt_min (hmeshI k) (hmeshO k))
  have hmI (k : Fin (gridN δ + 1)) : mesh ≤ meshI k :=
    (Finset.inf'_le _ (Finset.mem_univ k)).trans (min_le_left _ _)
  have hmO (k : Fin (gridN δ + 1)) : mesh ≤ meshO k :=
    (Finset.inf'_le _ (Finset.mem_univ k)).trans (min_le_right _ _)
  refine ⟨mesh, hmeshpos, ?_⟩
  intro D S hDt hfine
  have hOrd (k : Fin (gridN δ + 1)) :
      QRH.Record12518109Count.WeightedAffineFineInput S (Qrh.MarkedAnchor.Interface.FiberBridge.countFace (ρ k)) :=
    hO k hDt (fun j => (hfine j).trans (by have := hmO k; linarith)) S
  have hsupp (b : Bool) : Function.support (orientedProfile b
      (DetectorDictionaryInverseClippedUniform.referenceWindow : ℝ → ℂ)) ⊆
      Icc (1/18 : ℝ) (13/4) := by
    intro x hx
    apply DetectorDictionaryInverseClippedUniform.referenceWindow_support
    apply subset_tsupport
    intro h0
    apply hx
    cases b <;> simp [orientedProfile, h0]
  have hsmooth (b : Bool) : ContDiff ℝ ∞ (orientedProfile b
      (DetectorDictionaryInverseClippedUniform.referenceWindow : ℝ → ℂ)) := by
    cases b
    · simpa only [orientedProfile, Bool.false_eq_true, ite_false] using
        DetectorDictionaryInverseClippedUniform.referenceWindow.smooth ⊤
    · simpa only [orientedProfile, ite_true] using
        HeckeInverseAmplification.conjugate_profile_smooth _
          (DetectorDictionaryInverseClippedUniform.referenceWindow.smooth ⊤)
  have hcf : Qrh.MarkedAnchor.Interface.Contract.canonicalFamily (Qrh.MarkedAnchor.Interface.Contract.canonicalSlotsRay (S.W : ℝ → ℂ) (33/50) S.modulus (Qrh.MarkedAnchor.Interface.Contract.SlotTwist.diag ⊤) le_top) :=
    ⟨S.W, S.W.smooth ⊤, S.complex_support, S.modulus, inferInstance, Qrh.MarkedAnchor.Interface.Contract.SlotTwist.diag ⊤, le_top, rfl⟩
  intro η
  let data := sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η
  -- the inverse degree depends on the row data; for one `η` only the finitely many
  -- data `data q.2` (labels) occur, so one degree `∑ q, deg q` serves all of them.
  choose deg Cl Z₀ hCl hZ₀ hb using
    fun q : (Fin (gridN δ + 1) × Bool) × Sum Bool (RayQuotient.Characters S.modulus ⊤) =>
      hI q.1.1 D.N _ hcf (orientedProfile q.1.2
        (DetectorDictionaryInverseClippedUniform.referenceWindow : ℝ → ℂ)) (1/18) (13/4)
        (by norm_num) (by norm_num) (hsupp q.1.2) (hsmooth q.1.2) (data q.2)
  have hdegle (q : (Fin (gridN δ + 1) × Bool) × Sum Bool (RayQuotient.Characters S.modulus ⊤)) :
      deg q ≤ ∑ q, deg q :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
  obtain ⟨Kf, Cf, hCf, hfib⟩ :=
    DetectorDictionaryInverseMarkedUniform.fiber_inverse_height_uniform (∑ q, deg q)
  choose Jo Co hCo hevo using fun k => hOrd k η
  have hCsum : 0 < 1 + ∑ q, Cl q := by
    have := Finset.sum_nonneg (fun q (_ : q ∈ Finset.univ) => (hCl q).le)
    linarith
  have hClle (q) : Cl q ≤ 1 + ∑ q, Cl q := by
    have := Finset.single_le_sum (fun q (_ : q ∈ Finset.univ) => (hCl q).le)
      (Finset.mem_univ q)
    linarith
  have hCo0 : 0 ≤ ∑ k, Co k := Finset.sum_nonneg (fun k _ => (hCo k).le)
  have hCfin : 0 < Cf*(1 + ∑ q, Cl q) + ∑ k, Co k := by positivity
  have hCole (k) : Co k ≤ Cf*(1 + ∑ q, Cl q) + ∑ k, Co k := by
    have := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => (hCo k).le)
      (Finset.mem_univ k)
    have := mul_pos hCf hCsum
    linarith
  -- the slot heights `|Im external| ≤ height` are paid by `(1+height)^(2 ∑ deg)`
  have hJole (k) : Jo k ≤ Kf + 2*(∑ q, deg q) + ∑ k, Jo k :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)).trans
      (Nat.le_add_left _ _)
  refine ⟨Kf + 2*(∑ q, deg q) + ∑ k, Jo k, Cf*(1 + ∑ q, Cl q) + ∑ k, Co k, hCfin, ?_⟩
  have hscale : ∀ᶠ Z : ℝ in atTop, ∀ q, ∀ d : ℝ, (1/200:ℝ) ≤ d → Z₀ q ≤ Z^d :=
    Filter.eventually_all.mpr (fun q =>
      HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) (Z₀ q) (by norm_num))
  filter_upwards [eventually_gt_atTop (1:ℝ), hscale,
    DetectorDictionaryInverseMarkedReference.deleted_large_eventually data D.ell
      (fun s => (D.slots_bounds s).1),
    Filter.eventually_all.mpr hevo] with Z hZ hscaleZ hlarge hord
  refine ⟨hZ, ?_⟩
  intro rows hrows d hd a tstar T allowance i B hB hdata hprof hwidth hupper hreal
    bin label left right hne height hheight hexternal
  have hdpos : 0 < d := by linarith
  have hU : 1 < Z^d := Real.one_lt_rpow hZ hdpos
  have hUp : 0 < Z^d := zero_lt_one.trans hU
  have hpow1 : 1 ≤ 1 + height := by linarith
  have hZpow : 0 ≤ (Z^d)^(1+D.t) := Real.rpow_nonneg hUp.le _
  have hFw (x : Fin D.N) : (B.fiber bin label left right hne).widths x = D.ell x / d := by
    change B.widths x = _
    rw [hwidth]
  constructor
  · -- inverse marked moment
    intro h1 h2 sel hsel hw n hn s hs t ht
    obtain ⟨k, hk1, hk2⟩ := grid_cover hδ h1 h2
    have hfd : (B.fiber bin label left right hne).rowData = data label := by
      change B.data label = data label
      rw [hdata]
    have hrect : Qrh.MarkedAnchor.Interface.Contract.InverseRectAt (Qrh.MarkedAnchor.Interface.Contract.canonicalSlotsRay (S.W : ℝ → ℂ) (33/50) S.modulus (Qrh.MarkedAnchor.Interface.Contract.SlotTwist.diag ⊤) le_top) (ρ k)
        (orientedProfile (B.fiber bin label left right hne).reverse
          (DetectorDictionaryInverseClippedUniform.referenceWindow : ℝ → ℂ))
        D.N (meshI k) 1 1 ε (Z^d) (B.fiber bin label left right hne).rowData
        (deg ((k, (B.fiber bin label left right hne).reverse), label))
        (Cl ((k, (B.fiber bin label left right hne).reverse), label)) := by
      rw [hfd]
      exact hb ((k, (B.fiber bin label left right hne).reverse), label) (Z^d)
        (hscaleZ _ d hd)
    have hadm : (ρ k).Admissible (B.fiber bin label left right hne).r
        (∑ x ∈ sel, (B.fiber bin label left right hne).widths x) 1 := by
      refine ⟨by linarith [show (0:ℝ) < anchorLeft by norm_num [anchorLeft]], ?_,
        Finset.sum_nonneg (fun x hx =>
          ((B.fiber bin label left right hne).widths_pos x (hsel hx)).le), ?_⟩
      · show _ ≤ (gridPt δ k - δ)*1
        linarith
      · show _ ≤ ((1 - gridPt δ k)/2 + (line.g0 - line.g1*gridPt δ k) - δ)*1
        have := slot_slack line hδε hk2 hk1
        rw [hDt] at hw
        linarith
    have href : ∀ v : ℝ, (∑ u ∈ (B.fiber bin label left right hne).rows,
        ‖polynomial ((B.fiber bin label left right hne).family u
          (B.fiber bin label left right hne).label) true
          (InverseMoment.childLogTest
            (DetectorDictionaryInverseClippedUniform.referenceWindow : ℝ → ℂ) v)
          ((Z^d)^(B.fiber bin label left right hne).r) 0 0 *
          (B.fiber bin label left right hne).physicalProduct sel u‖^2) ≤
        ((1 + ∑ q, Cl q)*(Z^d)^(1+D.t)*(1+height)^(2*(∑ q, deg q)))*
          (1+‖v‖)^(2*(∑ q, deg q)) := by
      intro v
      have hr := fiber_reference_of_rect le_top (B.fiber bin label left right hne) sel
        (S.W : ℝ → ℂ)
        (fun x => Complex.conj_eq_iff_im.mpr (S.real x))
        (fun x hx => S.complex_support hx)
        (fun x => by
          rw [S.complex_eq x, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (S.bounded x).1]
          exact (S.bounded x).2)
        _ hrect hU (by simpa using Finset.card_le_univ sel)
        (fun x _ => by
          change B.profile x = _
          rw [hprof]
          funext y
          exact (S.complex_eq y).symm)
        (fun x _ => hupper x) (fun x _ => hreal x)
        (fun x hx => ((B.fiber bin label left right hne).widths_pos x (hsel hx)).le)
        (fun x _ => by
          rw [hFw x]
          apply (div_le_iff₀ hdpos).mpr
          have h1 := hfine x
          have h2 := hmI k
          have h3 := mul_le_mul_of_nonneg_left hd (hmeshI k).le
          linarith)
        (fun x _ => by
          rw [hfd, hFw x]
          exact hlarge.2 d hdpos label x)
        hadm height hheight (fun x _ => hexternal x) v
      rw [hDt]
      set dq := deg ((k, (B.fiber bin label left right hne).reverse), label) with hdq
      have hdq_le : dq ≤ ∑ q, deg q := hdegle _
      have hpv : (1+‖v‖)^(2*dq) ≤ (1+‖v‖)^(2*(∑ q, deg q)) :=
        pow_le_pow_right₀ (by linarith [norm_nonneg v]) (by omega)
      have hph : (1+height)^(2*dq) ≤ (1+height)^(2*(∑ q, deg q)) :=
        pow_le_pow_right₀ hpow1 (by omega)
      have hZe : 0 ≤ (Z^d)^(1+ε) := Real.rpow_nonneg hUp.le _
      refine hr.trans ?_
      have hsplit := Qrh.MarkedAnchor.Interface.Contract.heightFactor_split v hheight dq
      calc Cl ((k, (B.fiber bin label left right hne).reverse), label)*(Z^d)^(1+ε)*
            ((1+‖v‖+height)^dq)^2
          ≤ Cl ((k, (B.fiber bin label left right hne).reverse), label)*(Z^d)^(1+ε)*
            ((1+height)^(2*dq)*(1+‖v‖)^(2*dq)) :=
            mul_le_mul_of_nonneg_left hsplit (mul_nonneg (hCl _).le hZe)
        _ ≤ (1 + ∑ q, Cl q)*(Z^d)^(1+ε)*
            ((1+height)^(2*(∑ q, deg q))*(1+‖v‖)^(2*(∑ q, deg q))) := by
            gcongr
            exact hClle _
        _ = ((1 + ∑ q, Cl q)*(Z^d)^(1+ε)*(1+height)^(2*(∑ q, deg q)))*
            (1+‖v‖)^(2*(∑ q, deg q)) := by ring
    have hres := hfib (B.fiber bin label left right hne) sel hUp
      ((1 + ∑ q, Cl q)*(Z^d)^(1+D.t)*(1+height)^(2*(∑ q, deg q))) (by positivity) href
      n hn s hs height t hheight ht
    refine hres.trans ?_
    have e1 : (1+height)^(Kf + 2*(∑ q, deg q)) ≤
        (1+height)^(Kf + 2*(∑ q, deg q) + ∑ k, Jo k) :=
      pow_le_pow_right₀ hpow1 (Nat.le_add_right _ _)
    have e2 : Cf*(1 + ∑ q, Cl q) ≤ Cf*(1 + ∑ q, Cl q) + ∑ k, Co k := by linarith
    calc Cf*((1 + ∑ q, Cl q)*(Z^d)^(1+D.t)*(1+height)^(2*(∑ q, deg q)))*(1+height)^Kf =
          (Cf*(1 + ∑ q, Cl q))*(1+height)^(Kf + 2*(∑ q, deg q))*(Z^d)^(1+D.t) := by
          rw [pow_add]; ring
      _ ≤ (Cf*(1 + ∑ q, Cl q) + ∑ k, Co k)*(1+height)^(Kf + 2*(∑ q, deg q) + ∑ k, Jo k)*
          (Z^d)^(1+D.t) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul e2 e1 (by positivity) hCfin.le) hZpow
  · -- ordinary two-factor moment
    intro h1 h2 sel hsel hw j k' hjk s hs t ht
    obtain ⟨k, hk1, hk2⟩ := grid_cover hδ h1 h2
    have hA := (hord k).2 rows hrows d hd a tstar T allowance i B hB hdata hprof hwidth hupper
      hreal bin label left right hne height hheight hexternal
    have hm0 : (0:ℝ) ≤ (B.fiber bin label left right hne).m := by
      have : (0:ℝ) < anchorLeft := by norm_num [anchorLeft]
      linarith
    have hm1 : (B.fiber bin label left right hne).m ≤ 1/2 := by
      have : anchorTop < 1 := by norm_num [anchorTop]
      linarith
    have hsum0 : (0:ℝ) ≤ ∑ x ∈ sel, (B.fiber bin label left right hne).widths x :=
      Finset.sum_nonneg (fun x hx =>
        ((B.fiber bin label left right hne).widths_pos x (hsel hx)).le)
    have hsumS : ∑ x ∈ sel, (B.fiber bin label left right hne).widths x ≤
        (1 - gridPt δ k)/2 + (line.g0 - line.g1*gridPt δ k) - δ := by
      have := slot_slack line hδε hk2 hk1
      rw [hDt] at hw
      linarith
    have hB' : 2*(B.fiber bin label left right hne).m +
        0*(∑ x ∈ sel, (B.fiber bin label left right hne).widths x) ≤ gridPt δ k - δ := by
      linarith
    have hmom := hA hm0 hm1 sel hsel hsum0 hsumS hB' j k' hjk s hs t ht
    refine hmom.trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hCole k) (pow_le_pow_right₀ hpow1 (hJole k)) (by positivity) hCfin.le) hZpow

/-- The bridge with the anchor family split at `anchorTop`: the stage family on
`[anchorLeft, anchorTop]` and any family slightly above `anchorTop`. -/
theorem fiber_of_improved_split {hi : ℝ} (hhi : anchorTop < hi)
    (hstages : Qrh.MarkedAnchor.Interface.Contract.ImprovedMoments anchorLeft anchorTop line.g0 line.g1)
    (htop : Qrh.MarkedAnchor.Interface.Contract.ImprovedMoments anchorTop hi line.g0 line.g1) : ImprovedFiberMoments line :=
  fiber_of_improved line hhi (improved_glue hstages htop)

end
end Qrh.TwoSlot.AnchorZeroLoss.Affine
#print axioms Qrh.TwoSlot.AnchorZeroLoss.Affine.fiber_of_improved
