/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Single-rectangle inverse source transport onto the original supported Batch.
Adapted from Sil/Bebel's Interface.Bridge and AnchorZeroLoss.AffineBridge,
retaining the OpenAI/Collet reference-profile, coefficient and height transports. -/
import Candidate.C092.transport.MediumInversePriceJoin
import Candidate.C092.UpstreamPrivate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Interface.Bridge
import Candidate.C092.UpstreamPrivate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Return.ImprovedFiber

namespace QRH.Cycle092.MediumInversePrice
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators ComplexConjugate ContDiff
open Filter Set OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorCoefficientTransfer DetectorDictionaryInverseRawInitialGates ProbeHighRowFamily
open Qrh.MarkedAnchor.Interface.Contract Qrh.MarkedAnchor.Interface.Bridge
local notation "O" => HeckeFamily.O
local instance sourceQuotientFinite (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-- A genuine rectangular inverse source supplies an improved count on the
literal original supported fiber, without the native r+2z or 2r+8z gates.
The sole replacement is the true rectangular admission, including its open
anchor decrement. Further flagged restrictions retain the same count. -/
theorem original_rect_inverse_count (ρ : AnchorRect)
    (hsource : UniformInverseRectSource canonicalFamily ρ) (εm : ℝ) (hεm : 0 < εm) :
    ∃ mesh : ℝ, 0 < mesh ∧ ∀ (D : Cycle25.Weighted.MomentData)
      (S : Cycle25ProbeFinalAssembly.WeightedSourceData D),
      D.t=εm → (∀ j, D.ell j ≤ mesh/200) →
    ∀ η : Character, ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
    1 < Z ∧ ∀ d : ℝ, (1/200 : ℝ) ≤ d →
    ∀ (a ε cutoff T allowance : ℝ) (i : ℕ)
      (B : Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤))
        (Fin D.N) (Z^d) a ε cutoff T allowance i),
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η →
      B.profile=(fun _ x => (S.w x : ℂ)) → B.upper=(fun _ => 2) →
      B.widths=(fun j => D.ell j/d) → (∀ j, (B.external j).re=17/50) →
    ∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
    ∀ height z : ℝ, 0 ≤ height → 1/2 ≤ a →
      (∀ j, |(B.external j).im| ≤ height) →
      2*Real.pi*allowance+(3*i : ℕ)*T ≤ height →
    let F := B.fiber bin label left right hne;
      0 ≤ z → z ≤ 7/37 → ρ.Admissible F.r z 1 →
    ∀ rows : Finset FreeRow, rows ⊆ F.rows →
    (rows.card : ℝ) ≤ (12*(1+height)*(C*(1+height)^J))*
      (Z^d)^(1-(2*a-1)*F.r-2*F.q*z+2*ε+(2*a-1)*F.mesh+D.t) := by
  obtain ⟨mesh,hmesh,hI⟩ := hsource εm hεm
  refine ⟨mesh,hmesh,?_⟩
  intro D S hDt hfine η
  let data := sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η
  have hsupp (b : Bool) : Function.support (orientedProfile b
      (DetectorDictionaryInverseClippedUniform.referenceWindow : ℝ → ℂ)) ⊆ Icc (1/18 : ℝ) (13/4) := by
    intro x hx
    apply DetectorDictionaryInverseClippedUniform.referenceWindow_support
    apply subset_tsupport
    intro h0
    apply hx
    cases b <;> simp [orientedProfile,h0]
  have hsmooth (b : Bool) : ContDiff ℝ ∞ (orientedProfile b
      (DetectorDictionaryInverseClippedUniform.referenceWindow : ℝ → ℂ)) := by
    cases b
    · simpa only [orientedProfile,Bool.false_eq_true,ite_false] using
        DetectorDictionaryInverseClippedUniform.referenceWindow.smooth ⊤
    · simpa only [orientedProfile,ite_true] using
        HeckeInverseAmplification.conjugate_profile_smooth _
          (DetectorDictionaryInverseClippedUniform.referenceWindow.smooth ⊤)
  have hcf : canonicalFamily (canonicalSlotsRay (S.W : ℝ → ℂ) (33/50) S.modulus (SlotTwist.diag ⊤) le_top) :=
    ⟨S.W,S.W.smooth ⊤,S.complex_support,S.modulus,inferInstance,SlotTwist.diag ⊤,le_top,rfl⟩
  choose deg Cl Z₀ hCl hZ₀ hb using
    fun q : Bool × Sum Bool (RayQuotient.Characters S.modulus ⊤) =>
      hI D.N _ hcf (orientedProfile q.1
        (DetectorDictionaryInverseClippedUniform.referenceWindow : ℝ → ℂ)) (1/18) (13/4)
        (by norm_num) (by norm_num) (hsupp q.1) (hsmooth q.1) (data q.2)
  have hdegle (q : Bool × Sum Bool (RayQuotient.Characters S.modulus ⊤)) : deg q ≤ ∑ q, deg q :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
  obtain ⟨Kf,Cf,hCf,hfib⟩ := DetectorDictionaryInverseMarkedUniform.fiber_inverse_height_uniform (∑ q, deg q)
  have hCsum : 0 < 1+∑ q, Cl q := by
    have := Finset.sum_nonneg (fun q (_ : q∈Finset.univ) => (hCl q).le)
    linarith
  have hClle (q) : Cl q ≤ 1+∑ q, Cl q := by
    have := Finset.single_le_sum (fun q (_ : q∈Finset.univ) => (hCl q).le) (Finset.mem_univ q)
    linarith
  refine ⟨Kf+2*(∑ q, deg q),Cf*(1+∑ q, Cl q),mul_pos hCf hCsum,?_⟩
  have hscale : ∀ᶠ Z : ℝ in atTop, ∀ q, ∀ d : ℝ, (1/200 : ℝ) ≤ d → Z₀ q ≤ Z^d :=
    Filter.eventually_all.mpr (fun q =>
      HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) (Z₀ q) (by norm_num))
  filter_upwards [eventually_gt_atTop (1 : ℝ),hscale,
    DetectorDictionaryInverseMarkedReference.deleted_large_eventually data D.ell
      (fun j => (D.slots_bounds j).1)] with Z hZ hscale hlarge
  refine ⟨hZ,?_⟩
  intro d hd a ε cutoff T allowance i B hdata hprof hupper hwidth hreal
    bin label left right hne height z hh ha hexternal hfreq
  dsimp only
  intro hz hzmax hadm rows hrows
  let F := B.fiber bin label left right hne
  have hdpos : 0 < d := by linarith
  have hU : 1 < Z^d := Real.one_lt_rpow hZ hdpos
  have hUp : 0 < Z^d := zero_lt_one.trans hU
  have hpow1 : 1 ≤ 1+height := by linarith
  have hfd : F.rowData=data label := by change B.data label=data label;rw [hdata]
  have hFw (j : Fin D.N) : F.widths j=D.ell j/d := by change B.widths j=_;rw [hwidth]
  have hrect : InverseRectAt (canonicalSlotsRay (S.W : ℝ → ℂ) (33/50)
      S.modulus (SlotTwist.diag ⊤) le_top) ρ
      (orientedProfile F.reverse (DetectorDictionaryInverseClippedUniform.referenceWindow : ℝ → ℂ))
      D.N mesh 1 1 εm (Z^d) F.rowData (deg (F.reverse,label)) (Cl (F.reverse,label)) := by
    rw [hfd]
    exact hb (F.reverse,label) (Z^d) (hscale _ d hd)
  have hraw : ∀ selected : Finset (Fin D.N), selected⊆F.slots →
      (∑ j∈selected,F.widths j) ≤ z →
      ∀ n : ℕ,n≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
        (∑ u∈F.rows,‖polynomial (F.family u F.label) true
          ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
          ((Z^d)^F.r) s t*F.physicalProduct selected u‖^2) ≤
          ((Cf*(1+∑ q,Cl q))*(1+height)^(Kf+2*(∑ q,deg q)))*(Z^d)^(1+D.t) := by
    intro selected hsel hwidths n hn s hs t ht
    have href : ∀ v : ℝ,
        (∑ u∈F.rows,‖polynomial (F.family u F.label) true
          (InverseMoment.childLogTest (DetectorDictionaryInverseClippedUniform.referenceWindow : ℝ → ℂ) v)
          ((Z^d)^F.r) 0 0*F.physicalProduct selected u‖^2) ≤
        ((1+∑ q,Cl q)*(Z^d)^(1+D.t)*(1+height)^(2*(∑ q,deg q)))*
          (1+‖v‖)^(2*(∑ q,deg q)) := by
      intro v
      have hrectSel : ρ.Admissible F.r (∑ j∈selected,F.widths j) 1 :=
        AnchorRect.admissible_downward hadm hadm.1 le_rfl
          (Finset.sum_nonneg (fun j hj => (F.widths_pos j (hsel hj)).le)) hwidths
      have hr := fiber_reference_of_rect le_top F selected (S.W : ℝ → ℂ)
        (fun x => Complex.conj_eq_iff_im.mpr (S.real x))
        (fun x hx => S.complex_support hx)
        (fun x => by rw [S.complex_eq x,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (S.bounded x).1];exact (S.bounded x).2)
        _ hrect hU (by simpa using Finset.card_le_univ selected)
        (fun j _ => by change B.profile j=_;rw [hprof];funext x;exact (S.complex_eq x).symm)
        (fun j _ => by change B.upper j=2;exact congrFun hupper j) (fun j _ => hreal j)
        (fun j hj => (F.widths_pos j (hsel hj)).le)
        (fun j _ => by
          rw [hFw]
          apply (div_le_iff₀ hdpos).mpr
          have := hfine j
          have hm := mul_le_mul_of_nonneg_right hd hmesh.le
          linarith)
        (fun j _ => by
          rw [hfd]
          rw [hFw]
          exact hlarge.2 d hdpos label j)
        hrectSel height hh (fun j _ => hexternal j) v
      rw [hDt]
      have hdq := hdegle (F.reverse,label)
      have hClq := hCl (F.reverse,label)
      have hsplit := heightFactor_split v hh (deg (F.reverse,label))
      have hpv : (1+‖v‖)^(2*deg (F.reverse,label)) ≤ (1+‖v‖)^(2*(∑ q,deg q)) :=
        pow_le_pow_right₀ (by linarith [norm_nonneg v]) (by omega)
      have hph : (1+height)^(2*deg (F.reverse,label)) ≤ (1+height)^(2*(∑ q,deg q)) :=
        pow_le_pow_right₀ hpow1 (by omega)
      apply hr.trans
      calc
        _ ≤ Cl (F.reverse,label)*(Z^d)^(1+εm)*
            ((1+height)^(2*deg (F.reverse,label))*(1+‖v‖)^(2*deg (F.reverse,label))) :=
          mul_le_mul_of_nonneg_left hsplit (by positivity)
        _ ≤ (1+∑ q,Cl q)*(Z^d)^(1+εm)*
            ((1+height)^(2*(∑ q,deg q))*(1+‖v‖)^(2*(∑ q,deg q))) := by gcongr;exact hClle _
        _ = _ := by ring
    have hres := hfib F selected hUp
      ((1+∑ q,Cl q)*(Z^d)^(1+D.t)*(1+height)^(2*(∑ q,deg q))) (by positivity) href
      n hn s hs height t hh ht
    convert hres using 1 <;> rw [pow_add] <;> ring
  have hcount := Qrh.MarkedAnchor.Return.fiber_inverse_width_count F hU ha
    (by positivity : 0 ≤ (Cf*(1+∑ q,Cl q))*(1+height)^(Kf+2*(∑ q,deg q)))
    hh hfreq z hz hzmax hraw
  exact (Nat.cast_le.mpr (Finset.card_le_card hrows)).trans hcount

#print axioms original_rect_inverse_count
end
end QRH.Cycle092.MediumInversePrice
