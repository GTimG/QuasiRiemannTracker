/- Repeated marks: fork of Record1252270103Source.PositiveRadius.SomeUniform (Hailey Collet, Apache-2.0; inherited notices retained).
Only the declarations whose statement depends on the HIGH gain, the uniform detector
cutoff or the source validity are restated, renamed `*_rm`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.PositiveRadius.SomeUniform
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.GainC
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.CountWrappersK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.GainPaymentK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.PaymentWrappersK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.WitnessWrappersK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Finite.SourceValid2
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Fork.Record1252270103Source.PositiveRadius.SomeLabeled
/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual source labels pulled back through the checked full sixth-root supplier. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.PositiveRadius.Some
noncomputable section
open OAI OAI.SevenEighths
open Record12518109Natural
open scoped Classical BigOperators ContDiff
open Set Filter HeckeFamily HeckeInverseAmplification ProbePhysical LocalMoment HeckeDetectorZeros
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource CenteredMomentCommonMaskExpansion
open CenteredMomentPrimeSlot HeckePrimeAnnular Cycle61Moment
open Record12518109GainWholeGeometry Record12518109GainExceptional Record12518109Gain WeightedHigh
open QRH.Record1252270103Source.High
local notation "O" => HeckeFamily.O
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local instance positiveRadiusSomeCutoffUniformLabeledRegularRawTauFinite_rm : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem actual_uniform_labeled_regular_raw_max_uniform_tau_rm
    (ηchar η₀ : Character)
    (sourceB sourceLam sourceCap sourceMesh : ℝ)
    (hB0 : 22/23≤sourceB) (hB1 : sourceB≤1) (hlam : 1<sourceLam) (hh0 : 0≤sourceCap) (hh1 : sourceCap<1)
    (setup : DensityCountingSetup) (W : ℝ→ℂ)
    (bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot : ℝ) (I : ℕ) (δ Bmask Broot wmin : ℝ) (hδ : 0<δ)
    (hBmask : 0≤Bmask) (hBroot : 0≤Broot) (hwmin : 0<wmin)
    (hparentSource : QRH.Record12518109Existence.UnitFaceSource ⟨sourceB,sourceLam,0,sourceB,0,sourceCap⟩ sourceMesh εm)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 2≤bΦ) (hrad : Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hbin : 0<binWidth) (hη : 0<η) (hζ : 0<ζ) (hεm : 0<εm)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hrmin : 0<rmin) (hRw : 0≤Rwidth)
    (hε : 0<ε) (hεsmall : ε≤1/1000) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hκ' : κ≤1) (hηw : 0≤ηw)
    (hbudget : 288*e+8*κ+2*ηw≤ε/2)
    (hεslot : 0<εslot) (hηslot : 0≤ηslot)
    (hslotBudget : 8*e*Rwidth+κ≤εslot) (hgap : εslot<rmin*binWidth)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (qlo Q mesh : ℝ) (hqlo : 0<qlo) (hQ : qlo≤Q)
    (hQroot : Q/12≤Broot) (hdlo : dmin≤qlo/2+δ)
    (hdsource : Q+Bmask+δ≤dmax)
    (hrlower : rmin≤wmin/dmax) (hmesh : 0≤mesh)
    (hmeshmax : mesh≤sourceMesh)
    (hmeshR : mesh≤Rwidth) :
    ∃J : ℕ,∃C : ℝ,0<C ∧∀τ : ℝ,0<τ →τ<dmin/2 →4*τ<dmin*ηw →2*τ<dmin*ηslot →∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(F a : ℝ)(i : ℕ),i≤I →3/4≤a →a≤7/8 →qlo≤F →F≤Q →
      binWidth≤(2*a-1)/2 →
      ∀{Row : Type}[Nonempty Row](rows : Finset Row)(row : Row→NonzeroFrequency),
      Set.InjOn row (↑rows:Set Row)→∀(slots : Finset Slot)(w σ v : Slot→ℝ)
        (t : Row→ℝ)(θ : Slot→RayQuotient.Characters M H)(mask : Row→Ideal O)(χ : Row→Character),
      (∀h∈rows,rawFrequencyNorm (row h)≤Z^F) →
      (∀h∈rows,¬(wholeRegularDictionary M H hH ηchar η₀).exceptionalCore (sixthFrequencyEquiv.symm (row h)).1) →
      (∀h∈rows,mask h≠0) →(∀h∈rows,((mask h).absNorm:ℝ)≤Z^Bmask) →
      (∀h∈rows,∀K,idealCoeff (χ h) K=idealCoeff
        (excluded (naturalRow ηchar (row h).val (row h).property).character (mask h)) K)→
      ∀hn : ∀h∈rows,∀j,(wholeSourceFamily M H hH η₀ (χ h) j).residue≠1,
      (∀h∈rows,∀hh : h∈rows,zeroMaximum (wholeSourceFamily M H hH η₀ (χ h)) (hn h hh)
        (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀h∈rows,∀hh : h∈rows,a≤zeroMaximum (wholeSourceFamily M H hH η₀ (χ h)) (hn h hh) ((3*i:ℕ)*Z^τ)) →
      (∀s∈slots,wmin≤w s) →(∀s∈slots,(33/50)≤σ s) →(∀s∈slots,σ s≤(33/50)) →
      (∀s∈slots,w s≤mesh*dmin) →
      (∀h∈rows,|t h|+Z^τ/2≤(3*i+2:ℕ)*Z^τ) →
      (∀h∈rows,∀s∈slots,|t h+v s|+Z^τ/2≤(3*i+2:ℕ)*Z^τ) →
      let S:=∑s∈slots,w s;
      (∑h∈rows,(∏s∈slots,max 1 ‖labeledRawSlot M H hH η₀ W Z w σ v t θ χ h s‖)^2)≤
        C*(1+rawGeometryHeight Z τ I)^J*Z^(QRH.Record1252270103Source.High.rho (2*a-1)*F+(2*a-1)*S-QRH.RepeatedMarks.Source.gainC (2*a-1) sourceB sourceLam sourceCap S F+
          dmax*(155*ε+mesh+εm+(2*a-1)*ζ+η)+QRH.Record1252270103Source.High.rho (2*a-1)*δ+2*binWidth*S) := by
  obtain ⟨J,C,hC,hraw⟩:=actual_labeled_regular_raw_max_uniform_tau_rm (Slot:=Slot) M H hH ηchar η₀
    sourceB sourceLam sourceCap sourceMesh hB0 hB1 hlam hh0 hh1
    setup W bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot I δ Bmask Broot wmin
    hδ hBmask hBroot hwmin hparentSource hWs hW hbΦ hrad hbin hη hζ hεm hdmin hdmax hrmin hRw
    hε hεsmall he he' hκ hκ' hηw hbudget hεslot hηslot hslotBudget hgap hβ
  refine ⟨J,C,hC,?_⟩
  intro τ hτ hτzero hτheight hheight
  filter_upwards [hraw τ hτ hτzero hτheight,eventually_uniform_root_geometry qlo Q τ δ Bmask dmin dmax rmin Rwidth mesh ηslot wmin I
    (by linarith) hQ hBmask hδ.le hdmin hdlo hdsource hτ hηslot hheight hwmin.le hrlower hmesh hmeshR]
    with Z hr hg
  refine ⟨hr.1,?_⟩
  intro F a i hi' ha0 ha1 hFlo hFhi hbin' Row _ rows row hinj slots w σ v t θ mask χ
    hnorm hregular hmask hmasknorm hcoeff hn hnext hcurrent hw hlo hhi hwhi hplainfreq hfreq S
  have hZp : 0<Z:=zero_lt_one.trans hr.1
  by_cases he : rows.Nonempty
  · obtain ⟨l₀,hl₀⟩:=he
    have hgeom:=hg.2 F hFlo hFhi i hi' slots w hw hwhi
    exact hr.2 F (Q+Bmask+δ) a mesh (rawGeometryHeight Z τ I) i hi' ha0 ha1
      (hqlo.trans_le hFlo) (by linarith) hmesh hmeshmax hbin' (raw_geometry_height_nonneg hZp.le I)
      rows row hinj slots w σ v t θ mask χ hnorm hregular hmask hmasknorm hcoeff hn hnext hcurrent hw hlo hhi
      (fun s hs=>raw_geometry_height_frequency hZp.le i I hi' (hplainfreq l₀ hl₀) (hfreq l₀ hl₀ s hs))
      (fun l hl=>raw_geometry_height_time hZp.le i I hi' (hplainfreq l hl)) hfreq
      hgeom.1 hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2.1 hgeom.2.2.2.2.1 (by linarith) hgeom.2.2.2.2.2
  · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty]
    exact mul_nonneg (mul_nonneg hC.le (pow_nonneg (by
      have hh:=raw_geometry_height_nonneg (τ:=τ) hZp.le I
      linarith) _)) (Real.rpow_nonneg hZp.le _)

end
end QRH.Record1252270103Source.PositiveRadius.Some
