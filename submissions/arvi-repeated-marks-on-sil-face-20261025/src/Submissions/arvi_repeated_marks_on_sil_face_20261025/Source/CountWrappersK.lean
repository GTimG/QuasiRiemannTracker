/- Repeated marks: Collet-shaped entry points of the repeated-mark weighted count (eight copies of
each marked slot, one detector cutoff per amplitude class). The statements are those of Collet's
High/WeightedRows.lean and High/ActualWeighted.lean (Apache-2.0) with the bin cutoff and the gain
replaced; they are the targets of the mechanically forked downstream modules. The gain is the
clamped repeated-mark gain `gainC` of Source/GainC.lean, which is the eight-copy gain at the
nonnegative widths and parameters met here. -/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.ActualWeightedK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.GainC
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace QRH.Record1252270103Source.High
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily CanonicalRowCompletion
open HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount HeckeDetectorDyadicProfiles
open DetectorDictionaryInverseRawInitialGates LocalMoment
open ConcreteTraceCRT ActualEisensteinCubic CenteredMomentDetectorPlainFiberSource
open HeckeDetectorSupportedWitness HeckeDetectorFiberPartition HeckeDetectorWitnessRows
open HeckeDetectorCoefficientTransfer Record12518109GainActual
local notation "O" => HeckeFamily.O

/-- The detector cutoff of an amplitude bin: the cutoff of its amplitude class. -/
def binCutoff_rm {Slot : Type*} (B lam h : ℝ) (slots : Finset Slot) (widths : Slot→ℝ) (a binWidth : ℝ)
    (bin : BinLabel slots ((2*a-1)/2) binWidth) : ℝ :=
  QRH.RepeatedMarks.Source.binCutoffK 8 B lam h slots widths a binWidth bin

/-- Every bin cutoff is an admissible detector cutoff. -/
lemma binCutoff_rm_bounds {Slot : Type*} {B lam h a binWidth : ℝ} (slots : Finset Slot)
    (widths : Slot→ℝ) (bin : BinLabel slots ((2*a-1)/2) binWidth)
    (ha0 : 1/2≤2*a-1) (ha : 2*a-1≤3/4) (hB0 : 22/23≤B) (hlam : 1<lam) (hh0 : 0≤h) (hh1 : h≤1)
    (hL : 0≤∑s∈slots,widths s) :
    1≤binCutoff_rm B lam h slots widths a binWidth bin ∧
      binCutoff_rm B lam h slots widths a binWidth bin≤3/2 := by
  have hh := QRH.RepeatedMarks.Source.classCutoff_bounds slots widths
    (binValue slots ((2*a-1)/2) binWidth bin) 8 ha0 ha hB0 hlam hh0 hh1 hL
  exact ⟨hh.1, hh.2.trans (by norm_num)⟩

variable {Label Slot : Type} [Fintype Label] [Nonempty Label] [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local instance countWrappersFinite : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
theorem ordinary_actual_weighted_row_sum_rm
    (base anchor : Label→Character) (bad : Label→Ideal O)
    (hbadM : ∀j,bad j≤M)
    (hbad0 : ∀j,internalQ (bad j) (anchor j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (anchor j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (anchor j)≤Ideal.span {(72:O)})
    (capacity lam cap sourceMesh : ℝ)
    (hB0 : 22/23≤capacity) (hB1 : capacity≤1) (hlam : 1<lam) (hh0 : 0≤cap) (hh1 : cap<1)
    (setup : DensityCountingSetup) (W : ℝ→ℂ) (bΦ εm ζ : ℝ)
    (hsource : QRH.Record12518109Existence.UnitFaceSource ⟨capacity,lam,0,capacity,0,cap⟩ sourceMesh εm)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 2≤bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hζ : 0<ζ) (hεm : 0<εm)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀ᶠ U : ℝ in atTop,1<U ∧
      ∀B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W (33/50) (33/50) U,
      ∀a ε T allowance mesh binWidth height : ℝ,∀i : ℕ,
      1/2≤2*a-1 → 2*a-1≤3/4 → 0≤ε → ε≤1/1000 →
      0≤ mesh → mesh≤sourceMesh → 0<binWidth → binWidth≤(2*a-1)/2 →
      (∀s∈B.slots,B.widths s≤ mesh) → 0≤(∑s∈B.slots,B.widths s) →
      0≤height → 2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      (∀s∈B.slots,|B.relativeHeight s|≤height) → (∀u∈B.rows,|B.commonHeight u|≤height) →
      ∀witness : ∀bin : BinLabel B.slots ((2*a-1)/2) binWidth,
        ∀u,SupportedWitness (B.family u) U a ε (binCutoff_rm capacity lam cap B.slots B.widths a binWidth bin) T allowance i,
      (∀u∈B.rows,∀s∈B.slots,‖B.Q u s‖≤(U^(B.widths s))^((2*a-1)/2+binWidth)) →
      (∑u∈B.rows,‖∏s∈B.slots,B.Q u s‖^2)≤
        ((Fintype.card (BinLabel B.slots ((2*a-1)/2) binWidth):ℝ)*Fintype.card Label*
          (dyadicLength U:ℝ)^2*C)*(1+height)^J*
        U^(rho (2*a-1)+(2*a-1)*(∑s∈B.slots,B.widths s)-
          QRH.RepeatedMarks.Source.gainC (2*a-1) capacity lam cap (∑s∈B.slots,B.widths s) 1+
          155*ε+mesh+εm+(2*a-1)*ζ+2*binWidth*(∑s∈B.slots,B.widths s)) := by
  obtain ⟨J,C,hC,hev⟩ := QRH.RepeatedMarks.Source.ordinary_actual_weighted_row_sum_K (Slot:=Slot) M H hH 8
    (by norm_num) base anchor bad hbadM hbad0 hbadTop hbad72 capacity lam cap sourceMesh hB0 hB1
    hlam hh0 hh1 setup W bΦ εm ζ hsource hWs hW hbΦ hrad hζ hεm hβ
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hev] with U hU
  refine ⟨hU.1,?_⟩
  intro B a ε T allowance mesh binWidth height i ha0 ha1 hε0 hε1 hm0 hm1 hb0 hb1 hwm hS hh hheight
    hrel hcom witness hQ
  have hb := hU.2 B a ε T allowance mesh binWidth height i ha0 ha1 hε0 hε1 hm0 hm1 hb0 hb1 hwm hS hh
    hheight hrel hcom witness hQ
  have hg : QRH.RepeatedMarks.Source.gainRep 8 (2*a-1) capacity lam cap (∑s∈B.slots,B.widths s) 1=
      QRH.RepeatedMarks.Source.gainC (2*a-1) capacity lam cap (∑s∈B.slots,B.widths s) 1 := by
    rw [QRH.RepeatedMarks.Source.gainC_eq
      (QRH.RepeatedMarks.Source.params_of ha0 ha1 hB0 hB1 hlam hh0 hh1.le) hS zero_le_one]
    simp only [QRH.RepeatedMarks.Source.gainRep, Nat.cast_ofNat]
  rw [hg] at hb
  exact hb

end QRH.Record1252270103Source.High
end
