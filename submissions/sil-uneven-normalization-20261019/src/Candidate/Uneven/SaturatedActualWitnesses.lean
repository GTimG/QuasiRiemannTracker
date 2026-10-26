import Candidate.Cycle63.Marked.Route.ActualWitnesses
import Candidate.Uneven.SaturatedAssembly
import Candidate.Cycle63.Marked.Route.ActualWeightedCount
import Candidate.Target836.Marked836.ActualWeightedFixedMesh
import Candidate.Cycle63.Marked.Route.ActualMarkedGates
import Candidate.Cycle63.Marked.AnnularPool
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorClassBudget

/- Original module: Candidate.Uneven.SaturatedWitnesses. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace OAI.SevenEighths.SaturatedActualWeighted
open OAI.SevenEighths.Cycle63ActualWeighted
open CenteredMomentDetectorPlainFiberSource CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification HeckeDetectorSupportedWitness
open HeckeDetectorWitnessRows HeckeDetectorFiberPartition LocalMoment SaturatedAssembly
local notation "O" => HeckeFamily.O
variable {Label Slot : Type} [Fintype Label] [Nonempty Label] [Fintype Slot] [DecidableEq Slot]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ} {hH : RayOrthogonality.globalUnits M≤ H}
variable {base anchor : Label→Character} {bad : Label→Ideal O} {W : ℝ→ℂ} {lo hi U : ℝ}

/-- The adaptive detector witnesses are constructed from actual buffered zero
maxima, uniformly for every amplitude bin, including unused rounded bins. -/
theorem actual_adaptive_supported_witnesses
    (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤ dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤ η)
    (hbudget : 12*e*((22:ℝ)+2)+8*κ+2*η≤ ε/2) :
    ∃Z₀ : ℝ,∀Z : ℝ,Z₀≤ Z → ∀d : ℝ,dmin≤ d → d≤ dmax →
      ∀{Row : Type}(χ : Row→Label→Character)(hχ : ∀u j,(χ u j).residue≠1),
      ∀(a binWidth : ℝ)(i : ℕ),i≤ I → 31/50≤2*a-1 → 2*a-1≤3/4 →
      0<binWidth → binWidth≤(2*a-1)/2 →
      (∀u,HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u,a≤ HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) ((3*i:ℕ)*Z^τ)) →
      (∀u j,(χ u j).modulus.absNorm≤ Z^d) →
      ∀(slots : Finset Slot)(widths : Slot→ℝ),(∀s∈slots,0≤ widths s) →
      0<(∑s∈slots,widths s) →
      Nonempty (∀bin : BinLabel slots ((2*a-1)/2) binWidth,
        ∀u,SupportedWitness (χ u) (Z^d) a ε (binCutoff slots widths a binWidth bin)
          (Z^τ) ((Z^d)^(τ/(2*dmax))) i) := by
  obtain ⟨Z₀,hsource⟩ := actual_supported_witness_family dmin dmax τ ε e κ η I
    hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' Row χ hχ a binWidth i hi ha0 ha hbin hbin' hnext hcurrent hmod
    slots widths hw hL
  have hbinWitness (bin : BinLabel slots ((2*a-1)/2) binWidth) :
      Nonempty (∀u,SupportedWitness (χ u) (Z^d) a ε (binCutoff slots widths a binWidth bin)
        (Z^τ) ((Z^d)^(τ/(2*dmax))) i) := by
    have hcut := binCutoff_bounds slots widths a binWidth ha0 ha hbin hbin' hw hL bin
    exact hsource Z hZ d hd hd' χ hχ a i hi (by linarith) (by linarith) hnext hcurrent hmod
      (binCutoff slots widths a binWidth bin) hcut.1 hcut.2
  exact ⟨fun bin=>Classical.choice (hbinWitness bin)⟩

end OAI.SevenEighths.SaturatedActualWeighted
end

/- Original module: Candidate.Uneven.SaturatedActualWeighted. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace OAI.SevenEighths.SaturatedActualWeighted
open OAI.SevenEighths.Cycle63ActualWeighted
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily CanonicalRowCompletion
open HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount HeckeDetectorDyadicProfiles
open DetectorDictionaryInverseRawInitialGates LocalMoment SaturatedAssembly Cycle63ActualMarked
open ConcreteTraceCRT ActualEisensteinCubic CenteredMomentDetectorPlainFiberSource
open HeckeDetectorSupportedWitness HeckeDetectorFiberPartition HeckeDetectorWitnessRows
open Marked830Assembly (RawFiberMoments)
local notation "O" => HeckeFamily.O
variable {Label Slot : Type} [Fintype Label] [Nonempty Label] [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

export OAI.SevenEighths.Marked836ActualWeighted (actual_marked_source_fields_fixedmesh)

theorem actual_weighted_row_sum_fixedmesh
    (base anchor : Label→Character) (bad : Label→Ideal O)
    (hbadM : ∀j,bad j≤ M)
    (hbad0 : ∀j,internalQ (bad j) (anchor j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (anchor j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (anchor j)≤ Ideal.span {(72:O)})
    (setup : DensityCountingSetup) (W : ℝ→ℂ) (lo hi bΦ Δ εm : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0<bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hΔ0 : 0≤ Δ) (hΔ : Δ=0) (hεm : 0<εm)
    (hβ : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤3/4+2*Δ) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀ᶠ U : ℝ in atTop,1<U ∧
      ∀B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W lo hi U,
      ∀a ε T allowance mesh binWidth height : ℝ,∀i : ℕ,
      31/50≤2*a-1 → 2*a-1≤3/4 → 0<ε → ε≤1/1000 →
      0≤ mesh → mesh≤ Cycle63MarkedPlain.markedPlainMesh (3/4+2*Δ) εm → 0<binWidth → binWidth≤(2*a-1)/2 →
      (∀s∈B.slots,B.widths s≤ mesh) → 0<(∑s∈B.slots,B.widths s) →
      0≤ height → 2*Real.pi*allowance+(3*i:ℕ)*T≤ height →
      (∀s∈B.slots,|B.relativeHeight s|≤ height) → (∀u∈B.rows,|B.commonHeight u|≤ height) →
      ∀witness : ∀bin : BinLabel B.slots ((2*a-1)/2) binWidth,
        ∀u,SupportedWitness (B.family u) U a ε (binCutoff B.slots B.widths a binWidth bin) T allowance i,
      (∀u∈B.rows,∀s∈B.slots,‖B.Q u s‖≤(U^(B.widths s))^((2*a-1)/2+binWidth)) →
      (∑u∈B.rows,‖∏s∈B.slots,B.Q u s‖^2)≤
        ((Fintype.card (BinLabel B.slots ((2*a-1)/2) binWidth):ℝ)*Fintype.card Label*
          (dyadicLength U:ℝ)^2*C)*(1+height)^J*
        U^(PR63Adaptation.fullCount (2*a-1) (∑s∈B.slots,B.widths s)+(2*a-1)*(∑s∈B.slots,B.widths s)+
          401*ε+mesh+εm+2*binWidth*(∑s∈B.slots,B.widths s)) := by
  let D := FixedUnmarkedDictionary.ofBases base
  obtain ⟨Ju,Cu,hCu,hU⟩ := Cycle63ActualUnmarked.actual_unmarked_fiber_gates D setup εm hεm hβ
  obtain ⟨Jm,Cm,hCm,hM⟩ := actual_marked_source_fields_fixedmesh (Slot:=Slot) M H hH base anchor bad
    hbadM hbad0 hbadTop hbad72 W lo hi bΦ (3/4+2*Δ) εm hWs hW hbΦ hrad
    (by linarith) hεm hβ hκβ
  let C := Cu+Cm
  let J := Ju+Jm
  refine ⟨J+1,192*C,by dsimp [C]; positivity,?_⟩
  filter_upwards [hU,hM] with U hU hM
  refine ⟨hU.1,?_⟩
  intro B a ε T allowance mesh binWidth height i ha0 ha hε hεsmall hmesh hmeshmax' hbin hbin'
    hwm hL hh hf hv hchoice witness hQ
  have hUp : 0<U := zero_lt_one.trans hU.1
  let Cnow := C*(1+height)^J
  have hCnow : 0<Cnow := by dsimp [Cnow,C]; positivity
  have hCu' : Cu*(1+height)^Ju≤ Cnow := by
    apply mul_le_mul (show Cu≤ C by dsimp [C]; linarith)
      (pow_le_pow_right₀ (by linarith : 1≤1+height) (by dsimp [J]; omega)) (by positivity)
    dsimp [C]; positivity
  have hCm' : Cm*(1+height)^Jm≤ Cnow := by
    apply mul_le_mul (show Cm≤ C by dsimp [C]; linarith)
      (pow_le_pow_right₀ (by linarith : 1≤1+height) (by dsimp [J]; omega)) (by positivity)
    dsimp [C]; positivity
  have hcut (bin : BinLabel B.slots ((2*a-1)/2) binWidth) :=
    binCutoff_bounds B.slots B.widths a binWidth ha0 ha hbin hbin'
      (fun s hs=>(B.widthsPositive s hs).le) hL bin
  have hmom (bin : BinLabel B.slots ((2*a-1)/2) binWidth) (label : Label)
      (left right : Fin (dyadicLength U)) : RawFiberMoments
      (adaptiveFiber B.rows B.slots B.widths B.Q B.family U a ε T allowance binWidth i hbin
        witness bin label left right) B.slots B.family B.Q B.widths U a ε
      (binCutoff B.slots B.widths a binWidth bin) (3/4+2*Δ) εm Cnow height label left right := by
    let F := adaptiveFiber B.rows B.slots B.widths B.Q B.family U a ε T allowance binWidth i hbin
      witness bin label left right
    have hfields (u : FreeRow) (hu : u∈F) := adaptiveFiber_fields B.rows B.slots B.widths B.Q B.family
      U a ε T allowance binWidth i hbin witness bin label left right u hu
    have hsub : F⊆B.rows := fun u hu=>(hfields u hu).1
    by_cases hne : F.Nonempty
    · let ub : UnmarkedBatch Label U a ε (binCutoff B.slots B.widths a binWidth bin) T allowance i := {
        rows := F
        family := B.family
        witness := witness bin
        row_norm := fun u hu=>B.rowNorm u (hsub hu)
        data := D.data
        reverse := fun _=>false
        row_coeff := fun u hu j I=>by
          simpa only [Bool.false_eq_true,ite_false,D,FixedUnmarkedDictionary.data,
            FixedUnmarkedDictionary.ofBases,momentElement] using B.idealCoefficients u (hsub hu) j I }
      have huf : ub.fiberRows label left right=F := by
        apply Finset.filter_eq_self.mpr
        intro u hu
        exact ⟨(hfields u hu).2.1,(hfields u hu).2.2.1,(hfields u hu).2.2.2.1⟩
      have hune : (ub.fiberRows label left right).Nonempty := huf.symm ▸ hne
      have hu := hU.2 a ε (binCutoff B.slots B.widths a binWidth bin) T allowance height i
        (by linarith) hε.le hεsmall (hcut bin).1 (hcut bin).2 hh hf ub rfl label left right hune
      dsimp only [UnmarkedBatch.fiber,UnmarkedFiber.r,UnmarkedFiber.m] at hu
      rw [huf] at hu
      have hgeom := fiber_lengths F hne B.family U a ε (binCutoff B.slots B.widths a binWidth bin)
        T allowance i hU.1 (witness bin) left right (fun u hu=>(hfields u hu).2.2.1)
        (fun u hu=>(hfields u hu).2.2.2.1)
      dsimp only at hgeom
      have hr0 : 0≤ Real.logb U ((2:ℝ)^left.val) := by linarith [hgeom.2.2.2.1,(hcut bin).1]
      have hm0 : 0≤ Real.logb U ((2:ℝ)^right.val) := hgeom.2.2.2.2
      have hm1 : Real.logb U ((2:ℝ)^right.val)≤1 := by linarith [hgeom.2.2.1]
      refine ⟨?_,?_,?_,?_⟩
      · exact hu.1.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hCu' (by positivity))
          (Real.rpow_nonneg (zero_lt_one.trans hU.1).le _))
      · intro j k hjk σ hσ freq hfreq
        exact (hu.2 j k hjk σ hσ freq hfreq).trans
          (mul_le_mul_of_nonneg_right hCu' (Real.rpow_nonneg (zero_lt_one.trans hU.1).le _))
      · intro selected hselected hcap1 hcap2 n hn σ hσ freq hfreq
        have he := (hM.2 B (fun s hs=>(hwm s hs).trans hmeshmax') height hh hv hchoice
          F hsub label selected hselected).1 _ hr0 hcap1 hcap2
          (binCutoff B.slots B.widths a binWidth bin) n hn σ hσ freq hfreq
        exact he.trans (mul_le_mul_of_nonneg_right hCm' (Real.rpow_nonneg (zero_lt_one.trans hU.1).le _))
      · intro selected hselected hcap j k hjk σ hσ freq hfreq
        have he := (hM.2 B (fun s hs=>(hwm s hs).trans hmeshmax') height hh hv hchoice
          F hsub label selected hselected).2 _ hm0 hm1 hcap j k hjk σ hσ freq hfreq
        exact he.trans (mul_le_mul_of_nonneg_right hCm' (Real.rpow_nonneg (zero_lt_one.trans hU.1).le _))
    · have he : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      change RawFiberMoments F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      rw [he]
      constructor
      · simp only [Finset.card_empty,Nat.cast_zero]
        positivity
      · intro j k hjk σ hσ freq hfreq
        simp only [Finset.sum_empty]
        positivity
      · intro selected hselected hcap1 hcap2 n hn σ hσ freq hfreq
        simp only [Finset.sum_empty]
        positivity
      · intro selected hselected hcap j k hjk σ hσ freq hfreq
        simp only [Finset.sum_empty]
        positivity
  have he := weighted_row_sum B.rows B.slots B.family B.Q B.widths U a ε T allowance mesh binWidth Δ
    εm Cnow height i hU.1 ha0 ha hε hmesh hbin hΔ0 hΔ hCnow hh hf B.widthsPositive hwm hL witness hQ hmom
  convert he using 1
  dsimp only [Cnow]
  rw [pow_succ]
  ring

theorem actual_weighted_row_sum_uniform_fixedmesh
    (base anchor : Label→Character) (bad : Label→Ideal O)
    (hbadM : ∀j,bad j≤ M)
    (hbad0 : ∀j,internalQ (bad j) (anchor j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (anchor j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (anchor j)≤ Ideal.span {(72:O)})
    (setup : DensityCountingSetup) (W : ℝ→ℂ) (lo hi bΦ Δ εm binWidth η : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0<bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hbin : 0<binWidth) (hη : 0<η)
    (hΔ0 : 0≤ Δ) (hΔ : Δ=0) (hεm : 0<εm)
    (hβ : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤3/4+2*Δ) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀ᶠ U : ℝ in atTop,1<U ∧
      ∀B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W lo hi U,
      ∀a ε T allowance mesh height : ℝ,∀i : ℕ,
      31/50≤2*a-1 → 2*a-1≤3/4 → 0<ε → ε≤1/1000 →
      0≤ mesh → mesh≤ Cycle63MarkedPlain.markedPlainMesh (3/4+2*Δ) εm → binWidth≤(2*a-1)/2 →
      (∀s∈B.slots,B.widths s≤ mesh) → 0<(∑s∈B.slots,B.widths s) →
      0≤ height → 2*Real.pi*allowance+(3*i:ℕ)*T≤ height →
      (∀s∈B.slots,|B.relativeHeight s|≤ height) → (∀u∈B.rows,|B.commonHeight u|≤ height) →
      ∀witness : ∀bin : BinLabel B.slots ((2*a-1)/2) binWidth,
        ∀u,SupportedWitness (B.family u) U a ε (binCutoff B.slots B.widths a binWidth bin) T allowance i,
      (∀u∈B.rows,∀s∈B.slots,‖B.Q u s‖≤(U^(B.widths s))^((2*a-1)/2+binWidth)) →
      (∑u∈B.rows,‖∏s∈B.slots,B.Q u s‖^2)≤
        C*(1+height)^J*
        U^(PR63Adaptation.fullCount (2*a-1) (∑s∈B.slots,B.widths s)+(2*a-1)*(∑s∈B.slots,B.widths s)+
          401*ε+mesh+εm+2*binWidth*(∑s∈B.slots,B.widths s)+η) := by
  obtain ⟨J,C,hC,hfield⟩ := actual_weighted_row_sum_fixedmesh (Slot:=Slot) M H hH
    base anchor bad hbadM hbad0 hbadTop hbad72 setup W lo hi bΦ Δ εm hWs hW hbΦ hrad hΔ0 hΔ hεm hβ hκβ
  obtain ⟨K,hK,hdyadic⟩ := fixed_label_dyadic_cost (Label:=Label) η hη
  let A : ℝ := (HeckeDetectorClassBudget.alphabetBound binWidth : ℝ)^Fintype.card Slot
  let C' := (1+A)*(1+K)*C
  have hA : 0≤ A := by dsimp [A]; positivity
  have hC' : 0<C' := by dsimp [C']; positivity
  refine ⟨J,C',hC',?_⟩
  filter_upwards [hfield,hdyadic] with U hfield hdyadic
  refine ⟨hfield.1,?_⟩
  intro B a ε T allowance mesh height i ha0 ha hε hεsmall hmesh hmeshmax' hbin' hwm hL hh hf hv hchoice
    witness hQ
  have he := hfield.2 B a ε T allowance mesh binWidth height i ha0 ha hε hεsmall hmesh hmeshmax'
    hbin hbin' hwm hL hh hf hv hchoice witness hQ
  have hcard : (Fintype.card (BinLabel B.slots ((2*a-1)/2) binWidth):ℝ)≤ A := by
    have hb := HeckeDetectorClassBudget.bin_card_le B.slots ((2*a-1)/2) binWidth (by linarith) hbin
    have hp : (HeckeDetectorClassBudget.alphabetBound binWidth)^B.slots.card≤
        (HeckeDetectorClassBudget.alphabetBound binWidth)^Fintype.card Slot := by
      apply Nat.pow_le_pow_right
      · unfold HeckeDetectorClassBudget.alphabetBound
        omega
      · exact Finset.card_le_univ B.slots
    dsimp only [A]
    exact_mod_cast hb.trans hp
  let E := PR63Adaptation.fullCount (2*a-1) (∑s∈B.slots,B.widths s)+(2*a-1)*(∑s∈B.slots,B.widths s)+
    401*ε+mesh+εm+2*binWidth*(∑s∈B.slots,B.widths s)
  have hUp : 0<U := zero_lt_one.trans hfield.1
  have hcost : ((Fintype.card (BinLabel B.slots ((2*a-1)/2) binWidth):ℝ)*Fintype.card Label*
      (dyadicLength U:ℝ)^2*C)≤(A*K*C)*U^η := by
    have hp := mul_le_mul hcard hdyadic (by positivity) hA
    have hpc := mul_le_mul_of_nonneg_right hp hC.le
    convert hpc using 1 <;> ring
  have hconst : A*K*C≤ C' := by
    apply mul_le_mul_of_nonneg_right _ hC.le
    exact mul_le_mul (by linarith : A≤1+A) (by linarith : K≤1+K) hK (by positivity)
  apply he.trans
  change _≤ C'*(1+height)^J*U^(E+η)
  calc
    _≤((A*K*C)*U^η)*(1+height)^J*U^E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcost (by positivity))
        (Real.rpow_nonneg hUp.le _)
    _≤(C'*U^η)*(1+height)^J*U^E := by
      gcongr
    _=C'*(1+height)^J*U^(E+η) := by rw [Real.rpow_add hUp E η]; ring
end OAI.SevenEighths.SaturatedActualWeighted
end

/- Original module: Candidate.Uneven.SaturatedActualWitnesses. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace OAI.SevenEighths.SaturatedActualWeighted
open OAI.SevenEighths.Cycle63ActualWeighted
open CenteredMomentDetectorPlainFiberSource CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification HeckeDetectorSupportedWitness
open HeckeDetectorWitnessRows HeckeDetectorFiberPartition LocalMoment SaturatedAssembly
local notation "O" => HeckeFamily.O
variable {Label Slot : Type} [Fintype Label] [Nonempty Label] [Fintype Slot] [DecidableEq Slot]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ} {hH : RayOrthogonality.globalUnits M≤ H}
variable {base anchor : Label→Character} {bad : Label→Ideal O} {W : ℝ→ℂ} {lo hi U : ℝ}

theorem actual_weighted_from_buffered_maxima_fixedmesh
    (base anchor : Label→Character) (bad : Label→Ideal O)
    (hbadM : ∀j,bad j≤ M)
    (hbad0 : ∀j,internalQ (bad j) (anchor j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (anchor j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (anchor j)≤ Ideal.span {(72:O)})
    (setup : DensityCountingSetup) (W : ℝ→ℂ) (lo hi bΦ Δ εm binWidth η : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0<bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hbin : 0<binWidth) (hη : 0<η)
    (hΔ0 : 0≤ Δ) (hΔ : Δ=0) (hεm : 0<εm)
    (hβ : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤3/4+2*Δ) :
    ∃J : ℕ,∀(dmin dmax τ ε e κw ηw : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤ dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*ηw)
    (hε : 0<ε) (hεsmall : ε≤1/1000) (he : 0<e) (he' : e<1/1000)
    (hκw : 0<κw) (hκw' : κw≤1) (hηw : 0≤ ηw)
    (hbudget : 12*e*((22:ℝ)+2)+8*κw+2*ηw≤ ε/2),
    ∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀d : ℝ,dmin≤ d → d≤ dmax →
      ∀B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W lo hi (Z^d),
      ∀a mesh height : ℝ,∀i : ℕ,i≤ I →
      31/50≤2*a-1 → 2*a-1≤3/4 →
      0≤ mesh → mesh≤ Cycle63MarkedPlain.markedPlainMesh (3/4+2*Δ) εm → binWidth≤(2*a-1)/2 →
      (∀s∈B.slots,B.widths s≤ mesh) → 0<(∑s∈B.slots,B.widths s) →
      0≤ height → 2*Real.pi*((Z^d)^(τ/(2*dmax)))+(3*i:ℕ)*Z^τ≤ height →
      (∀s∈B.slots,|B.relativeHeight s|≤ height) → (∀u∈B.rows,|B.commonHeight u|≤ height) →
      ∀hχ : ∀u∈B.rows,∀j,(B.family u j).residue≠1,
      (∀u : B.rows,HeckeDetectorZeros.zeroMaximum (B.family u.val) (hχ u.val u.property)
        (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u : B.rows,a≤ HeckeDetectorZeros.zeroMaximum (B.family u.val) (hχ u.val u.property)
        ((3*i:ℕ)*Z^τ)) →
      (∀u∈B.rows,∀j,(B.family u j).modulus.absNorm≤ Z^d) →
      (∀u∈B.rows,∀s∈B.slots,‖B.Q u s‖≤((Z^d)^(B.widths s))^((2*a-1)/2+binWidth)) →
      (∑u∈B.rows,‖∏s∈B.slots,B.Q u s‖^2)≤
        C*(1+height)^J*
        (Z^d)^(PR63Adaptation.fullCount (2*a-1) (∑s∈B.slots,B.widths s)+(2*a-1)*(∑s∈B.slots,B.widths s)+
          401*ε+mesh+εm+2*binWidth*(∑s∈B.slots,B.widths s)+η) := by
  obtain ⟨J,C,hC,hfield⟩ := actual_weighted_row_sum_uniform_fixedmesh (Slot:=Slot) M H hH
    base anchor bad hbadM hbad0 hbadTop hbad72 setup W lo hi bΦ Δ εm binWidth η hWs hW hbΦ hrad
    hbin hη hΔ0 hΔ hεm hβ hκβ
  refine ⟨J,?_⟩
  intro dmin dmax τ ε e κw ηw I hdmin hdmax hτ hτzero hτheight hε hεsmall he he' hκw hκw' hηw hbudget
  obtain ⟨Z₀,hwitness⟩ := actual_adaptive_supported_witnesses (Label:=Label) (Slot:=Slot)
    dmin dmax τ ε e κw ηw I hdmin hdmax hτ hτzero hτheight hε he he' hκw hκw' hηw hbudget
  obtain ⟨U₀,hU₀⟩ := eventually_atTop.mp hfield
  have hlarge : ∀ᶠ Z : ℝ in atTop,U₀≤ Z^dmin :=
    (tendsto_rpow_atTop hdmin).eventually (eventually_ge_atTop U₀)
  refine ⟨C,hC,?_⟩
  filter_upwards [hlarge,eventually_ge_atTop Z₀,eventually_gt_atTop (1:ℝ)] with Z hlarge hZ₀ hZ
  refine ⟨hZ,?_⟩
  intro d hd hd' B a mesh height i hi ha0 ha hmesh hmeshmax' hbin' hwm hL hh hf hv hchoice
    hχ hnext hcurrent hmod hQ
  have hthreshold : U₀≤ Z^d := hlarge.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hd)
  have hfield := hU₀ (Z^d) hthreshold
  by_cases hne : B.rows.Nonempty
  · obtain ⟨u₀,hu₀⟩ := hne
    obtain ⟨w⟩ := hwitness Z hZ₀ d hd hd' (fun u:B.rows=>B.family u.val)
      (fun u=>hχ u.val u.property) a binWidth i hi ha0 ha hbin hbin' hnext hcurrent
      (fun u=>hmod u.val u.property) B.slots B.widths
      (fun s hs=>(B.widthsPositive s hs).le) hL
    let urow : B.rows := ⟨u₀,hu₀⟩
    exact hfield.2 (B.retracted urow) a ε (Z^τ) ((Z^d)^(τ/(2*dmax))) mesh height i
      ha0 ha hε hεsmall hmesh hmeshmax' hbin' hwm hL hh hf hv hchoice
      (fun bin u=>w bin (supportedRowRetraction B.rows urow u)) hQ
  · have hempty : B.rows=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty,Finset.sum_empty]
    have hUp : 0<Z^d := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
    positivity

end OAI.SevenEighths.SaturatedActualWeighted
end
