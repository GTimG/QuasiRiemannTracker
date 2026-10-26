import Candidate.Target830.Marked.GenericCountAssembly
import Candidate.Cycle63.Marked.Route.ActualMaxWeighted
import Candidate.Cycle63.Marked.Route.ActualWitnesses
import Candidate.Cycle63.Marked.DeletionMaxAmplitude
import Candidate.Target830.Kernel.ExactMarkedGain
import Candidate.Target830.Marked.ActualWitnessesFixedMesh
import Candidate.Cycle63.Marked.WholeBufferedMax
import Candidate.Cycle63.Marked.WholeNaturalBatch
import Candidate.Cycle63.Marked.WholeFamilyMaximum
import Candidate.Target830.Marked.VariableSupply
import Candidate.Cycle63.Marked.WholeCoreGates
import Candidate.Cycle63.Marked.DeletionRawPadded

/- Original module: Candidate.Target830.Marked.ActualUnmarkedUniform. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace OAI.SevenEighths.Marked830ActualWeighted
open OAI.SevenEighths.Cycle63ActualWeighted
open HeckeFamily HeckeInverseAmplification HeckeDetectorSupportedWitness
open HeckeDetectorWitnessRows HeckeDetectorFiberPartition LocalMoment Marked830Assembly
open CenteredMomentDetectorPlainFiberSource CenteredMomentNaturalFixedRaySource ProbeHighRowFamily
local notation "O" => HeckeFamily.O
variable {Label Slot : Type} [Fintype Label] [Nonempty Label] [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_unmarked_from_buffered_maxima_uniform
    (base : Label→Character) (setup : DensityCountingSetup)
    (εm η : ℝ) (hεm : 0<εm) (hη : 0<η)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) :
    ∃J : ℕ,∀(dmin dmax τ ε e κw ηw : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*ηw)
    (hε : 0<ε) (hεsmall : ε≤1/1000) (he : 0<e) (he' : e<1/1000)
    (hκw : 0<κw) (hκw' : κw≤1) (hηw : 0≤ηw)
    (hbudget : 12*e*((22:ℝ)+2)+8*κw+2*ηw≤ε/2),
    ∃C : ℝ,0≤C ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀d : ℝ,dmin≤d → d≤dmax →
      ∀{anchor : Label→Character}{bad : Label→Ideal O}{W : ℝ→ℂ}{lo hi : ℝ},
      ∀B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W lo hi (Z^d),
      ∀a height : ℝ,∀i : ℕ,i≤I → 31/50≤2*a-1 → 2*a-1≤7/10 →
      0≤height → 2*Real.pi*((Z^d)^(τ/(2*dmax)))+(3*i:ℕ)*Z^τ≤height →
      ∀hχ : ∀u∈B.rows,∀j,(B.family u j).residue≠1,
      (∀u : B.rows,HeckeDetectorZeros.zeroMaximum (B.family u.val) (hχ u.val u.property)
        (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u : B.rows,a≤HeckeDetectorZeros.zeroMaximum (B.family u.val) (hχ u.val u.property)
        ((3*i:ℕ)*Z^τ)) →
      (∀u∈B.rows,∀j,(B.family u j).modulus.absNorm≤Z^d) →
      (B.rows.card:ℝ)≤C*(1+height)^J*(Z^d)^(Marked830.VariableSupply.density (2*a-1)+156*ε+εm+η) := by
  let D := FixedUnmarkedDictionary.ofBases base
  obtain ⟨J,C,hC,hcount⟩ := setup.actual_batch_count D εm η hεm hη hβ
  refine ⟨J,?_⟩
  intro dmin dmax τ ε e κw ηw I hdmin hdmax hτ hτzero hτheight hε hεsmall he he' hκw hκw' hηw hbudget
  obtain ⟨Z₀,hw⟩ := unmarked_batch_from_actual_maxima dmin dmax τ ε e κw ηw I
    hdmin hdmax hτ hτzero hτheight hε he he' hκw hκw' hηw hbudget
  obtain ⟨U₀,hU₀⟩ := eventually_atTop.mp hcount
  have hlarge : ∀ᶠ Z : ℝ in atTop,U₀≤Z^dmin :=
    (tendsto_rpow_atTop hdmin).eventually (eventually_ge_atTop U₀)
  refine ⟨C,hC,?_⟩
  filter_upwards [hlarge,eventually_ge_atTop Z₀,eventually_gt_atTop (1:ℝ)] with Z hlarge hZ₀ hZ
  refine ⟨hZ,?_⟩
  intro d hd hd' anchor bad W lo hi B a height i hiI ha0 ha hh hf hχ hnext hcurrent hmod
  have hthreshold : U₀≤Z^d := hlarge.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hd)
  have hc := hU₀ (Z^d) hthreshold
  by_cases hne : B.rows.Nonempty
  · have hcut := unmarkedCutoff_bounds (show 0≤2*a-1 by linarith) (show 2*a-1≤5/6 by linarith)
    have hcoeff : ∀u : B.rows,∀j I,idealCoeff (B.family u.val j) I=
        if (fun _:Label=>false) j then starRingEnd ℂ
          (idealCoeff ((D.data j).character ⟨u.val.val,u.val.property.1⟩) I)
        else idealCoeff ((D.data j).character ⟨u.val.val,u.val.property.1⟩) I := by
      intro u j I
      simpa only [Bool.false_eq_true,ite_false,D,FixedUnmarkedDictionary.data,
        FixedUnmarkedDictionary.ofBases,momentElement] using B.idealCoefficients u.val u.property j I
    obtain ⟨batch,hrows,hdata,hrev,hfamily⟩ := hw Z hZ₀ d hd hd' B.rows hne
      (fun u=>B.family u.val) (fun u=>hχ u.val u.property) D.data (fun _=>false) B.rowNorm hcoeff
      a i hiI (by linarith) (by linarith) hnext hcurrent (fun u=>hmod u.val u.property)
      (unmarkedCutoff (2*a-1)) hcut.1 hcut.2
    rw [←hrows]
    exact hc.2 a ε (Z^τ) ((Z^d)^(τ/(2*dmax))) height i (by linarith) (by linarith)
      hε.le hεsmall hh hf batch hdata
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero]
    exact mul_nonneg (mul_nonneg hC (by positivity)) (Real.rpow_nonneg (zero_lt_one.trans hc.1).le _)


end OAI.SevenEighths.Marked830ActualWeighted
#print axioms OAI.SevenEighths.Marked830ActualWeighted.actual_unmarked_from_buffered_maxima_uniform
end

/- Original module: Candidate.Target830.Marked.ActualMaxWeightedFixedMesh. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace OAI.SevenEighths.Marked830ActualWeighted
open OAI.SevenEighths.Cycle63ActualWeighted
open HeckeFamily HeckeInverseAmplification HeckeDetectorSupportedWitness
open HeckeDetectorWitnessRows HeckeDetectorFiberPartition LocalMoment Marked830Assembly
open CenteredMomentDetectorPlainFiberSource CenteredMomentNaturalFixedRaySource ProbeHighRowFamily
local notation "O" => HeckeFamily.O
variable {Label Slot : Type} [Fintype Label] [Nonempty Label] [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_max_weighted_from_buffered_maxima_fixedmesh
    (base anchor : Label→Character) (bad : Label→Ideal O)
    (hbadM : ∀j,bad j≤M)
    (hbad0 : ∀j,internalQ (bad j) (anchor j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (anchor j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (anchor j)≤Ideal.span {(72:O)})
    (setup : DensityCountingSetup) (W : ℝ→ℂ) (lo hi bΦ Δ εm binWidth η : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0<bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hbin : 0<binWidth) (hη : 0<η)
    (hΔ0 : 0≤Δ) (hΔ : Δ=0) (hεm : 0<εm)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤3/4+2*Δ) :
    ∃J : ℕ,∀(dmin dmax τ ε e κw ηw : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*ηw)
    (hε : 0<ε) (hεsmall : ε≤1/1000) (he : 0<e) (he' : e<1/1000)
    (hκw : 0<κw) (hκw' : κw≤1) (hηw : 0≤ηw)
    (hbudget : 12*e*((22:ℝ)+2)+8*κw+2*ηw≤ε/2),
    ∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀d : ℝ,dmin≤d → d≤dmax →
      ∀B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W lo hi (Z^d),
      ∀a mesh height : ℝ,∀i : ℕ,i≤I →
      31/50≤2*a-1 → 2*a-1≤7/10 →
      0≤ mesh → mesh≤Cycle63MarkedPlain.markedPlainMesh (3/4+2*Δ) εm → binWidth≤(2*a-1)/2 →
      (∀s∈B.slots,B.widths s≤ mesh) →
      0≤height → 2*Real.pi*((Z^d)^(τ/(2*dmax)))+(3*i:ℕ)*Z^τ≤height →
      (∀s∈B.slots,|B.relativeHeight s|≤height) → (∀u∈B.rows,|B.commonHeight u|≤height) →
      ∀hχ : ∀u∈B.rows,∀j,(B.family u j).residue≠1,
      (∀u : B.rows,HeckeDetectorZeros.zeroMaximum (B.family u.val) (hχ u.val u.property)
        (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u : B.rows,a≤HeckeDetectorZeros.zeroMaximum (B.family u.val) (hχ u.val u.property)
        ((3*i:ℕ)*Z^τ)) →
      (∀u∈B.rows,∀j,(B.family u j).modulus.absNorm≤Z^d) →
      (∀u∈B.rows,∀s∈B.slots,‖B.Q u s‖≤((Z^d)^(B.widths s))^((2*a-1)/2+binWidth)) →
      (∑u∈B.rows,(∏s∈B.slots,max 1 ‖B.Q u s‖)^2)≤
        C*(1+height)^J*
        (Z^d)^(Marked830.VariableSupply.density (2*a-1)+(2*a-1)*(∑s∈B.slots,B.widths s)-
          Marked830.VariableSupply.phi (2*a-1)*Marked830.VariableSupply.chosenWidth (2*a-1) (∑s∈B.slots,B.widths s)+
          156*ε+mesh+εm+2*binWidth*(∑s∈B.slots,B.widths s)+η) := by
  obtain ⟨Jm,hmarked⟩ := actual_weighted_from_buffered_maxima_fixedmesh
    (Slot:=Slot) base anchor bad hbadM hbad0 hbadTop hbad72 setup W lo hi bΦ Δ εm binWidth η
    hWs hW hbΦ hrad hbin hη hΔ0 hΔ hεm hβ hκβ
  obtain ⟨Ju,hunmarked⟩ := actual_unmarked_from_buffered_maxima_uniform (Slot:=Slot) M H hH base setup
    εm η hεm hη hβ
  refine ⟨Ju+Jm,?_⟩
  intro dmin dmax τ ε e κw ηw I hdmin hdmax hτ hτzero hτheight hε hεsmall he he' hκw hκw' hηw hbudget
  obtain ⟨Cm,hCm,hmarked⟩ := hmarked dmin dmax τ ε e κw ηw I hdmin hdmax hτ hτzero hτheight
    hε hεsmall he he' hκw hκw' hηw hbudget
  obtain ⟨Cu,hCu,hunmarked⟩ := hunmarked dmin dmax τ ε e κw ηw I hdmin hdmax hτ hτzero hτheight
    hε hεsmall he he' hκw hκw' hηw hbudget
  let J := Ju+Jm
  let C := Cu+Cm
  have hC : 0<C := by dsimp [C]; linarith
  refine ⟨(2:ℝ)^Fintype.card Slot*C,by positivity,?_⟩
  filter_upwards [hmarked,hunmarked] with Z hmarked hunmarked
  refine ⟨hmarked.1,?_⟩
  intro d hd hd' B a mesh height i hiI ha0 ha hmesh hmeshmax' hbin' hwm hh hf hv hchoice
    hχ hnext hcurrent hmod hQ
  let U := Z^d
  have hU : 1<U := Real.one_lt_rpow hmarked.1 (hdmin.trans_le hd)
  let Cnow := C*(1+height)^J
  have hCnow : 0<Cnow := by dsimp [Cnow]; positivity
  have hCu' : Cu*(1+height)^Ju≤Cnow := by
    apply mul_le_mul (show Cu≤C by dsimp [C]; linarith)
      (pow_le_pow_right₀ (by linarith : 1≤1+height) (by dsimp [J]; omega)) (by positivity) hC.le
  have hCm' : Cm*(1+height)^Jm≤Cnow := by
    apply mul_le_mul (show Cm≤C by dsimp [C]; linarith)
      (pow_le_pow_right₀ (by linarith : 1≤1+height) (by dsimp [J]; omega)) (by positivity) hC.le
  let loss := 156*ε+mesh+εm+2*binWidth*(∑s∈B.slots,B.widths s)+η
  have hS : 0≤∑s∈B.slots,B.widths s := Finset.sum_nonneg (fun s hs=>(B.widthsPositive s hs).le)
  have hcount : (B.rows.card:ℝ)≤Cnow*U^(Marked830.VariableSupply.density (2*a-1)+loss) := by
    have he := hunmarked.2 d hd hd' B a height i hiI ha0 ha hh hf hχ hnext hcurrent hmod
    apply he.trans
    apply mul_le_mul hCu' (Real.rpow_le_rpow_of_exponent_le hU.le _)
      (Real.rpow_nonneg (zero_lt_one.trans hU).le _) hCnow.le
    dsimp [loss]
    nlinarith [mul_nonneg hbin.le hS]
  have hsub (selected : Finset Slot) (hs : selected⊆B.slots) (hne : selected.Nonempty) :
      (∑u∈B.rows,‖∏s∈selected,B.Q u s‖^2)≤Cnow*
        U^(Marked830.VariableSupply.density (2*a-1)+(2*a-1)*(∑s∈selected,B.widths s)-
          Marked830.VariableSupply.phi (2*a-1)*Marked830.VariableSupply.chosenWidth (2*a-1) (∑s∈selected,B.widths s)+loss) := by
    let Bs := B.restrictSlots M H hH selected hs
    have hL : 0<∑s∈selected,B.widths s := Finset.sum_pos (fun s h=>B.widthsPositive s (hs h)) hne
    have he := hmarked.2 d hd hd' Bs a mesh height i hiI ha0 ha hmesh hmeshmax' hbin'
      (fun s h=>hwm s (hs h)) hL hh hf (fun s h=>hv s (hs h)) hchoice hχ hnext hcurrent hmod
      (fun u hu s h=>hQ u hu s (hs h))
    apply he.trans
    apply mul_le_mul hCm' (Real.rpow_le_rpow_of_exponent_le hU.le _)
      (Real.rpow_nonneg (zero_lt_one.trans hU).le _) hCnow.le
    have hsum : (∑s∈selected,B.widths s)≤∑s∈B.slots,B.widths s :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun s hs _=>(B.widthsPositive s hs).le)
    change _≤_
    dsimp only [loss,Bs,NaturalBatch.restrictSlots]
    nlinarith [mul_le_mul_of_nonneg_left hsum (show 0≤2*binWidth by positivity)]
  have hsub' (selected : Finset Slot) (hs : selected⊆B.slots) (hne : selected.Nonempty) :
      (∑u∈B.rows,‖∏s∈selected,B.Q u s‖^2)≤Cnow*
        U^(Marked830.VariableSupply.density (2*a-1)+(2*a-1)*(∑s∈selected,B.widths s)-
          ExactMarkedGain.gain (Marked830.VariableSupply.phi (2*a-1))
            (Marked830.VariableSupply.cap (2*a-1)) (Marked830.VariableSupply.plainCap (2*a-1))
            (∑s∈selected,B.widths s)+loss) := by
    convert hsub selected hs hne using 1
    congr 2
    dsimp [ExactMarkedGain.gain,Marked830.VariableSupply.chosenWidth,
      Marked830.VariableSupply.inverseWidth,Marked830.VariableSupply.plainWidth]
    ring
  have he := ExactMarkedGain.max_weighted_row_sum_of_nonempty B.rows B.slots B.Q B.widths U Cnow
    (Marked830.VariableSupply.density (2*a-1)) (2*a-1)
    (Marked830.VariableSupply.phi (2*a-1)) (Marked830.VariableSupply.cap (2*a-1))
    (Marked830.VariableSupply.plainCap (2*a-1)) loss
    (fun s hs=>(B.widthsPositive s hs).le) hU.le hCnow.le
    (Marked830.VariableSupply.phi_nonneg ha0 ha)
    (Marked830.VariableSupply.phi_le_delta ha0 ha)
    (Marked830.VariableSupply.cap_bounds ha0 ha).1.le
    (Marked830.VariableSupply.plainCap_nonneg ha0 ha) hcount hsub'
  have hN : (2:ℝ)^B.slots.card≤(2:ℝ)^Fintype.card Slot :=
    pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ B.slots)
  have he' : (∑u∈B.rows,(∏s∈B.slots,max 1 ‖B.Q u s‖)^2)≤
      (2:ℝ)^B.slots.card*Cnow*U^(Marked830.VariableSupply.density (2*a-1)+(2*a-1)*
        (∑s∈B.slots,B.widths s)-Marked830.VariableSupply.phi (2*a-1)*
          Marked830.VariableSupply.chosenWidth (2*a-1) (∑s∈B.slots,B.widths s)+loss) := by
    convert he using 1
    congr 2
    dsimp [ExactMarkedGain.gain,Marked830.VariableSupply.chosenWidth,
      Marked830.VariableSupply.inverseWidth,Marked830.VariableSupply.plainWidth]
    ring
  apply he'.trans
  calc
    _≤(2:ℝ)^Fintype.card Slot*Cnow*U^(Marked830.VariableSupply.density (2*a-1)+(2*a-1)*
        (∑s∈B.slots,B.widths s)-Marked830.VariableSupply.phi (2*a-1)*Marked830.VariableSupply.chosenWidth (2*a-1) (∑s∈B.slots,B.widths s)+loss) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hN hCnow.le)
        (Real.rpow_nonneg (zero_lt_one.trans hU).le _)
    _=_ := by
      dsimp only [Cnow,U,loss]
      congr 1 <;> ring

end OAI.SevenEighths.Marked830ActualWeighted
#print axioms OAI.SevenEighths.Marked830ActualWeighted.actual_max_weighted_from_buffered_maxima_fixedmesh
end

/- Original module: Candidate.Target830.Marked.WholeBufferedMaxFixedMesh. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.Marked830Plain
open OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter HeckeFamily HeckeInverseAmplification HeckeDetectorZeros
open ProbeHighRowFamily LocalMoment Cycle63Moment HeckeDetectorFiberPartition
open CenteredMomentPrimeSlot CenteredMomentDetectorPlainFiberSource
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentDetectorEnergyInitialState
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_whole_max_weighted_fixedmesh {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (η η₀ : Character) (bad : WholeSourceIndex M H→Ideal O)
    (hbadM : ∀j,bad j≤M)
    (hbad0 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≤Ideal.span {(72:O)})
    (setup : DensityCountingSetup) (W : ℝ→ℂ) (lo hi bΦ Δ εm binWidth ηloss : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0<bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hbin : 0<binWidth) (hη : 0<ηloss)
    (hΔ0 : 0≤Δ) (hΔ : Δ=0) (hεm : 0<εm)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤3/4+2*Δ) :
    ∃J : ℕ,∀(dmin dmax τ ε e κw ηw : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*ηw)
    (hε : 0<ε) (hεsmall : ε≤1/1000) (he : 0<e) (he' : e<1/1000)
    (hκw : 0<κw) (hκw' : κw≤1) (hηw : 0≤ηw)
    (hbudget : 12*e*((22:ℝ)+2)+8*κw+2*ηw≤ε/2),
    ∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀d : ℝ,dmin≤d → d≤dmax →
      ∀(rows : Finset FreeRow)(slots : Finset Slot)(w σ v : Slot→ℝ)
        (t : FreeRow→ℝ)(θ : Slot→RayQuotient.Characters M H),
      (∀s∈slots,0<w s) → (∀s∈slots,lo≤σ s) → (∀s∈slots,σ s≤hi) →
      (∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤Z^d) →
      (∀u∈rows,‖ConcreteTraceCRT.eisEmbedding u.val‖^2≤Z^d) →
      (∀u∈rows,∀j,initialKeep (cleanWholeBase M H hH η η₀ j)
        (internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)) u.val) →
      (∀s∈slots,∀j,
        ((DetectorDictionaryInverseRawInitialGates.deletedBase
          (momentData (cleanWholeBase M H hH η η₀ j))).modulus.absNorm:ℝ)<(Z^d)^(w s)) →
      ∀(χ : FreeRow→Character)(holes : FreeRow→Ideal O),
      (∀u∈rows,holes u≠0) →
      (∀u∈rows,∀K,idealCoeff (χ u) K=
        idealCoeff (excluded (naturalRow η u.val u.property.1).character (holes u)) K) →
      ∀a mesh height : ℝ,∀i : ℕ,i≤I →
      31/50≤2*a-1 → 2*a-1≤7/10 →
      0≤ mesh → mesh≤ markedPlainMesh (3/4+2*Δ) εm → binWidth≤(2*a-1)/2 →
      (∀s∈slots,w s≤ mesh) →
      0≤height → 2*Real.pi*((Z^d)^(τ/(2*dmax)))+(3*i:ℕ)*Z^τ≤height →
      (∀s∈slots,|v s|≤height) → (∀u∈rows,|t u|≤height) →
      ∀hχ : ∀u∈rows,∀j,(wholeSourceFamily M H hH η₀ (χ u) j).residue≠1,
      (∀u : rows,zeroMaximum (wholeSourceFamily M H hH η₀ (χ u.val)) (hχ u.val u.property)
        (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u : rows,a≤zeroMaximum (wholeSourceFamily M H hH η₀ (χ u.val)) (hχ u.val u.property)
        ((3*i:ℕ)*Z^τ)) →
      (∀u∈rows,∀j,(wholeCleanFamily M H hH η η₀ u j).modulus.absNorm≤Z^d) →
      (∀u∈rows,∀s∈slots,‖wholeCleanSlot M H hH η η₀ W (Z^d) w σ v t θ u s‖
        ≤((Z^d)^(w s))^((2*a-1)/2+binWidth)) →
      (∑u∈rows,(∏s∈slots,max 1 ‖wholeCleanSlot M H hH η η₀ W (Z^d) w σ v t θ u s‖)^2)≤
        C*(1+height)^J*
        (Z^d)^(Marked830.VariableSupply.density (2*a-1)+(2*a-1)*(∑s∈slots,w s)-
          Marked830.VariableSupply.phi (2*a-1)*Marked830.VariableSupply.chosenWidth (2*a-1) (∑s∈slots,w s)+
          156*ε+mesh+εm+2*binWidth*(∑s∈slots,w s)+ηloss) := by
  obtain ⟨J,hcount⟩ :=
    Marked830ActualWeighted.actual_max_weighted_from_buffered_maxima_fixedmesh (Slot:=Slot) M H hH
      (cleanWholeBase M H hH η η₀) (wholeSourceAnchor M H hH η₀) bad
      hbadM hbad0 hbadTop hbad72 setup W lo hi bΦ Δ εm binWidth ηloss
      hWs hW hbΦ hrad hbin hη hΔ0 hΔ hεm hβ hκβ
  refine ⟨J,?_⟩
  intro dmin dmax τ ε e κw ηw I hdmin hdmax hτ hτzero hτheight hε hεsmall he he' hκw hκw' hηw hbudget
  obtain ⟨C,hC,hcount⟩ := hcount dmin dmax τ ε e κw ηw I hdmin hdmax hτ hτzero hτheight
    hε hεsmall he he' hκw hκw' hηw hbudget
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount] with Z hcount
  refine ⟨hcount.1,?_⟩
  intro d hd hd' rows slots w σ v t θ hw hlo hhi hrow hnorm hkeep hlarge
    χ holes hholes hcoeff a mesh height i hiI ha0 ha hmesh hmeshmax hbin' hwm hh hf hv ht
    hχ hnext hcurrent hmod hQ
  let B := wholeNaturalBatch M H hH η η₀ bad W lo hi (Z^d) hWs rows slots w σ v t θ
    hw hlo hhi hrow hnorm hkeep hlarge
  have he (u : FreeRow) (hu : u∈rows) :=
    whole_family_clean_maximum M H hH η η₀ (χ u) u.val u.property.1 (holes u)
      (hholes u hu) (hcoeff u hu) (hχ u hu)
  let hc : ∀u∈B.rows,∀j,(B.family u j).residue≠1 := fun u hu=>(he u hu).choose
  have hmax (u : FreeRow) (hu : u∈rows) (T : ℝ) :
      zeroMaximum (B.family u) (hc u hu) T=
      zeroMaximum (wholeSourceFamily M H hH η₀ (χ u)) (hχ u hu) T :=
    (he u hu).choose_spec T
  exact hcount.2 d hd hd' B a mesh height i hiI ha0 ha hmesh hmeshmax hbin' hwm hh hf hv ht hc
    (fun u=>by rw [hmax u.val u.property];exact hnext u)
    (fun u=>by rw [hmax u.val u.property];exact hcurrent u) hmod hQ

end
end OAI.SevenEighths.Marked830Plain
#print axioms OAI.SevenEighths.Marked830Plain.actual_whole_max_weighted_fixedmesh
end

/- Original module: Candidate.Target830.Marked.PhysicalRescale. -/
section

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace Marked830.VariableSupply

theorem rescaled_exact_marked_power_padded
    (U Y d dmax pad delta q S loss : ℝ)
    (hU : 1 ≤ U) (hY : 0 < Y) (hd : 0 < d) (hdmax : d ≤ dmax)
    (hbase : U^d=Y*U^pad) (hloss : 0 ≤ loss) :
    (U^d)^(density delta+q*(S/d)-phi delta*chosenWidth delta (S/d)+loss) ≤
      U^(q*S-physicalGain delta S d+dmax*loss+pad*density delta)*Y^(density delta) := by
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hYeq : Y=U^(d-pad) := by
    rw [Real.rpow_sub hUp]
    apply (eq_div_iff (Real.rpow_pos_of_pos hUp pad).ne').mpr
    exact hbase.symm
  have hgain := physicalGain_rescale delta S d hd
  have hexp : d*(density delta+q*(S/d)-phi delta*chosenWidth delta (S/d)+loss) =
      q*S-physicalGain delta S d+d*loss+d*density delta := by
    have hcancel : d*(S/d)=S := mul_div_cancel₀ _ hd.ne'
    linear_combination q*hcancel-hgain
  rw [←Real.rpow_mul hUp.le,hexp,hYeq,←Real.rpow_mul hUp.le,←Real.rpow_add hUp]
  apply Real.rpow_le_rpow_of_exponent_le hU
  have hh := mul_le_mul_of_nonneg_right hdmax hloss
  linarith

end Marked830.VariableSupply
#print axioms Marked830.VariableSupply.rescaled_exact_marked_power_padded
end

/- Original module: Candidate.Target830.Marked.WholePaddedCoreFixedMesh. -/
section

set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OAI.SevenEighths.Marked830Plain
open OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter HeckeFamily HeckeInverseAmplification HeckeDetectorZeros
open ProbeHighRowFamily LocalMoment Cycle63Moment HeckeDetectorFiberPartition
open CenteredMomentPrimeSlot CenteredMomentDetectorPlainFiberSource
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentDetectorEnergyInitialState
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- Actual padded core source count in physical slot widths. The finite
exception set, modulus padding, embedding cap, inverse conductor threshold,
and both buffered-maximum transports are proved inside this adapter. -/
theorem actual_whole_padded_core_weighted_fixedmesh {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (η η₀ : Character) (bad : WholeSourceIndex M H→Ideal O)
    (hbadM : ∀j,bad j≤ M)
    (hbad0 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≤ Ideal.span {(72:O)})
    (setup : DensityCountingSetup) (W : ℝ→ℂ) (lo hi bΦ Δ εm binWidth ηloss : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0< bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hbin : 0< binWidth) (hη : 0<ηloss)
    (hΔ0 : 0≤Δ) (hΔ : Δ=0) (hεm : 0<εm)
    (hβ : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤3/4+2*Δ) :
    ∃E : Finset FreeRow,∃J : ℕ,∀(dmin dmax τ ε e κw ηw pad wmin : ℝ) (I : ℕ)
    (hpad : 0< pad) (hwmin : 0< wmin) (hdmin : 0< dmin) (hdmax : dmin≤ dmax) (hτ : 0<τ)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*ηw)
    (hε : 0<ε) (hεsmall : ε≤1/1000) (he : 0< e) (he' : e<1/1000)
    (hκw : 0<κw) (hκw' : κw≤1) (hηw : 0≤ηw)
    (hbudget : 12*e*((22:ℝ)+2)+8*κw+2*ηw≤ε/2),
      ∃C : ℝ,0< C ∧
      ∀ᶠU : ℝ in atTop,1< U ∧ ∀Y d : ℝ,dmin≤ d → d≤ dmax → U^d=Y*U^pad →
      ∀(rows : Finset FreeRow)(slots : Finset Slot)(w σ v : Slot→ℝ)
        (t : FreeRow→ℝ)(θ : Slot→RayQuotient.Characters M H),
      (∀u∈rows,u∉E) → (∀u∈rows,rowNorm u≤ Y) →
      (∀s∈slots,wmin≤ w s) → (∀s∈slots,lo≤σ s) → (∀s∈slots,σ s≤ hi) →
      ∀(χ : FreeRow→Character)(holes : FreeRow→Ideal O),
      (∀u∈rows,holes u≠0) →
      (∀u∈rows,∀K,idealCoeff (χ u) K=
        idealCoeff (excluded (naturalRow η u.val u.property.1).character (holes u)) K) →
      ∀a mesh height : ℝ,∀i : ℕ,i≤ I →
      31/50≤2*a-1 → 2*a-1≤7/10 →
      0≤ mesh → mesh≤ markedPlainMesh (3/4+2*Δ) εm → binWidth≤(2*a-1)/2 →
      (∀s∈slots,w s≤ mesh*d) →
      0≤ height → 2*Real.pi*((U^d)^(τ/(2*dmax)))+(3*i:ℕ)*U^τ≤ height →
      (∀s∈slots,|v s|≤ height) → (∀u∈rows,|t u|≤ height) →
      ∀hχ : ∀u∈rows,∀j,(wholeSourceFamily M H hH η₀ (χ u) j).residue≠1,
      (∀u : rows,zeroMaximum (wholeSourceFamily M H hH η₀ (χ u.val)) (hχ u.val u.property)
        (3*(i+1:ℕ)*U^τ)< a+2*e) →
      (∀u : rows,a≤ zeroMaximum (wholeSourceFamily M H hH η₀ (χ u.val)) (hχ u.val u.property)
        ((3*i:ℕ)*U^τ)) →
      (∀u∈rows,∀s∈slots,‖wholeCleanSlot M H hH η η₀ W U w σ v t θ u s‖
        ≤(U^(w s))^((2*a-1)/2+binWidth)) →
      (∑u∈rows,(∏s∈slots,max 1 ‖wholeCleanSlot M H hH η η₀ W U w σ v t θ u s‖)^2)≤
        C*(1+height)^J*
        (U^((2*a-1+2*binWidth)*(∑s∈slots,w s)-Marked830.VariableSupply.physicalGain (2*a-1) (∑s∈slots,w s) d+
          dmax*(156*ε+mesh+εm+ηloss)+pad*Marked830.VariableSupply.density (2*a-1))*
          Y^Marked830.VariableSupply.density (2*a-1)) := by
  obtain ⟨E,hE⟩ := whole_core_exception_set M H hH η η₀ bad hbad0 hbadTop hbad72
  obtain ⟨J,hcount⟩ := actual_whole_max_weighted_fixedmesh (Slot:=Slot) M H hH
    η η₀ bad hbadM hbad0 hbadTop hbad72 setup W lo hi bΦ Δ εm binWidth ηloss
    hWs hW hbΦ hrad hbin hη hΔ0 hΔ hεm hβ hκβ
  refine ⟨E,J,?_⟩
  intro dmin dmax τ ε e κw ηw pad wmin I hpad hwmin hdmin hdmax hτ hτzero hτheight
    hε hεsmall he he' hκw hκw' hηw hbudget
  obtain ⟨C,hC,hcount⟩ := hcount dmin dmax τ ε e κw ηw I hdmin hdmax hτ hτzero hτheight
    hε hεsmall he he' hκw hκw' hηw hbudget
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount,eventually_whole_core_norm_caps M H hH η η₀ pad hpad,
    eventually_whole_core_inverse_large M H hH η η₀ wmin hwmin]
    with U hcount hnorms hlarge
  refine ⟨hcount.1,?_⟩
  intro Y d hd hd' hbase rows slots w σ v t θ hrows hrow hw hlo hhi
    χ holes hholes hcoeff a mesh height i hiI ha0 ha hmesh hmeshmax hbin' hwm hh hf hv ht
    hχ hnext hcurrent hQ
  have hUp : 0< U := zero_lt_one.trans hcount.1
  have hdp : 0< d := hdmin.trans_le hd
  have hscale (s : Slot) : (U^d)^(w s/d)=U^(w s) := by
    rw [←Real.rpow_mul hUp.le,mul_div_cancel₀ _ hdp.ne']
  have hYs : 0< Y*U^pad := hbase ▸ Real.rpow_pos_of_pos hUp d
  have hY : 0< Y := (mul_pos_iff.mp hYs).elim (fun h=>h.1)
    (fun h=>False.elim ((not_lt_of_ge (Real.rpow_nonneg hUp.le _)) h.2))
  have he := hcount.2 d hd hd' rows slots (fun s=>w s/d) σ v t θ
    (fun s hs=>div_pos (hwmin.trans_le (hw s hs)) hdp) hlo hhi
    (fun u hu=>by rw [hbase];exact (hnorms.2 Y u (hrow u hu)).1)
    (fun u hu=>by rw [hbase];exact (hnorms.2 Y u (hrow u hu)).2.1)
    (fun u hu=>(hE u).mp (hrows u hu))
    (fun s hs j=>by rw [hscale];exact hlarge.2 (w s) (hw s hs) j)
    χ holes hholes hcoeff a mesh height i hiI ha0 ha hmesh hmeshmax hbin'
    (fun s hs=>(div_le_iff₀ hdp).mpr (hwm s hs)) hh hf hv ht hχ hnext hcurrent
    (fun u hu j=>by rw [hbase];exact (hnorms.2 Y u (hrow u hu)).2.2 j)
    (fun u hu s hs=>by rw [wholeCleanSlot_rescale M H hH η η₀ W U d hUp hdp.ne',hscale];exact hQ u hu s hs)
  simp only [wholeCleanSlot_rescale M H hH η η₀ W U d hUp hdp.ne',←Finset.sum_div] at he
  have heq : Marked830.VariableSupply.density (2*a-1)+(2*a-1)*((∑s∈slots,w s)/d)-
      Marked830.VariableSupply.phi (2*a-1)*Marked830.VariableSupply.chosenWidth (2*a-1) ((∑s∈slots,w s)/d)+
      156*ε+mesh+εm+2*binWidth*((∑s∈slots,w s)/d)+ηloss =
      Marked830.VariableSupply.density (2*a-1)+(2*a-1+2*binWidth)*((∑s∈slots,w s)/d)-
        Marked830.VariableSupply.phi (2*a-1)*Marked830.VariableSupply.chosenWidth (2*a-1) ((∑s∈slots,w s)/d)+(156*ε+mesh+εm+ηloss) := by
    ring
  rw [heq] at he
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Marked830.VariableSupply.rescaled_exact_marked_power_padded U Y d dmax pad
    (2*a-1) (2*a-1+2*binWidth) (∑s∈slots,w s) (156*ε+mesh+εm+ηloss)
    hcount.1.le hY hdp hd' hbase (by positivity)

end
end OAI.SevenEighths.Marked830Plain
#print axioms OAI.SevenEighths.Marked830Plain.actual_whole_padded_core_weighted_fixedmesh
end
