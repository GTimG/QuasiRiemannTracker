/- The selected low frequency columns of the final daughters of the LOW children of a step with the second step: the old
rows with the allowance of their labels, plus the returned HIGH parts of the second step, paid by the facts of the
first level. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.LowChildSelectedFacts
import Candidate.Cycle63.Physical.InitialMass.LowChildAllowancePayment
import Candidate.Cycle63.Physical.InitialMass.LowChildJoinedArith
import Candidate.Cycle63.Physical.InitialMass.LowChildReturnedPart
import Candidate.Cycle63.Physical.InitialMass.LowChildJoinedTotal
import Candidate.Cycle63.Physical.InitialMass.LowChildJoinedShift
import Candidate.Cycle63.Physical.InitialMass.LowChildSideExponent
import Candidate.Cycle63.Physical.InitialMass.LowChildJoinedRow
import Candidate.Cycle63.Physical.InitialMass.DepthTwoReturnedPayment
import Candidate.Cycle63.Physical.InitialMass.SecondChildLowPayment
import Candidate.Cycle63.Moment.LowBranch.TwoLevelBridge

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentSourceLiveColumn
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceMass CenteredMomentRankinRadical CenteredMomentFirstDiscardedEnergy
open CenteredMomentLogDyadic
open CenteredMomentCommonPairedSource
open CenteredMomentFirstChildProfileControl
open Cycle63FinalNatural Cycle63Moment.LowBranch
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open CenteredMomentCommonLinearNormalization CenteredMomentSourceLiveColumn
open Cycle63Moment
open Cycle63FinalLow
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle63FinalProfiles

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal HeckeFamily.O) [NeZero M]
variable (H : Subgroup (HeckeFamily.O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

attribute [local instance] lowChildSelectedDecidable

attribute [local irreducible] actualSecondLabels

/-- The degree `J` in the height `T` of the payment of the returned parts of rows, for every dictionary and character
indexed by `Base`, the bound `B` of the norms, the loss `lossPay` and the width `width` of the bins: the degree of
`depth_two_returned_payment`, zero when the parameters are not admissible. -/
def returnedHeightDegree (Base : Type) [Fintype Base] (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (B lossPay width : ℝ) : ℕ :=
  if h : 0 ≤ B ∧ 0 < lossPay ∧ 0 < width then
    Classical.choose (depth_two_returned_payment.{0} (Base := Base) M H hH B lossPay width h.1 h.2.1 h.2.2)
  else 0

set_option linter.unusedVariables false in
/-- The selected low frequency columns of the final daughters of the LOW children of a step with the second step are
paid by the finite supported label budget, with the allowance of the labels and the returned HIGH parts of the second
step: the bound of `LowSelectedStmt` for the units `unit = 1`, the frequency losses at most `ωmax`, the exponent
`lowSideExponent` of the labels (the exponent of the old region and the cone surplus) and the presentation `Presented`
of the children. The old part of a row is paid by the budget of the labels with the allowance `lowAllowance`; the
returned part of a row is paid, together with the other rows, by `depth_two_returned_payment`, with the target exponent
shifted by the side bound `p + exponent - log N(seed₀)` of the labels.

The hypotheses are: `hfixed`, the bound of the columns of one final daughter with the second step, at the rate `rate`
of the padding, the reflection loss `εX`, the allowance of the labels and the returned part (the rows 1-4 on
`two_level_low_daughter`, see `two_level_low_fixed_columns`); `hfacts`, the facts of the first level that pay the
returned parts (`LowReturnedFactsStmt`); `hPres`, the zero height `Tz` of a presented child lies in `[0, Z^τT]`; `hJτ`,
the degree `J` of the height in the payment of the returned parts (`returnedHeightDegree`) satisfies `J τT ≤ εlabels/6`;
and `hrate`, `hεX`, the rate and the reflection loss of the daughters are absorbed in the rate `lowRate` of the ledger,
`rate ≤ lowRate` and `εX ≤ (lowRate - rate) εpad Mmin`. The bound `hfixed` is used for the children presented by
`Presented` whose multipliers have norm at most `Z^(Mcap + 5 Bnorm + ε + 1)` (a fact of the first level), and its
returned records have the label cap `Bret ≥ Bnorm`. -/
theorem lowSelectedStmt_joined [Led : Cycle63.AffineLedger] [IsTwoLevelFirstStep Led] {α : Type} [Fintype α]
    [DecidableEq α] {Base : Type} [Fintype Base]
    (W : ℝ→ℂ) (B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d : ℝ)
    (bs εwidth εpad Mmin εshell : ℝ) (hεpad : 0≤εpad) (heshell : 0≤εshell) (N : ℕ) (Cs supply εv Bnorm εlabels : ℝ)
    (hsupply : 0<supply) (hev : 0<εv) (hBnorm : 0≤Bnorm) (hel : 0<εlabels)
    (ωmax rate εX : ℝ) (base : Character → Base → Character) (lossFloor gridSlack ampSlack : ℝ)
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop) (Bret : ℝ) (hBret : Bnorm≤Bret)
    (τT : ℝ) (hPres : ∀ η Z (st : NaturalState Z Bmask 2) v Tz, Presented η Z st v Tz → 0≤Tz ∧ Tz≤Z^τT)
    (hJτ : (returnedHeightDegree Base M H hH Bret (εlabels/6) (εlabels/(6*(3+4*Bret))) : ℝ)*τT ≤ εlabels/6)
    (hrate : rate≤Cycle63.AffineLedger.lowRate)
    (hεX : εX≤(Cycle63.AffineLedger.lowRate-rate)*(εpad*Mmin))
    (hfixed : LowFixedColumnsStmt (α:=α) M H hH W B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs εwidth εpad
      Mmin εshell N Cs (fun u om _ => u=1 ∧ om≤ωmax) True rate εX
      (fun Z C₁ D₁ C₂ D₂ E₂ => lowAllowance Z C₁ D₁ C₂ D₂ E₂) base Bret lossFloor gridSlack ampSlack
      (fun η Z s v T => Presented η Z s v T ∧ ((Ideal.span {v}).absNorm:ℝ)≤Z^(Mcap+5*Bnorm+ε+1)))
    (hfacts : LowReturnedFactsStmt (α:=α) M H hH W B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs εwidth
      εpad Mmin εshell N Cs supply εv Bnorm εlabels (fun u om _ => u=1 ∧ om≤ωmax) lowSideExponent Presented lossFloor
      gridSlack ampSlack) :
    LowSelectedStmt (α:=α) M H hH W B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs εwidth εpad Mmin εshell N
      Cs supply εv Bnorm εlabels (fun u om _ => u=1 ∧ om≤ωmax) lowSideExponent Presented := by
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨degree,Sp,Kcls,Cg,hCg,hbound⟩ := hfixed η₀ Q hQM hQ0 hQt hQ72
  have hfb := hfacts η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Capre,εA,hCapre,hεA,hfev⟩ := hfb
  obtain ⟨K₀,hK₀,hpaidev⟩ := eventual_selected_low_allowance_paid N supply εv Bnorm εlabels hsupply hev hBnorm hel
  have hmassev := eventual_actual_child_low_mass_payment N supply εv hsupply hev
  have hlossPay : (0:ℝ)<εlabels/6 := by positivity
  have hBret0 : 0≤Bret := hBnorm.trans hBret
  have hwidthPay : (0:ℝ)<εlabels/(6*(3+4*Bret)) := by positivity
  have hex := depth_two_returned_payment.{0} (Base := Base) M H hH Bret (εlabels/6) (εlabels/(6*(3+4*Bret)))
    hBret0 hlossPay hwidthPay
  have hJ : returnedHeightDegree Base M H hH Bret (εlabels/6) (εlabels/(6*(3+4*Bret)))=Classical.choose hex := by
    unfold returnedHeightDegree
    split
    · rfl
    · rename_i hc
      exact absurd ⟨hBret0,hlossPay,hwidthPay⟩ hc
  obtain ⟨Cret,hCret,hretpay⟩ := Classical.choose_spec hex (base η₀) η₀
  have hτJ := hJτ
  rw [hJ] at hτJ
  generalize Classical.choose hex=J at hτJ hretpay
  have hKmax : 0 ≤ max Kcls 0 := le_max_right _ _
  refine ⟨degree,Sp,Cg*(K₀+Cret*2^J*Capre*max Kcls 0),
    mul_pos hCg (add_pos_of_pos_of_nonneg hK₀ (by positivity)),?_⟩
  filter_upwards [hbound,hfev,hpaidev,hmassev] with Z hz hfz hzpaid hmz
  refine ⟨hzpaid.1,?_⟩
  intro hZone s θ w σ freq v height mesh aLow i hcard hmass hsupply' hm hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh unit Mrow omega ξ
    hMmin hAdm hω hξ hMcap' hfit hzslot haff Label _ reflected second first hf heq Rfirst alloc χfirst tfirst halloc
    childSrc R seed K Tsec reserve hseed hw₁ hw₂ hsource Tfirst p exponent hTfirst hp seed₀ hs₀ hs₀0
    hinj hfirstseed hfirstproj hfirstnorm hrad hgeom hfirstshell rows hU box hbox label cell amp q g
    hC₁ hD₁ hC₂ hD₂ hU₂ hEeq hKeq hRadius hωeq χ hP hPN st src divisorSeed hE₂ hdivisor Ds T pad hT hDs
    p₀ hp₁ hp₂ hallow hcaps left₁ u₀ unit₁ Tz hleft hu₀ hdict mult hpres low zs weight hnonneg hkeep hweight mass
    physical loss hphysical hmass0 hmasscap c error
  have hZ0 : 0<Z := zero_lt_one.trans hZone
  obtain ⟨hunit,hωmax⟩ := hAdm
  have hfr := hfz.2 hZone s θ w σ freq v height mesh aLow i hcard hmass hsupply' hm hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh unit Mrow omega ξ
    hMmin ⟨hunit,hωmax⟩ hω hξ hMcap' hfit hzslot haff reflected second first hf heq Rfirst alloc χfirst tfirst
    halloc R seed K Tsec reserve hseed hw₁ hw₂ hsource Tfirst p exponent hTfirst hp seed₀ hs₀ hs₀0
    hinj hfirstseed hfirstproj hfirstnorm hrad hgeom hfirstshell rows hU box hbox q g
    hC₁ hD₁ hC₂ hD₂ hU₂ hEeq hKeq hRadius hωeq χ hP hPN divisorSeed hE₂ hdivisor Ds T pad hT hDs
    p₀ hp₁ hp₂ hallow hcaps left₁ u₀ unit₁ Tz hleft hu₀ hdict hpres
  obtain ⟨small₁,mfreq,A₁,a₁,γ₁,κ,Lmax,hX1,hpre,hF3,hγ,hscale,hF6,hF7,hF9,hmultN⟩ := hfr
  have hrowf := fun r : rows => hz.2 hZone s θ w σ freq v height mesh aLow i hcard hmass hm hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh unit Mrow omega ξ hMmin
    ⟨hunit,hωmax⟩ hω hξ hMcap' hfit hzslot haff (q r) (g r) (χ r) (hP r) (hPN r) (divisorSeed r) (hE₂ r)
    (hdivisor r) Ds T pad hT hDs p₀ hp₁ hp₂ (hallow r) (hcaps r) (mult r) Tz
    (fun W' hW' => ⟨hpres r W' hW',hmultN r⟩)
  choose Ret hRet0 hRetcl hRowbd using hrowf
  have hPr := fun r : rows => (hRetcl r).exists_part
  choose Pr hPrscale hPrloss hPrlen hPramp hPrcard hPrRet using hPr
  -- the cell of the parent
  have hM1 : (0:ℝ)<unit := by rw [hunit]; exact one_pos
  obtain ⟨hc₁,hc₂,-,hc₄⟩ := Cycle63.AffineLedger.originalCell_mem
    (show Cycle63.AffineLedger.slotFloor ≤ (∑ j,Real.logb Z (s.P j))/unit ∧
        (∑ j,Real.logb Z (s.P j))/unit ≤ Cycle63.AffineLedger.slotTop from
      ⟨(le_div_iff₀ hM1).mpr hzslot.1,(div_le_iff₀ hM1).mpr hzslot.2⟩)
  have hcell0 := Cycle63.AffineLedger.cellUpper_bounds hc₁ hc₂
  have hbwin : Cycle63.Optimization.firstCellTop ≤ cell ∧ cell ≤ Cycle63.Optimization.slotTop :=
    cell_range hcell0
  -- the quantities of the rows
  let target : ℝ := unit*Cycle63.Optimization.fixedDeletion cell
  let E₀ : ℝ := loss+amp+εv+Bnorm*εshell+pad+2*ε*d*(Fintype.card α:ℝ)
  let σbar : ℝ := p+exponent-Real.logb Z (seed₀.absNorm:ℝ)
  let E₀' : ℝ := E₀+σbar
  let X := fun r : rows=>actualHighCoordinates reflected left₁ second (first r.val.1) (label r).1.1 (label r).1.2
    (label r).2.val Z Mrow (Real.logb Z (volume s)) amp ξ reserve ε
  let Wt := fun r : rows=>Z^(E₀+X r 0+Cycle63.AffineLedger.q*(target+mesh))
  -- the constants of the bound
  let fixed := (2*b^2*Cs^(4*N))*QuadraticInitialBound.diagonalControl ballProfile*(p₀.control Sp)^2*
    (1+|v|+height)^degree*(2*T)^(3*εshell)
  have hfixed : 0 ≤ fixed :=
    joined_fixed_nonneg (QuadraticInitialBound.diagonalControl_nonneg ballProfile)
      (pow_nonneg (by linarith only [abs_nonneg v,hheight]) _) (Real.rpow_nonneg (by linarith only [hT]) _)
  have hApre : 0 ≤ Capre*(box.card:ℝ)*Z^εA :=
    mul_nonneg (mul_nonneg hCapre.le (Nat.cast_nonneg _)) (Real.rpow_nonneg hZ0.le _)
  have hCg' : 0 ≤ Cg*(K₀+Cret*2^J*Capre*max Kcls 0) :=
    mul_nonneg hCg.le (add_nonneg hK₀.le
      (mul_nonneg (mul_nonneg (mul_nonneg hCret.le (pow_nonneg zero_le_two _)) hCapre.le) hKmax))
  have hseedpos : (0:ℝ) < (seed₀.absNorm:ℝ) := CenteredMomentFirstScale.norm_pos seed₀ hs₀0
  have hgeomOld : ∀ l,lowAllowedExponent reflected Z (Real.logb Z (volume s)) (first l)≤exponent := fun l =>
    (lowAllowedExponent_le_lowSideExponent reflected Z _ (first l)).trans (hgeom l)
  rcases isEmpty_or_nonempty rows with hemp | ⟨⟨r₀,hr₀⟩⟩
  · -- no rows: the sum is empty
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    have hRHS : 0 ≤ Cg*(K₀+Cret*2^J*Capre*max Kcls 0)*fixed*(box.card:ℝ)*physical*
        Z^(loss+amp+p+exponent+error+εv+Bnorm*εshell+εlabels)/(seed₀.absNorm:ℝ) :=
      div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCg' hfixed) (Nat.cast_nonneg box.card))
        hphysical) (Real.rpow_nonneg hZ0.le _)) hseedpos.le
    refine hRHS.trans_eq ?_
    dsimp only [fixed]
    ring
  · obtain ⟨hTz0,hTzZ⟩ := hPres η₀ Z (widenState (st ⟨r₀,hr₀⟩) (st ⟨r₀,hr₀⟩).width le_rfl) (mult ⟨r₀,hr₀⟩) Tz
      (hpres ⟨r₀,hr₀⟩ _ _)
    -- the payment of the returned parts of the rows
    have hret : ∑ r : rows,Wt r*(Pr r).value ≤ Cret*(1+Tz)^J*(Capre*(box.card:ℝ)*Z^εA)*(max Kcls 0)*
        Z^(E₀'-Cycle63.Optimization.highTwoMargin+Lmax+εlabels/6+εlabels/6) := by
      have hWnn : ∀ r ∈ (Finset.univ : Finset rows),0 ≤ Wt r := fun r _ => Real.rpow_nonneg hZ0.le _
      have hX1' : ∀ r ∈ (Finset.univ : Finset rows),0 ≤ X r 1 ∧ X r 1 ≤ Bret :=
        fun r _ => ⟨(hX1 r).1,(hX1 r).2.trans hBret⟩
      have hpre' : ∀ (cap : ℝ) (D : Ideal O),
          ((((Finset.univ : Finset rows).filter (fun r => X r 1 ≤ cap)).filter
            (fun r => Ideal.span {mult r} = D)).card:ℝ) ≤ Capre*(box.card:ℝ)*Z^εA*Z^cap := by
        intro cap D
        rw [Finset.filter_filter]
        exact hpre cap D
      have hcard' : ∀ b : Bool,∀ r ∈ (Finset.univ : Finset rows),
          (Fintype.card ((Pr r).record b).Class:ℝ) ≤ max Kcls 0 := fun b r _ => hPrcard r b
      have hpays' : ∀ b : Bool,∀ r ∈ (Finset.univ : Finset rows),
          ((Pr r).record b).Pays Cycle63.Optimization.secondJunction (Pr r).scale (Pr r).length (Pr r).amp
            lossFloor := by
        intro b r _
        have h := (Pr r).pays b
        rwa [hPrloss r] at h
      have hw' : ∀ r ∈ (Finset.univ : Finset rows),
          Wt r ≤ Z^(E₀'+(X r 0-σbar)+Cycle63.AffineLedger.q*(target+mesh)) := by
        intro r _
        refine le_of_eq ?_
        dsimp only [Wt,E₀']
        congr 1
        ring
      have hF3' : ∀ r ∈ (Finset.univ : Finset rows),∀ δ : ℝ,Cycle63.Optimization.secondJunction ≤ δ → δ ≤ 3/4 →
          (X r 0-σbar)+X r 1+Cycle63.Optimization.density δ*X r 2+δ*X r 3 ≤
            small₁ r-(mfreq r*(1-Cycle63.Optimization.density δ)-δ*A₁ r-
              a₁ r*Cycle63.Optimization.amplifierCost δ)-γ₁ r := fun r _ δ h1 h2 => hF3 r δ h1 h2
      have hγ' : ∀ r ∈ (Finset.univ : Finset rows),0 ≤ γ₁ r := fun r _ => hγ r
      have hscale' : ∀ r ∈ (Finset.univ : Finset rows),
          (Pr r).scale+Real.logb Z ((Ideal.span {mult r}).absNorm:ℝ) ≤ X r 2+κ := by
        intro r _
        rw [hPrscale r]
        exact hscale r
      have hvol' : ∀ r ∈ (Finset.univ : Finset rows),
          (Pr r).length ≤ X r 3-target+(supportPadding (Fintype.card α) bs s.b₁ s.b₂ Z+gridSlack) := by
        intro r _
        have h := hPrlen r
        have hX3 : X r 3 = Real.logb Z (volume s)-
            Real.logb Z ((if reflected then (first r.val.1).1.2 else (first r.val.1).1.1).absNorm:ℝ)-
            Real.logb Z ((if second then (label r).1.2 else (label r).1.1).absNorm:ℝ) := rfl
        rw [hC₁ r,hEeq r] at h
        rw [hX3]
        linarith only [h]
      have hdel' : ∀ r ∈ (Finset.univ : Finset rows),
          Cycle63.Optimization.fixedDeletion cell ≤ target ∧ target ≤ target := by
        intro r _
        refine ⟨?_,le_rfl⟩
        dsimp only [target]
        rw [hunit,one_mul]
      have hcell' : ∀ r ∈ (Finset.univ : Finset rows),
          Cycle63.Optimization.firstCellTop ≤ cell ∧ cell ≤ Cycle63.Optimization.slotTop :=
        fun r _ => hbwin
      have hcaps' : ∀ r ∈ (Finset.univ : Finset rows),
          1 ≤ mfreq r ∧ A₁ r ≤ Cycle63.Optimization.twoLevelTotalA cell ∧ a₁ r ≤ Cycle63.Optimization.firstAmp cell ∧
            (Pr r).amp ≤ Cycle63.Optimization.secondAmp cell+ampSlack := by
        intro r _
        refine ⟨(hF6 r).1,(hF6 r).2.1,(hF6 r).2.2,?_⟩
        have h : (Pr r).amp ≤ unit*Cycle63.Optimization.secondAmp cell+ampSlack := hPramp r
        rw [hunit,one_mul] at h
        exact h
      have hLm' : ∀ r ∈ (Finset.univ : Finset rows),∀ δ : ℝ,Cycle63.Optimization.secondJunction ≤ δ → δ ≤ 3/4 →
          small₁ r+lossFloor+Cycle63.Optimization.density δ*κ+
            δ*(supportPadding (Fintype.card α) bs s.b₁ s.b₂ Z+gridSlack)+Cycle63.AffineLedger.q*mesh+
            (Cycle63.AffineLedger.q-Cycle63.Optimization.firstJunction)*target+
            Cycle63.Optimization.amplifierCost δ*ampSlack ≤ Lmax := fun r _ δ h1 h2 => hF7 r δ h1 h2
      have hsum := hretpay (P:=rows) mult (fun b r => (Pr r).unit b) Z Tz hzpaid.1 hTz0
        (fun b r => (Pr r).record b) Finset.univ Wt (Capre*(box.card:ℝ)*Z^εA) (max Kcls 0) E₀' Lmax
        (fun _ => cell) (fun r => (Pr r).scale) (fun r => (Pr r).length) (fun r => (Pr r).amp)
        (fun r => X r 0-σbar) (fun r => X r 1) (fun r => X r 2) (fun r => X r 3) mfreq A₁ a₁ small₁ γ₁
        (fun _ => target) (fun _ => target) lossFloor κ mesh
        (supportPadding (Fintype.card α) bs s.b₁ s.b₂ Z+gridSlack) Cycle63.AffineLedger.q ampSlack
        hWnn hApre hKmax hX1' hpre' hcard' hpays' hw' hF3' hγ' hscale' hvol' hdel' hcell' hcaps' hLm'
      rw [width_mul hBret0] at hsum
      exact hsum
    -- the old payment of the rows with the allowance of the labels
    let common : ℝ := εwidth*unit+ξ/2-unit*(Cycle63.AffineLedger.lowReserve)+εold+2*ε*d*(Fintype.card α:ℝ)+
      Cycle63.AffineLedger.lowRate*(omega+εpad*unit)+Cycle63.AffineLedger.q*mesh
    let errorBase : ℝ := common+pad
    let nomL := fun r : rows=>secondNominal unit Z amp (frequencyLoss Z 32 ξ+reserve)
      (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
      (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2) (label r).1.1 (label r).1.2 (label r).2.val
    let pay0 := fun r : rows=>Z^(-amp)*
      (firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first r.val.1)/volume (childSrc r.val.1))*
      (normalizer (label r).1.1 (label r).1.2 (label r).2.val*
        ((if second then (label r).1.2 else (label r).1.1).absNorm:ℝ)^(εshell-1))*
      Z^(nomL r+amp+errorBase)
    let allow := fun r : rows=>lowAllowance Z (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
      (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2) (label r).1.1 (label r).1.2
      (if second then (label r).1.2 else (label r).1.1)
    let apay := fun r : rows=>lowGeometryExponent reflected Z (Real.logb Z (volume s)) (first r.val.1)+errorBase+
      (unit-Mrow)+εv+Bnorm*εshell
    have hpays : (∑ r : rows,pay0 r*Z^(allow r)) ≤ (box.card:ℝ)*(K₀*Z^(p+exponent+errorBase+(unit-Mrow)+εv+
        Bnorm*εshell+εlabels)/(seed₀.absNorm:ℝ)) :=
      hzpaid.2 s hcard hsupply' reflected second first hf heq Rfirst alloc χfirst tfirst halloc
        R seed K Tsec ξ unit Mrow amp reserve errorBase εshell hseed hw₁ hw₂ heshell hsource
        Tfirst p exponent hTfirst hp seed₀ hs₀ hs₀0 hinj hfirstseed hfirstnorm hrad hgeomOld hfirstshell
        rows hU box hbox
    have hex : p+exponent+errorBase+(unit-Mrow)+εv+Bnorm*εshell+εlabels =
        p+exponent+error+εv+Bnorm*εshell+εlabels := by
      dsimp only [error,errorBase,common]
      ring
    rw [hex] at hpays
    have hlab : ∀ r : rows,label r∈actualSecondLabels (childSrc r.val.1) (R r.val.1) (seed r.val.1) := fun r =>
      actual_second_supported_label_mem (childSrc r.val.1) (R r.val.1) (seed r.val.1) (K r.val.1) (Tsec r.val.1) Z ξ
        r.val.2 (hU r.val r.property)
    have hgate := fun r : rows=>actual_second_labels_gates (childSrc r.val.1) (R r.val.1) (seed r.val.1)
      (hseed r.val.1) (hw₁ r.val.1) (hw₂ r.val.1) (label r) (hlab r)
    have hpay0nn : ∀ r : rows,0 ≤ pay0 r := fun r => by
      dsimp only [pay0]
      exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hZ0.le _)
        (div_nonneg (first_main_radius_pos _ _ _ _ _ _ _ hZ0 _).le
          (CenteredMomentAmplificationChildInput.volume_pos _).le))
        (mul_nonneg (normalizer_pos _ _ (hgate r).1 _).le (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
        (Real.rpow_nonneg hZ0.le _)
    have hold : ∑ r : rows,Cg*fixed*(mass r.val.1*Z^amp)*(pay0 r*Z^(allow r)) ≤
        Cg*fixed*(physical*Z^(loss+amp))*((box.card:ℝ)*(K₀*Z^(p+exponent+error+εv+Bnorm*εshell+εlabels)/
          (seed₀.absNorm:ℝ))) := by
      have hCf : 0 ≤ Cg*fixed := mul_nonneg hCg.le hfixed
      calc ∑ r : rows,Cg*fixed*(mass r.val.1*Z^amp)*(pay0 r*Z^(allow r))
          ≤ ∑ r : rows,Cg*fixed*(physical*Z^(loss+amp))*(pay0 r*Z^(allow r)) := by
            refine Finset.sum_le_sum fun r _ => ?_
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hCf)
              (mul_nonneg (hpay0nn r) (Real.rpow_nonneg hZ0.le _))
            simpa only [Real.rpow_add hZ0,mul_assoc] using
              mul_le_mul_of_nonneg_right (hmasscap r.val.1) (Real.rpow_nonneg hZ0.le amp)
        _ = Cg*fixed*(physical*Z^(loss+amp))*∑ r : rows,pay0 r*Z^(allow r) := by rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left hpays (mul_nonneg hCf (mul_nonneg hphysical (Real.rpow_nonneg hZ0.le _)))
    -- the bound of one row
    have hrow : ∀ r : rows,c r*(∑D∈Ds,∑z∈zs r,weight r z*
        ‖normalizedColumn (src r) (q r).E₂ (hE₂ r) (q r).R₂ (divisorSeed r) D z‖^2) ≤
        Cg*fixed*(mass r.val.1*Z^amp)*(pay0 r*Z^(allow r))+Cg*fixed*physical*(Wt r*(Pr r).value) := by
      intro r
      have hb := hRowbd r (zs r) (weight r) (hnonneg r) (hkeep r) (hweight r)
      have hc : 0 ≤ c r := by
        dsimp only [c]
        exact mul_nonneg (mul_nonneg (div_nonneg (hmass0 _) (CenteredMomentAmplificationChildInput.volume_pos _).le)
          (g r).datum.K_pos.le) (normalizer_pos _ _ (g r).datum.hC _).le
      have hnom : secondNominal unit Z amp omega (q r).C₁ (g r).D₁ (g r).datum.C (g r).datum.D
          (g r).datum.inactive = nomL r := by
        have hback := actual_low_label_nominal unit Z amp omega (q r).C₁ (g r).D₁ (g r).datum.C (g r).datum.D
          (g r).datum.inactive (label r) (hC₂ r) (hD₂ r) (hU₂ r)
        have hfront := congrArg₂ (fun C₁ D₁ : Ideal O=>
          secondNominal unit Z amp omega C₁ D₁ (label r).1.1 (label r).1.2 (label r).2.val) (hC₁ r) (hD₁ r)
        have homega := congrArg (fun omega : ℝ=>secondNominal unit Z amp omega
          (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
          (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
          (label r).1.1 (label r).1.2 (label r).2.val) hωeq
        exact hback.trans (hfront.trans homega)
      have hN : ((q r).E₂.absNorm:ℝ) = ((if second then (label r).1.2 else (label r).1.1).absNorm:ℝ) := by
        rw [hEeq r]
      have hXf : lowAllowance Z (q r).C₁ (g r).D₁ (g r).datum.C (g r).datum.D (q r).E₂ = allow r := by
        dsimp only [allow]
        rw [hC₁ r,hD₁ r,hC₂ r,hD₂ r,hEeq r]
      rw [hN,hXf,hnom] at hb
      have hE2 : (0:ℝ) < ((if second then (label r).1.2 else (label r).1.1).absNorm:ℝ) :=
        second_norm_pos second (hgate r).1 (hgate r).2.1
      have hnormE : ((if second then (label r).1.2 else (label r).1.1).absNorm:ℝ) ≤ Z^Bnorm :=
        second_norm_le second ((hgate r).2.2.2.2.2.1.trans (hsource r.val.1))
          ((hgate r).2.2.2.2.2.2.trans (hsource r.val.1))
      have hpay : pay0 r ≤ Z^(apay r)/((if second then (label r).1.2 else (label r).1.1).absNorm:ℝ) :=
        hmz.2 s hcard hsupply' reflected second (first r.val.1) (hf r.val.1).1 (hf r.val.1).2 (heq r.val.1) Rfirst
          (alloc r.val.1) (χfirst r.val.1) (tfirst r.val.1) (halloc r.val.1) (label r).1.1 (label r).1.2
          (hgate r).1 (hgate r).2.1 (label r).2.val unit Mrow amp ξ reserve errorBase εshell Bnorm heshell hnormE
      have hcoef : c r = mass r.val.1/volume (childSrc r.val.1)*
          firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first r.val.1)*
          normalizer (label r).1.1 (label r).1.2 (label r).2.val :=
        congrArg₂ (fun K normal : ℝ=>mass r.val.1/volume (childSrc r.val.1)*K*normal) (hKeq r)
          (actual_low_label_normalizer _ _ _ _ (hC₂ r) (hD₂ r) (hU₂ r))
      have hpower : Z^(nomL r+amp+common)*Z^pad = Z^(nomL r+amp+errorBase) := by
        rw [← Real.rpow_add hZ0]
        congr 1
        dsimp only [errorBase]
        ring
      have hcancel : Z^amp*Z^(-amp) = (1:ℝ) := by
        rw [← Real.rpow_add hZ0]
        simp
      have hid : c r*(Cg*(2*b^2*Cs^(4*N))*QuadraticInitialBound.diagonalControl (st r).radial.profile*
          (p₀.control Sp)^2*(1+|v|+height)^degree*
          (((if second then (label r).1.2 else (label r).1.1).absNorm:ℝ)^(εshell-1))*(2*T)^(3*εshell)*Z^pad)*
          Z^(nomL r+amp+common) = Cg*fixed*(mass r.val.1*Z^amp)*pay0 r := by
        have hprof : (st r).radial.profile = ballProfile := rfl
        rw [hprof]
        exact joined_identity hcoef rfl hpower hcancel
      refine (mul_le_mul_of_nonneg_left hb hc).trans ?_
      refine joined_row_bound hZone hid ?_ ?_ (hpay0nn r) hpay (hmasscap r.val.1) hphysical
        (mul_nonneg hCg.le hfixed) hE2 (hPrRet r) ((Pr r).value_nonneg hZ0.le) (Real.rpow_nonneg hZ0.le _) ?_
      · have habs := absorb_rate hrate hεX hεpad hMmin hω
        dsimp only [common]
        linarith only [habs]
      · exact mul_nonneg hc (joined_const_nonneg hCg.le (QuadraticInitialBound.diagonalControl_nonneg _)
          (pow_nonneg (by linarith only [abs_nonneg v,hheight]) _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
          (Real.rpow_nonneg (by linarith only [hT]) _) (Real.rpow_nonneg hZ0.le _))
      · exact returned_weight_eq hZone hE2 rfl (returned_row_exponent reflected second left₁ (first r.val.1) (label r)
          Z Mrow (Real.logb Z (volume s)) amp ξ reserve ε unit errorBase common pad loss εv Bnorm εshell
          (2*ε*d*(Fintype.card α:ℝ)) (Cycle63.AffineLedger.q*(unit*Cycle63.Optimization.fixedDeletion cell+mesh))
          E₀ (apay r) (nomL r+amp+common) rfl rfl rfl rfl)
    -- the sum over the rows
    have hsumrow := Finset.sum_le_sum (fun r (_ : r∈(Finset.univ : Finset rows)) => hrow r)
    rw [Finset.sum_add_distrib] at hsumrow
    have hRET : ∑ r : rows,Cg*fixed*physical*(Wt r*(Pr r).value) ≤
        Cg*fixed*physical*(Cret*(1+Tz)^J*(Capre*(box.card:ℝ)*Z^εA)*(max Kcls 0)*
          Z^(E₀'-Cycle63.Optimization.highTwoMargin+Lmax+εlabels/6+εlabels/6)) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hret (mul_nonneg (mul_nonneg hCg.le hfixed) hphysical)
    have hF9' : Lmax-Cycle63.Optimization.highTwoMargin+εA ≤
        (error-pad-2*ε*d*(Fintype.card α:ℝ))+εlabels/2 := by
      have herr : error = εwidth*unit+ξ/2-unit*(Cycle63.AffineLedger.lowReserve)+(unit-Mrow)+εold+
          2*ε*d*(Fintype.card α:ℝ)+Cycle63.AffineLedger.lowRate*(omega+εpad*unit)+
          Cycle63.AffineLedger.q*mesh+pad := rfl
      linarith only [hF9,herr]
    have hfinal := joined_total_shift hZone hCg.le hCret.le hCapre.le hKmax hfixed (Nat.cast_nonneg _) hphysical hTz0
      hTzZ hel.le hτJ hseedpos rfl rfl hF9' hold hRET
    exact hsumrow.trans (hfinal.trans_eq (by dsimp only [fixed]; ring))

end
end OAI.SevenEighths.Cycle63InitialMass
