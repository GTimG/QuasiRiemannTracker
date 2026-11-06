/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B095
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorInverseRawField
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorClassBudget
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorCountFromMoments
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorRowCountEndpoint

/- BEGIN ORIGINAL Cycle61.Moment.HighSourceRows; sha256 44d31c0dd178cc1f21a2eb6ace4dba1e1221be394b21425543d51e5d7ffb1ebc -/
section
                                        
                                          

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set HeckeFamily HeckePrimeRay HeckePrimeAnnular HeckeDetectorZeros
open HeckeDyadic HeckeDetectorCoefficientTransfer
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
open LowBranch CenteredMomentEligibleEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Genuine high-bin estimates for the literal second retained allocation.
All structural equalities are exact source data; no energy envelope is assumed. -/
theorem actual_high_source_row
    (Wslot : ℝ → ℂ) (A₀ B₀ : ℝ) (hA₀ : 0 < A₀)
    (hWs : Function.support Wslot ⊆ Icc A₀ B₀) (hW : ContDiff ℝ ∞ Wslot)
    (Rwidth Rplain dmax τ εslot εplain e κ vplain vslot σmin σmax
      bΦ Mcap Bmask margin d : ℝ)
    (hRw : 0 ≤ Rwidth) (hRp : 0 ≤ Rplain) (hdmax : 0 ≤ dmax)
    (hτ : 0 < τ) (hεs : 0 < εslot) (hεp : 0 < εplain)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hκ' : κ ≤ 1)
    (hvp : 0 ≤ vplain) (hvs : 0 ≤ vslot)
    (hslotBudget : 8*e*Rwidth+κ ≤ εslot)
    (hplainBudget : 12*e*(Rplain+2)+8*κ+2*vplain ≤ εplain)
    (hbΦ : 0 ≤ bΦ) (hmargin : 0 < margin) (hd : 0 < d)
    (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax)
    (profileBound : ℕ → ℝ) (hprofile : ∀ k, 0 ≤ profileBound k) :
    ∃ n : ℕ, ∃ Cp Cs : ℝ, 0 < Cp ∧ 0 < Cs ∧
    ∀ η₀ : Character, ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (s : NaturalState Z Bmask bΦ), s.width ≤ Mcap →
    ∀ (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ η₀.modulus)
      (a : ℝ) (i : ℕ), 51/100 ≤ a → a ≤ 1 →
    ∀ z : O, ∀ hz : s.radial.keep z, ∀ F : NaturalRow s.character z,
    ActualLow M H hH s η₀ hQM hQη a e (3*(i+1 : ℕ)*Z^τ) z →
    ∀ {Dict : Type*} [Fintype Dict] (χ : Dict → Character)
      (hχ : ∀ j, (χ j).residue ≠ 1) (j : Dict),
    χ j = excluded F.character s.puncture →
    zeroMaximum χ hχ (3*(i+1 : ℕ)*Z^τ) < a+2*e →
    (χ j).modulus.absNorm ≤ Z^d →
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (w σ v : ι → ℝ) (θ : ι → RayQuotient.Characters M H) (t : ℝ)
      (src : Data ι) (second : Bool) (L : Ideal O)
      (alloc : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2))),
    src.η = s.character → src.m = s.mask → src.A = 1 → src.t = t →
    (∀ k, src.slots k = primePool M H B₀ (Z^(w k))) →
    (∀ k I, src.coefficient k I = idealCoeff (relativeCharacter M H hH η₀ (θ k)) I*
      annularWeight Wslot (Z^(w k)) (σ k) (v k) I) →
    (∀ k, src.P k = Z^(w k)) →
    (∀ k, 0 ≤ w k) → (∀ k, w k/d ≤ Rwidth) →
    (∀ k, σmin ≤ σ k) → (∀ k, σ k ≤ σmax) →
    (∀ k, |t+v k|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ) →
    (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^vslot →
    |t|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
    (3+(3*i+2 : ℕ)*Z^τ)^4 ≤ (Z^d)^vplain →
    ∀ (W : Fin 2 → ℝ → ℂ) (X r A B : Fin 2 → ℝ),
    src.W₁ = W 0 → src.W₂ = W 1 →
    (∀ k, Cycle61.Physical.postPlainScale L alloc
      (Cycle61.Physical.sourcePlainScales src.toSource second) k = X k) →
    (∀ k, 0 < X k) → (∀ k, clippedScale (X k) = (Z^d)^(r k)) →
    (∀ k, 0 < A k) →
    (∀ k, Function.support (dilated (W k) (clipDilation (X k))) ⊆ Icc (A k) (B k)) →
    (∀ k, ContDiff ℝ ∞ (dilated (W k) (clipDilation (X k)))) →
    (∀ k, 0 ≤ r k) → (∀ k, r k ≤ Rplain) →
    (∀ k, ∀ x ∈ Icc (1-a-6*e) 2, ∀ u : ℝ,
      (1+|u|)^2*‖mellin (dilated (W k) (clipDilation (X k)))
        ((x : ℂ)+u*Complex.I)‖ ≤ profileBound 2) →
    (∀ k, ∀ x ∈ Icc (1-a-6*e) 2, ∀ u : ℝ,
      (1+|u|)^(n+2)*‖mellin (dilated (W k) (clipDilation (X k)))
        ((x : ℂ)+u*Complex.I)‖ ≤ profileBound (n+2)) →
    ‖Cycle61.Physical.sourcePositiveRow src.toSource second L alloc z‖^2 ≤
      Cp^2*Cs^((liveIndices L alloc).card)*
        Z^((2*a-1)*(
          (∑ j, Real.logb Z (clippedScale (Cycle61.Physical.sourcePlainScales src.toSource second j)))+
          (∑ k, w k)-Cycle61.Physical.clippedReduction
            (Real.logb Z (formalReductionFactor L alloc src.P))
            (fun j => Real.logb Z (Cycle61.Physical.sourcePlainScales src.toSource second j))
            (Cycle61.Physical.actualPlainReduction Z L alloc))+
          2*εplain*d+2*εslot*d*((liveIndices L alloc).card)) := by
  obtain ⟨n,Cp,Cs,hCp,hCs,hbound⟩ := actual_high_retained_row M H hH Wslot A₀ B₀ hA₀ hWs hW
    Rwidth Rplain dmax τ εslot εplain e κ vplain vslot σmin σmax bΦ Mcap Bmask margin d
    hRw hRp hdmax hτ hεs hεp he he' hκ hκ' hvp hvs hslotBudget hplainBudget
    hbΦ hmargin hd hdsupply hdm profileBound hprofile
  refine ⟨n,Cp,Cs,hCp,hCs,?_⟩
  intro η₀
  filter_upwards [hbound η₀] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s hs hQM hQη a i ha ha' z hz F hbin Dict _ χ hχ j hj hzero hmod
    ι _ _ w σ v θ t src second L alloc hchar hmask hA' ht hpool hcoeff hP
    hw hwr hσ hσ' hfreq hheight hfreqP hheightP W X r A B hW₁ hW₂ hpost
    hX hscale hA hsupport hsmooth hr hrR hm₂ hmn
  have hb := hZ.2 s hs hQM hQη a i ha ha' z hz F hbin χ hχ j hj hzero hmod
    (fun k : liveIndices L alloc => w k) (fun k : liveIndices L alloc => σ k)
    (fun k : liveIndices L alloc => v k) (fun k : liveIndices L alloc => θ k) t
    (fun k => hw k) (fun k => hwr k) (fun k => hσ k) (fun k => hσ' k)
    (fun k => hfreq k) hheight hfreqP hheightP W X r A B hX hscale hA hsupport
    hsmooth hr hrR hm₂ hmn
  have hrow := final_source_row_eq s src second L alloc
    (fun k => primePool M H B₀ (Z^(w k)))
    (fun k I => idealCoeff (relativeCharacter M H hH η₀ (θ k)) I*
      annularWeight Wslot (Z^(w k)) (σ k) (v k) I)
    (fun k => Z^(w k)) t z hchar hmask hA' ht hpool hcoeff hP
  rw [hW₁,hW₂,hpost 0,hpost 1] at hrow
  have hpreX : ∀ j, 0 < Cycle61.Physical.sourcePlainScales src.toSource second j := by
    intro j
    cases second <;> fin_cases j
    · exact src.X₁_pos
    · exact src.X₂_pos
    · exact src.Y₁_pos
    · exact src.Y₂_pos
  have he := actual_high_allocation_exponent Z hZ.1 L alloc
    (Cycle61.Physical.sourcePlainScales src.toSource second) hpreX w d r
    (fun j => by rw [hpost j]; exact hscale j)
  rw [←funext hP] at he
  rw [hrow]
  have hb' := hb
  simp only [Fintype.card_coe,Finset.sum_coe_sort] at hb'
  rw [he] at hb'
  exact hb' 

#print axioms actual_high_source_row
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.HighSourceRows -/

/- BEGIN ORIGINAL LocalMoment.UnmarkedDensity; sha256 de4fff9416258deadcc0c6cd023ecd5fb8dd1c90f698c587aa2899201258098d -/
section
                                                                 
                                                                 

/-! The unmarked zero-density source interface used by the proposed local
physical moment.  These lemmas use only the existing unmarked plain and
inverse moments.  They do not assert the local physical moment. -/

namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set Filter

namespace SevenEighths.LocalMoment
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
open HeckeDetectorCoefficientTransfer HeckeDetectorDyadicProfiles
open HeckeDetectorRawFiber HeckeDetectorBranchBudget HeckeDetectorRowCount
open HeckeDetectorInverseFiberCount
open HeckeDetectorRowwisePolynomial

def unmarkedDensity (δ : ℝ) : ℝ := 1 - 10 * δ / (3 * (5 - 2 * δ))

def unmarkedCutoff (δ : ℝ) : ℝ := Endpoint.balancedCutoff δ (1 / 2)

theorem unmarkedDensity_ge_two_sevenths {δ : ℝ} (hδ : δ ≤ 3 / 4) :
    2 / 7 ≤ unmarkedDensity δ := by
  have hden : 0 < 3 * (5 - 2 * δ) := by linarith
  have hquot : 10 * δ / (3 * (5 - 2 * δ)) ≤ 5 / 7 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  unfold unmarkedDensity
  linarith

theorem unmarkedDensity_gt_one_sixth {δ : ℝ} (hδ : δ ≤ 3 / 4) :
    1 / 6 < unmarkedDensity δ := by
  linarith [unmarkedDensity_ge_two_sevenths hδ]

theorem unmarkedCutoff_eq {δ : ℝ} (hδ : δ ≤ 5 / 6) :
    unmarkedCutoff δ = 5 / (5 - 2 * δ) := by
  have hden : 5 - 2 * δ ≠ 0 := by linarith
  have hden' : (5 : ℝ) - δ * 2 ≠ 0 := by linarith
  have hD : Endpoint.balanceDenominator δ (1 / 2) = (5 - 2 * δ) / 2 := by
    unfold Endpoint.balanceDenominator Endpoint.denominator Endpoint.primeWeight
    ring
  unfold unmarkedCutoff Endpoint.balancedCutoff
  rw [hD, show 2 * ((5 - 2 * δ) / 2) = 5 - 2 * δ by ring]
  norm_num [Endpoint.primeWeight]
  field_simp [hden, hden']
  ring

theorem unmarkedDensity_eq_balanced {δ : ℝ} (hδ : δ ≤ 5 / 6) :
    unmarkedDensity δ = Endpoint.balancedRowCount δ (1 / 2) := by
  have hden : 5 - 2 * δ ≠ 0 := by linarith
  have hden' : (5 : ℝ) - δ * 2 ≠ 0 := by linarith
  unfold Endpoint.balancedRowCount
  change unmarkedDensity δ = 1 - 5 / 6 + (5 / 6 - δ) * unmarkedCutoff δ
  rw [unmarkedCutoff_eq hδ]
  unfold unmarkedDensity
  field_simp [hden, hden']
  ring

theorem unmarkedCutoff_bounds {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 5 / 6) :
    1 ≤ unmarkedCutoff δ ∧ unmarkedCutoff δ ≤ 3 / 2 := by
  simpa only [unmarkedCutoff, sub_zero] using
    balanced_cutoff_bounds hδ hδ' (show (0 : ℝ) ≤ 0 by norm_num)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)

/-- Two existing unmarked source bounds suffice for the density exponent.
The support tolerance is kept explicitly; no prime amplitude or marked
moment is used in this interpolation. -/
theorem unmarked_count_bound (B C U δ r m ε γ : ℝ)
    (hC : 0 ≤ C) (hU : 1 ≤ U) (hδ : 0 ≤ δ) (hδ' : δ ≤ 5 / 6)
    (hγ : 0 ≤ γ)
    (hleft : unmarkedCutoff δ - r - γ ≤ m)
    (hright : r ≤ unmarkedCutoff δ + γ)
    (hI : B ≤ C * U ^ (max 1 ((1 + 5 * r) / 6) - δ * r + ε))
    (hP : B ≤ C * U ^ (1 - 2 * δ * m + ε)) :
    B ≤ C * U ^ (unmarkedDensity δ + ε + 2 * γ) := by
  have hbounds := unmarkedCutoff_bounds hδ hδ'
  have hbal := balanced_count_identity hδ hδ'
    (show (0 : ℝ) ≤ 0 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have hbal' : max (shortExponent δ 0 (unmarkedCutoff δ))
      (longExponent δ (unmarkedCutoff δ)) = unmarkedDensity δ := by
    simpa only [unmarkedCutoff, sub_zero, ← unmarkedDensity_eq_balanced hδ'] using hbal
  have hs : shortExponent δ 0 (unmarkedCutoff δ) ≤ unmarkedDensity δ := by
    rw [← hbal']
    exact le_max_left _ _
  have hl : longExponent δ (unmarkedCutoff δ) ≤ unmarkedDensity δ := by
    rw [← hbal']
    exact le_max_right _ _
  have promote (p : ℝ) (hp : B ≤ C * U ^ p)
      (hpt : p ≤ unmarkedDensity δ + ε + 2 * γ) :
      B ≤ C * U ^ (unmarkedDensity δ + ε + 2 * γ) :=
    hp.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hU hpt) hC)
  by_cases hr1 : 1 ≤ r
  · rw [max_eq_right (show (1 : ℝ) ≤ (1 + 5 * r) / 6 by linarith)] at hI
    apply promote _ hI
    have hh := long_count_bound hδ' hγ hright
    have hg : (5 / 6 - δ) * γ ≤ 2 * γ := by nlinarith
    linarith
  · rw [max_eq_left (show (1 + 5 * r) / 6 ≤ (1 : ℝ) by linarith)] at hI
    have hchoose := selected_short_bound (δ := δ) (x := 0)
      (t := unmarkedCutoff δ) (r := r) hδ (by norm_num) (by norm_num)
    by_cases hrc : crossing 0 (unmarkedCutoff δ) ≤ r
    · apply promote _ hI
      have hh := hchoose.2 hrc
      unfold inverseExponent at hh
      nlinarith
    · apply promote _ hP
      have hh := hchoose.1 (le_of_not_ge hrc)
      have hm := mul_le_mul_of_nonneg_left hleft (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hδ)
      have hg : 2 * δ * γ ≤ 2 * γ := by nlinarith
      unfold plainExponent at hh
      nlinarith

/-- A detector fiber with no required prime-slot supply.  Unlike the existing
marked `HeckeDetectorRawFiber.Fiber`, it admits a truly unmarked source. -/
structure UnmarkedFiber (U a ε tstar T allowance : ℝ) (i : ℕ) (Label : Type*) where
  rows : Finset FreeRow
  nonempty : rows.Nonempty
  family : FreeRow → Label → Character
  witness : ∀ u, SupportedWitness (family u) U a ε tstar T allowance i
  label : Label
  left : Fin (dyadicLength U)
  right : Fin (dyadicLength U)
  fixed_label : ∀ u ∈ rows, (witness u).label = label
  fixed_left : ∀ u ∈ rows, (witness u).left = left
  fixed_right : ∀ u ∈ rows, (witness u).right = right
  row_norm : ∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ U
  rowData : RowData
  reverse : Bool
  row_coeff : ∀ u ∈ rows, ∀ J : Ideal O, idealCoeff (family u label) J =
    if reverse then starRingEnd ℂ (idealCoeff (rowData.character ⟨u.val, u.property.1⟩) J)
    else idealCoeff (rowData.character ⟨u.val, u.property.1⟩) J

def UnmarkedFiber.r {U a ε tstar T allowance : ℝ} {i : ℕ} {Label : Type*}
    (F : UnmarkedFiber U a ε tstar T allowance i Label) : ℝ :=
  Real.logb U ((2 : ℝ) ^ F.left.val)

def UnmarkedFiber.m {U a ε tstar T allowance : ℝ} {i : ℕ} {Label : Type*}
    (F : UnmarkedFiber U a ε tstar T allowance i Label) : ℝ :=
  Real.logb U ((2 : ℝ) ^ F.right.val)

structure UnmarkedMoments {U a ε tstar T allowance : ℝ} {i : ℕ} {Label : Type*}
    (F : UnmarkedFiber U a ε tstar T allowance i Label)
    (c κ C height εm : ℝ) : Prop where
  inverse_raw : ∀ n : ℕ, n ≤ 2 → ∀ s ∈ Icc (0 : ℝ) 1,
    ∀ t ∈ Icc (-height) height,
      let W := twistProfile (logTest
        (orientedProfile F.reverse (inverseTest U tstar F.r)) n) s t
      RawMoment F.rowData W c κ C ∧ RawMoment F.rowData (scaleProfile W) c κ C
  plain_unmarked : ∀ j k : ℕ, j + k ≤ 2 → ∀ s ∈ Icc (0 : ℝ) 1,
    ∀ t ∈ Icc (-height) height,
      ∑ u ∈ F.rows, ‖polynomial (F.family u F.label) false
        ((logProfile^[j]) positiveAnnular) (U^F.m) s t *
        polynomial (F.family u F.label) false
        ((logProfile^[k]) positiveAnnular) (U^F.m) s t‖^2 ≤
          C * U ^ (max 1 (2 * F.m) + εm)

/-- The actual unmarked detector density bound follows from the established
raw inverse moment and the established two-plain zero-slot moment.  The
statement retains coefficient orientation, all source profiles and frequencies,
and the full finite row set; its only loss is the displayed source padding. -/
theorem count_from_unmarked_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm : ℝ) (hεm : 0 < εm) :
    ∃ c κ K₀ : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < κ ∧ 0 ≤ K₀ ∧
      ∀ᶠ U : ℝ in atTop,
        ∀ (a ε T allowance C height : ℝ) (i : ℕ),
        1 < U → 1 / 2 ≤ a → 2 * a - 1 ≤ 5 / 6 → 0 ≤ ε → ε ≤ 1 / 1000 →
        0 ≤ C → 0 ≤ height → 2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height →
        ∀ {Label : Type*}
          (F : UnmarkedFiber U a ε (unmarkedCutoff (2 * a - 1)) T allowance i Label),
        UnmarkedMoments F c κ C height εm →
          (F.rows.card : ℝ) ≤ fiberConstant C height K₀ *
            U ^ (unmarkedDensity (2 * a - 1) + 156 * ε + εm) := by
  obtain ⟨c, κ, K₀, hc, hc1, hκ, hK, hamp⟩ :=
    HeckeDetectorNoSlotInverseCount.no_slot_inverse_count M H hH S φ hφ hφc hφp hφ0
      hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB 2 εm (by norm_num) hεm
  refine ⟨c, κ, K₀, hc, hc1, hκ, hK, ?_⟩
  filter_upwards [hamp] with U hamp
  intro a ε T allowance C height i hU ha hδcap hε hεsmall hC hh hf Label F moments
  let δ := 2 * a - 1
  have hδ : 0 ≤ δ := by dsimp [δ]; linarith
  have ht := unmarkedCutoff_bounds hδ hδcap
  have hgeom := fiber_lengths F.rows F.nonempty F.family U a ε (unmarkedCutoff δ)
    T allowance i hU F.witness F.left F.right F.fixed_left F.fixed_right
  change unmarkedCutoff δ - F.r - ε ≤ F.m ∧ F.r ≤ unmarkedCutoff δ + ε ∧
    F.m ≤ 1 / 2 + 75 * ε ∧ unmarkedCutoff δ - 1 / 2 - 76 * ε ≤ F.r ∧
    0 ≤ F.m at hgeom
  have hr0 : 0 ≤ F.r := by linarith [hgeom.2.2.2.1]
  have hr2 : F.r ≤ 2 := by linarith [hgeom.2.1]
  have hUp : 0 < U := zero_lt_one.trans hU
  obtain ⟨hconst, hconstP, hconstI, hconstI0⟩ :=
    fiberConstant_bounds C height K₀ hC hh hK
  have hi0 := hamp F.rows F.family a ε (unmarkedCutoff δ) T allowance i hU ha
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label
    F.fixed_left F.fixed_right hr0 hr2 F.rowData F.reverse C height hC hh hf
    F.row_norm F.row_coeff moments.inverse_raw
  have hp0 := HeckeDetectorNoSlotPlainCount.no_slot_plain_count F.rows F.family U a ε
    (unmarkedCutoff δ) T allowance i hU (by linarith)
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label
    F.fixed_left F.fixed_right εm C height hC hh hf moments.plain_unmarked
  have promote (C' p q : ℝ) (hC' : C' ≤ fiberConstant C height K₀)
      (hb : (F.rows.card : ℝ) ≤ C' * U ^ p) (hpq : p ≤ q) :
      (F.rows.card : ℝ) ≤ fiberConstant C height K₀ * U ^ q := by
    exact hb.trans ((mul_le_mul_of_nonneg_right hC' (Real.rpow_nonneg hUp.le _)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le hpq) hconst))
  have hI : (F.rows.card : ℝ) ≤ fiberConstant C height K₀ *
      U ^ (max 1 ((1 + 5 * F.r) / 6) - δ * F.r + (154 * ε + εm)) := by
    apply promote _ _ _ hconstI0 hi0
    change max 1 ((1 + 5 * F.r) / 6) - δ * F.r + 2 * ε + εm ≤
      max 1 ((1 + 5 * F.r) / 6) - δ * F.r + (154 * ε + εm)
    linarith
  have hP : (F.rows.card : ℝ) ≤ fiberConstant C height K₀ *
      U ^ (1 - 2 * δ * F.m + (154 * ε + εm)) := by
    apply promote _ _ _ hconstP hp0
    change max 1 (2 * F.m) - 2 * δ * F.m + 4 * ε + εm ≤
      1 - 2 * δ * F.m + (154 * ε + εm)
    have hm : max 1 (2 * F.m) ≤ 1 + 150 * ε := max_le (by linarith) (by linarith [hgeom.2.2.1])
    linarith
  have hbound := unmarked_count_bound (F.rows.card : ℝ) (fiberConstant C height K₀)
    U δ F.r F.m (154 * ε + εm) ε hconst hU.le hδ hδcap hε
    hgeom.1 hgeom.2.1 hI hP
  convert hbound using 1
  congr 2
  ring

end SevenEighths.LocalMoment
end
end OAI

end
/- END ORIGINAL LocalMoment.UnmarkedDensity -/

/- BEGIN ORIGINAL LocalMoment.UnmarkedBatch; sha256 1bfbe1461df05e5ee16b4b71db9e9dde57f50499be7f372451c62f57e19bdff1 -/
section
                                  

/-! Unmarked detector partition, adapted from OpenAI's DetectorBatch and
DetectorFiberPartition. Unlike the marked batch, this has no positive
prime-slot-supply hypothesis. Its moments remain explicit source inputs. -/

namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set Filter

namespace SevenEighths.LocalMoment
open HeckeFamily HeckeInverseAmplification HeckeDetectorSupportedWitness
open HeckeDetectorWitnessRows HeckeDetectorInverseFiberCount HeckeDetectorRawFiber

structure UnmarkedBatch (Label : Type*) (U a ε tstar T allowance : ℝ) (i : ℕ) where
  rows : Finset FreeRow
  family : FreeRow → Label → Character
  witness : ∀ u, SupportedWitness (family u) U a ε tstar T allowance i
  row_norm : ∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ U
  data : Label → RowData
  reverse : Label → Bool
  row_coeff : ∀ u ∈ rows, ∀ j, ∀ I : Ideal O, idealCoeff (family u j) I =
    if reverse j then starRingEnd ℂ (idealCoeff ((data j).character ⟨u.val, u.property.1⟩) I)
    else idealCoeff ((data j).character ⟨u.val, u.property.1⟩) I

variable {Label : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}

/-- Extend witnesses only to satisfy the ambient `FreeRow` interface.
Outside the finite source set, reuse one source row; no principal or
out-of-bin ambient row is required to possess a detector witness. -/
def supportedRowRetraction (rows : Finset FreeRow) (u₀ : rows) (u : FreeRow) : rows :=
  if hu : u ∈ rows then ⟨u, hu⟩ else u₀

@[simp] theorem supportedRowRetraction_mem (rows : Finset FreeRow) (u₀ u : rows) :
    supportedRowRetraction rows u₀ u.val = u := by
  simp [supportedRowRetraction, u.property]

def UnmarkedBatch.ofSupportedRows (rows : Finset FreeRow) (u₀ : rows)
    (family : rows → Label → Character)
    (witness : ∀ u, SupportedWitness (family u) U a ε tstar T allowance i)
    (hrow : ∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ U)
    (data : Label → RowData) (reverse : Label → Bool)
    (hcoeff : ∀ u : rows, ∀ j, ∀ I : Ideal O, idealCoeff (family u j) I =
      if reverse j then starRingEnd ℂ (idealCoeff ((data j).character
        ⟨u.val.val, u.val.property.1⟩) I)
      else idealCoeff ((data j).character ⟨u.val.val, u.val.property.1⟩) I) :
    UnmarkedBatch Label U a ε tstar T allowance i where
  rows := rows
  family := fun u => family (supportedRowRetraction rows u₀ u)
  witness := fun u => witness (supportedRowRetraction rows u₀ u)
  row_norm := hrow
  data := data
  reverse := reverse
  row_coeff := by
    intro u hu j I
    have h := hcoeff ⟨u, hu⟩ j I
    simpa only [supportedRowRetraction, dite_eq_left hu] using h

def UnmarkedBatch.fiberRows (B : UnmarkedBatch Label U a ε tstar T allowance i)
    (j : Label) (J K : Fin (dyadicLength U)) : Finset FreeRow :=
  B.rows.filter (fun u => (B.witness u).label = j ∧
    (B.witness u).left = J ∧ (B.witness u).right = K)

def UnmarkedBatch.fiber (B : UnmarkedBatch Label U a ε tstar T allowance i)
    (j : Label) (J K : Fin (dyadicLength U))
    (hne : (B.fiberRows j J K).Nonempty) : UnmarkedFiber U a ε tstar T allowance i Label where
  rows := B.fiberRows j J K
  nonempty := hne
  family := B.family
  witness := B.witness
  label := j
  left := J
  right := K
  fixed_label := fun _ hu => (Finset.mem_filter.mp hu).2.1
  fixed_left := fun _ hu => (Finset.mem_filter.mp hu).2.2.1
  fixed_right := fun _ hu => (Finset.mem_filter.mp hu).2.2.2
  row_norm := fun u hu => B.row_norm u (Finset.mem_filter.mp hu).1
  rowData := B.data j
  reverse := B.reverse j
  row_coeff := fun u hu => B.row_coeff u (Finset.mem_filter.mp hu).1 j

theorem UnmarkedBatch.card_eq_sum_fibers [Fintype Label]
    (B : UnmarkedBatch Label U a ε tstar T allowance i) :
    B.rows.card = ∑ j : Label, ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
      (B.fiberRows j J K).card := by
  have hh := Finset.card_eq_sum_card_fiberwise (s := B.rows) (t := Finset.univ)
    (f := fun u => ((B.witness u).label, (B.witness u).left, (B.witness u).right))
    (by intro u hu; exact Finset.mem_univ _)
  simpa only [Fintype.sum_prod_type, Prod.mk.injEq, UnmarkedBatch.fiberRows] using hh

theorem UnmarkedBatch.card_bound [Fintype Label]
    (B : UnmarkedBatch Label U a ε tstar T allowance i)
    (C exponent : ℝ) (hC : 0 ≤ C) (hU : 0 < U)
    (hfiber : ∀ j J K, ∀ hne : (B.fiberRows j J K).Nonempty,
      ((B.fiber j J K hne).rows.card : ℝ) ≤ C * U ^ exponent) :
    (B.rows.card : ℝ) ≤ (Fintype.card Label : ℝ) * (dyadicLength U : ℝ)^2 *
      C * U ^ exponent := by
  have he : (B.rows.card : ℝ) = ∑ j : Label,
      ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
        ((B.fiberRows j J K).card : ℝ) := by exact_mod_cast B.card_eq_sum_fibers
  rw [he]
  calc
    _ ≤ ∑ j : Label, ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
        C * U ^ exponent := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro J _
      apply Finset.sum_le_sum
      intro K _
      by_cases hn : (B.fiberRows j J K).Nonempty
      · exact hfiber j J K hn
      · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
        simp only [Finset.card_empty, Nat.cast_zero]
        exact mul_nonneg hC (Real.rpow_nonneg hU.le _)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Sum the actual supported-witness partition at the balanced unmarked
cutoff. This incurs only the displayed label and two dyadic-length counts. -/
theorem batch_count_from_unmarked_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm : ℝ) (hεm : 0 < εm) :
    ∃ c κ K₀ : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < κ ∧ 0 ≤ K₀ ∧
      ∀ᶠ U : ℝ in atTop,
        ∀ (a ε T allowance C height : ℝ) (i : ℕ),
        1 < U → 1 / 2 ≤ a → 2 * a - 1 ≤ 5 / 6 → 0 ≤ ε → ε ≤ 1 / 1000 →
        0 ≤ C → 0 ≤ height → 2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height →
        ∀ {Label : Type*} [Fintype Label]
          (B : UnmarkedBatch Label U a ε (unmarkedCutoff (2 * a - 1)) T allowance i),
        (∀ j J K, ∀ hne : (B.fiberRows j J K).Nonempty,
          UnmarkedMoments (B.fiber j J K hne) c κ C height εm) →
        (B.rows.card : ℝ) ≤ (Fintype.card Label : ℝ) * (dyadicLength U : ℝ)^2 *
          fiberConstant C height K₀ * U ^ (unmarkedDensity (2 * a - 1) + 156 * ε + εm) := by
  obtain ⟨c, κ, K₀, hc, hc1, hκ, hK, hcount⟩ := count_from_unmarked_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c, κ, K₀, hc, hc1, hκ, hK, ?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε T allowance C height i hU ha hδ hε hεsmall hC hh hf Label _ B moments
  apply B.card_bound (fiberConstant C height K₀) _
    (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU)
  intro j J K hne
  exact hcount a ε T allowance C height i hU ha hδ hε hεsmall hC hh hf
    (B.fiber j J K hne) (moments j J K hne)

end SevenEighths.LocalMoment
end
end OAI

end
/- END ORIGINAL LocalMoment.UnmarkedBatch -/

/- BEGIN ORIGINAL LocalMoment.ActualUnmarkedInputs; sha256 043aa665989b02e5e51641470375b6e0ddd56e77f729c5300d1685e2cfbf7971 -/
section
                                
                                                                   
                                                            

set_option autoImplicit false

/-! Actual incumbent inverse moments, actual buffered-zero witnesses, and
the cost of the finite label/dyadic partition for the unmarked batch.

This removes an inverse-moment assumption for a fixed finite family of
`RowData`; it does not provide the unmarked plain moment or identify the
joint physical row with that family. The witness constructor retains the
nonprincipal, conductor, coefficient, and buffered-maximum conditions. -/

namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set Filter
namespace SevenEighths.LocalMoment
open HeckeFamily HeckeInverseAmplification HeckeDetectorSupportedWitness
open HeckeDetectorWitnessRows HeckeDetectorCoefficientTransfer
open HeckeDetectorDyadicProfiles HeckeDetectorRawFiber
open HeckeDetectorInverseFiberCount HeckeDetectorProfiles

private theorem rawMoment_mono_constant (data : RowData) (W : ℝ → ℂ)
    (c κ A B : ℝ) (hAB : A ≤ B) (h : RawMoment data W c κ A) :
    RawMoment data W c κ B := by
  intro X D hX hD hcap rows hrows
  apply (h X D hX hD hcap rows hrows).trans
  gcongr

/-- One incumbent constant works for a fixed finite character-label family,
uniformly over all dyadic lengths, orientations, and independent frequencies.
The input contains no assumed raw moment. -/
theorem fixed_family_inverse_raw {Label : Type*} [Fintype Label]
    (data : Label → RowData) (c κ : ℝ) (hc : 0 < c) (hκ : 0 < κ) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ label reverse, ∀ n : ℕ, n ≤ 2 → ∀ U : ℝ, 0 < U →
      ∀ tstar r : ℝ, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ height t : ℝ, 0 ≤ height → t ∈ Icc (-height) height →
        let W := twistProfile (logTest
          (orientedProfile reverse (inverseTest U tstar r)) n) s t
        RawMoment (data label) W c κ (C * (1 + height)^J) ∧
        RawMoment (data label) (scaleProfile W) c κ (C * (1 + height)^J) := by
  obtain ⟨J, hJ⟩ := ProbeDetectorInverseRawField.fixed_raw_profiles c κ hc hκ
  choose A hA hbound using (fun label => hJ (data label))
  let C : ℝ := 1 + ∑ label, A label
  have hsum : 0 ≤ ∑ label, A label := Finset.sum_nonneg (fun j _ => (hA j).le)
  have hC : 0 < C := by dsimp [C]; linarith
  have hAC (label) : A label ≤ C := by
    have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (hA j).le)
      (Finset.mem_univ label)
    dsimp [C]
    linarith
  refine ⟨J, C, hC, ?_⟩
  intro label reverse n hn U hU tstar r s hs height t hh ht
  have hb := hbound label reverse n hn U hU tstar r s hs height t hh ht
  have hconst : A label * (1 + height)^J ≤ C * (1 + height)^J :=
    mul_le_mul_of_nonneg_right (hAC label) (by positivity)
  exact ⟨rawMoment_mono_constant _ _ _ _ _ _ hconst hb.1,
    rawMoment_mono_constant _ _ _ _ _ _ hconst hb.2⟩

/-- With the actual incumbent inverse input supplied above, only the plain
unmarked field remains to build `UnmarkedMoments` for every batch fiber. -/
theorem batch_moments_of_plain_unmarked {Label : Type*} [Fintype Label]
    (data : Label → RowData) (c κ : ℝ) (hc : 0 < c) (hκ : 0 < κ) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ {U a ε tstar T allowance εm height : ℝ} {i : ℕ},
      0 < U → 0 ≤ height →
      ∀ (B : UnmarkedBatch Label U a ε tstar T allowance i), B.data = data →
      ∀ label left right, ∀ hne : (B.fiberRows label left right).Nonempty,
        let F := B.fiber label left right hne
        (∀ j k : ℕ, j + k ≤ 2 → ∀ s ∈ Icc (0 : ℝ) 1,
          ∀ t ∈ Icc (-height) height,
          ∑ u ∈ F.rows, ‖HeckeDyadic.polynomial (F.family u F.label) false
            ((HeckeDetectorRowwisePolynomial.logProfile^[j]) positiveAnnular)
            (U^F.m) s t * HeckeDyadic.polynomial (F.family u F.label) false
            ((HeckeDetectorRowwisePolynomial.logProfile^[k]) positiveAnnular)
            (U^F.m) s t‖^2 ≤
              (C * (1 + height)^J) * U^(max 1 (2 * F.m) + εm)) →
        UnmarkedMoments F c κ (C * (1 + height)^J) height εm := by
  obtain ⟨J, C, hC, hraw⟩ := fixed_family_inverse_raw data c κ hc hκ
  refine ⟨J, C, hC, ?_⟩
  intro U a ε tstar T allowance εm height i hU hh B hd label left right hne F hp
  refine ⟨?_, hp⟩
  intro n hn s hs t ht
  have hdata : F.rowData = data label := by
    change B.data label = data label
    rw [hd]
  rw [hdata]
  exact hraw label F.reverse n hn U hU tstar F.r s hs height t hh ht

/-- Construct supported witnesses from actual buffered maxima on just the
nonempty source set, and retain the exact coefficient dictionary. No
detector witness is postulated for an arbitrary ambient free row. -/
theorem unmarked_batch_from_actual_maxima
    (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax) (hτ : 0 < τ)
    (hτzero : τ < dmin / 2) (hτheight : 4 * τ < dmin * η)
    (hε : 0 < ε) (he : 0 < e) (he' : e < 1 / 1000)
    (hκ : 0 < κ) (hκ' : κ ≤ 1) (hη : 0 ≤ η)
    (hbudget : 12 * e * ((22 : ℝ) + 2) + 8 * κ + 2 * η ≤ ε / 2) :
    ∃ Z₀ : ℝ, ∀ Z : ℝ, Z₀ ≤ Z → ∀ d : ℝ, dmin ≤ d → d ≤ dmax →
      ∀ {Label : Type*} [Fintype Label] (rows : Finset FreeRow), rows.Nonempty →
      ∀ (family : rows → Label → Character)
        (hχ : ∀ u j, (family u j).residue ≠ 1)
        (data : Label → RowData) (reverse : Label → Bool),
      (∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ Z^d) →
      (∀ u : rows, ∀ j, ∀ Q : Ideal O, idealCoeff (family u j) Q =
        if reverse j then starRingEnd ℂ
          (idealCoeff ((data j).character ⟨u.val.val, u.val.property.1⟩) Q)
        else idealCoeff ((data j).character ⟨u.val.val, u.val.property.1⟩) Q) →
      ∀ (a : ℝ) (i : ℕ), i ≤ I → 51 / 100 < a → a ≤ 1 →
      (∀ u, HeckeDetectorZeros.zeroMaximum (family u) (hχ u)
        (3 * (i + 1 : ℕ) * Z^τ) < a + 2 * e) →
      (∀ u, a ≤ HeckeDetectorZeros.zeroMaximum (family u) (hχ u)
        ((3 * i : ℕ) * Z^τ)) →
      (∀ u j, (family u j).modulus.absNorm ≤ Z^d) →
      ∀ tstar : ℝ, 1 ≤ tstar → tstar ≤ 3 / 2 →
        ∃ B : UnmarkedBatch Label (Z^d) a ε tstar (Z^τ)
          ((Z^d)^(τ / (2 * dmax))) i,
          B.rows = rows ∧ B.data = data ∧ B.reverse = reverse ∧
          ∀ u : rows, B.family u.val = family u := by
  obtain ⟨Z₀, hZ₀⟩ := actual_supported_witness_family dmin dmax τ ε e κ η I
    hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨Z₀, ?_⟩
  intro Z hZ d hd hd' Label _ rows hne family hχ data reverse hrow hcoeff
    a i hi ha ha' hnext hcurrent hQ tstar ht ht'
  obtain ⟨w⟩ := hZ₀ Z hZ d hd hd' family hχ a i hi ha ha' hnext hcurrent hQ
    tstar ht ht'
  obtain ⟨u₀, hu₀⟩ := hne
  let B := UnmarkedBatch.ofSupportedRows rows ⟨u₀, hu₀⟩ family w hrow data reverse hcoeff
  refine ⟨B, rfl, rfl, rfl, ?_⟩
  intro u
  change family (supportedRowRetraction rows ⟨u₀, hu₀⟩ u.val) = family u
  rw [supportedRowRetraction_mem]

/-- The label family is fixed before the row scale. Both dyadic counts
are paid by an arbitrary positive power, with the label cost in a fixed
constant. This assertion would not cover a growing family of labels. -/
theorem fixed_label_dyadic_cost {Label : Type*} [Fintype Label]
    (η : ℝ) (hη : 0 < η) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ U : ℝ in atTop,
      (Fintype.card Label : ℝ) * (dyadicLength U : ℝ)^2 ≤ K * U^η := by
  obtain ⟨K, hK, hbound⟩ := HeckeDetectorClassBudget.dyadic_cost_eventually η hη
  refine ⟨(Fintype.card Label : ℝ) * K, by positivity, ?_⟩
  filter_upwards [hbound] with U hU
  calc
    _ ≤ (Fintype.card Label : ℝ) * (K * U^η) :=
      mul_le_mul_of_nonneg_left hU (by positivity)
    _ = _ := by ring

end SevenEighths.LocalMoment
end
end OAI

end
/- END ORIGINAL LocalMoment.ActualUnmarkedInputs -/
