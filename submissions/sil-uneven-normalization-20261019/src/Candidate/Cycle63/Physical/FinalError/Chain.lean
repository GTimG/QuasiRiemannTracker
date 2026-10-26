import Candidate.Cycle63.Physical.FinalErrorCapacity.Physical
import Candidate.Cycle63.Physical.TerminalLedger
import Candidate.Cycle63.Physical.FinalCapacity.UniformPadding
import Candidate.Cycle63.Physical.ChildMatches
import Candidate.Cycle63.Physical.FinalNatural.Error
import Candidate.Cycle63.Physical.FinalProfiles
import Candidate.Cycle63.Physical.WidthLoss

/- Original module: Candidate.Cycle63.Physical.FinalErrorCapacity.Paid. -/
section

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63FinalErrorCapacity
noncomputable section
open Cycle63.Arithmetic
open HeckeFamily CompletedGauss CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

theorem actual_prime_widths (p : O) (hp : p ≠ 0) (Z : ℝ) (hZ : 1 < Z)
    (k : ℕ) (hk : 1 ≤ k) :
    errorRemoval p Z k = (k:ℝ)*Real.logb Z ((Ideal.span {p}).absNorm:ℝ) ∧
      0 ≤ errorMoving p Z k ∧ errorMoving p Z k ≤ errorRemoval p Z k := by
  have hQ := Ideal.span_singleton_eq_bot.not.mpr hp
  have hn := CenteredMomentAmplificationChildSourceCaps.norm_ge_one (Ideal.span {p}) hQ
  have hl : 0 ≤ Real.logb Z (normValue p) := Real.logb_nonneg hZ hn
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  constructor
  · rfl
  · unfold errorMoving errorRemoval
    split_ifs <;> constructor <;> nlinarith

/-- The width defect is paid at the same global deletion rate as the
 original retained energy. Outside extraction and squared scalar costs
 remain separate, so the three literal alternatives can be substituted. -/
theorem paid_error_excess_bound {b M widthDefect allowance F w wo scalarLoss padding : ℝ}
    (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) (hM : 0 ≤ M)
    (hd : widthDefect ≤ allowance) (hallowance : 0 ≤ allowance)
    (hwo : wo ≤ w) (hpadding : 0 ≤ padding)
    (hF : F ≤ M*g b+3*(M*amp b)+(w-wo)+padding) :
    widthDefect-allowance+(1/6)*max (F-widthDefect) 0-(w-wo)-scalarLoss ≤
      M*g b/6+M*amp b/2-(5/6)*(w-wo)-scalarLoss+padding/6 := by
  have hpaid := Cycle63.Physical.paid_deletion_bound (F := F) hd hallowance
    (show 0 ≤ (1/6:ℝ) ∧ (1/6:ℝ) ≤ 1 by norm_num)
  have hcap : 0 ≤ M*g b+3*(M*amp b)+(w-wo)+padding := by
    have hg := g_pos hb
    have ha := amp_pos hb
    have hw : 0 ≤ w-wo := sub_nonneg.mpr hwo
    positivity
  have hmax := max_le hF hcap
  linarith

theorem first_paid_error_reserve {b M widthDefect allowance F primeWidth padding : ℝ}
    (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) (hM : 0 ≤ M)
    (hd : widthDefect ≤ allowance) (hallowance : 0 ≤ allowance)
    (hprime : 3*(M*amp b)/4 ≤ primeWidth) (hpadding : 0 ≤ padding)
    (hF : F ≤ M*g b+3*(M*amp b)+padding) :
    widthDefect-allowance+(1/6)*max (F-widthDefect) 0-primeWidth ≤
      -M*(530959781/482529600000)+padding/6 := by
  have hp := paid_error_excess_bound (F := F) (w := primeWidth) (wo := primeWidth)
    (scalarLoss := primeWidth) hb hM hd hallowance le_rfl hpadding (by linarith)
  have hr := mul_le_mul_of_nonneg_left (first_error_reserve hb) hM
  nlinarith

theorem sixth_paid_error_reserve {b M widthDefect allowance F primeWidth padding : ℝ}
    (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) (hM : 0 ≤ M)
    (hd : widthDefect ≤ allowance) (hallowance : 0 ≤ allowance)
    (hprime : 3*(M*amp b)/4 ≤ primeWidth) (hpadding : 0 ≤ padding)
    (hF : F ≤ M*g b+3*(M*amp b)+6*primeWidth+padding) :
    widthDefect-allowance+(1/6)*max (F-widthDefect) 0-6*primeWidth ≤
      -M*(11360006033/482529600000)+padding/6 := by
  have ha := amp_pos hb
  have hl : 0 ≤ primeWidth := by nlinarith
  have hp := paid_error_excess_bound (F := F) (w := 6*primeWidth) (wo := 0) (scalarLoss := 0)
    hb hM hd hallowance (by linarith) hpadding (by linarith)
  have hr := mul_le_mul_of_nonneg_left (sixth_error_reserve hb) hM
  nlinarith

theorem seventh_paid_error_reserve {b M widthDefect allowance F primeWidth padding : ℝ}
    (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) (hM : 0 ≤ M)
    (hd : widthDefect ≤ allowance) (hallowance : 0 ≤ allowance)
    (hprime : 3*(M*amp b)/4 ≤ primeWidth) (hpadding : 0 ≤ padding)
    (hF : F ≤ M*g b+3*(M*amp b)+6*primeWidth+padding) :
    widthDefect-allowance+(1/6)*max (F-widthDefect) 0-7*primeWidth ≤
      -M*(3516816899/120632400000)+padding/6 := by
  have ha := amp_pos hb
  have hl : 0 ≤ primeWidth := by nlinarith
  have hp := paid_error_excess_bound (F := F) (w := 7*primeWidth) (wo := primeWidth)
    (scalarLoss := primeWidth) hb hM hd hallowance (by linarith) hpadding (by linarith)
  have hr := mul_le_mul_of_nonneg_left (seventh_error_reserve hb) hM
  nlinarith

#print axioms actual_prime_widths
#print axioms paid_error_excess_bound
#print axioms first_paid_error_reserve
#print axioms sixth_paid_error_reserve
#print axioms seventh_paid_error_reserve
end
end OAI.SevenEighths.Cycle63FinalErrorCapacity
end

/- Original module: Candidate.Cycle63.Physical.FinalError.Chain. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63FinalError
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
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
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale CenteredMomentAllocatedChildCapacity
open CenteredMomentAmplificationChildSourceCaps
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity Cycle63FinalErrorCapacity
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

structure Chain (s : Input α) where
  C₁ : Ideal O
  R₁ : Ideal O
  B₁ : actualAllocations s.pools C₁
  η₁ : Character
  t₁ : ℝ
  p : O
  hp : p≠0
  k : ℕ
  hk : 1≤k
  coprime : ∀i,∀I∈(child s C₁ R₁ B₁ η₁ t₁).slots i,IsCoprime (Ideal.span {p}) I
  Bp : actualAllocations (child s C₁ R₁ B₁ η₁ t₁).pools ((Ideal.span {p})^k)
  υ : Character
  t₂ : ℝ
  E₂ : Ideal O
  R₂ : Ideal O
  B₂ : actualAllocations (twiceChild s C₁ R₁ B₁ η₁ t₁ (Ideal.span {p}) k Bp υ t₂).pools E₂

def Chain.first {s : Input α} (q : Chain s) := child s q.C₁ q.R₁ q.B₁ q.η₁ q.t₁
def Chain.extracted {s : Input α} (q : Chain s) :=
  twiceChild s q.C₁ q.R₁ q.B₁ q.η₁ q.t₁ (Ideal.span {q.p}) q.k q.Bp q.υ q.t₂
def Chain.final {s : Input α} (q : Chain s) (η : Character) (v : ℝ) :=
  commonData (withHeight q.extracted η v) q.E₂ q.R₂ q.B₂
def Chain.embedding {s : Input α} (q : Chain s) :
    CenteredMomentCommonProfile.liveIndices q.B₂.val ↪ α :=
  ((originalEmbedding q.extracted q.E₂ q.B₂).trans
    (originalEmbedding q.first ((Ideal.span {q.p})^q.k) q.Bp)).trans
    (originalEmbedding s q.C₁ q.B₁)
def Chain.indices {s : Input α} (q : Chain s) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2))) :=
  (CenteredMomentDivisorRaw.liveIndices L a).map q.embedding

theorem original_positive_energy (M : Ideal O) [NeZero M]
    (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (s : Input α) (η₀ : Character) (θ : α→RayQuotient.Characters M H)
    (w σ freq : α→ℝ) (W : ℝ→ℂ) (bslot Z Bmask : ℝ) (hZ : 1<Z)
    (hm : Matches M H hH s η₀ θ w σ freq W bslot Z) (q : Chain s)
    (η : Character) (v : ℝ) (Q : Ideal O) (hP : q.R₂*q.E₂≠0)
    (hPN : ((q.R₂*q.E₂).absNorm:ℝ)≤Z^Bmask) (R : ℝ)
    (C D : Ideal O) (U : Finset (CommonIndex C D)) (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2))) :
    let st := retainedState Z Bmask hZ η Q (q.R₂*q.E₂) hP hPN R C D U
    let src := q.final η v
    let J := q.indices L a
    finalPositiveEnergy src second L a st.radial.keep st.radial.profile st.radial.scale =
      energy st.character st.mask 1 v
        (dilated s.W₁ (clipDilation (Cycle63.Physical.sourcePlainScales src.toSource second 0/
          (Ideal.absNorm (selectedPlain L a 0):ℝ))))
        (dilated s.W₂ (clipDilation (Cycle63.Physical.sourcePlainScales src.toSource second 1/
          (Ideal.absNorm (selectedPlain L a 1):ℝ))))
        (fun j : J=>primePool M H bslot (Z^(w j)))
        (fun (j : J) I=>idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
          annularWeight W (Z^(w j)) (σ j) (freq j) I)
        (fun j : J=>Z^(w j)) (finalPlain src second L a 0) (finalPlain src second L a 1)
        st.radial.keep st.radial.profile st.radial.scale := by
  dsimp only
  have hc := Cycle63ChildMatches.actual_twice_child_matches M H hH s η₀ θ w σ freq W bslot Z hm
    q.C₁ q.R₁ q.B₁ q.η₁ q.t₁ (Ideal.span {q.p}) q.k q.Bp q.υ q.t₂
  unfold Chain.final
  have he := actual_positive_natural_energy M H hH q.extracted η₀
    (fun j=>θ j.val.val) (fun j=>w j.val.val) (fun j=>σ j.val.val) (fun j=>freq j.val.val)
    W bslot Z Bmask hZ hc q.E₂ q.R₂ q.B₂ η v Q hP hPN R C D U second L a (fun _=>True)
  simp only [and_true] at he
  rw [he]
  exact CenteredMomentEnergyReindex.energy_subset_map q.embedding
    (CenteredMomentDivisorRaw.liveIndices L a) η (fixedBadMask*idealGenerator (q.R₂*q.E₂)) 1
    _ _ (fun j=>primePool M H bslot (Z^(w j)))
    (fun j I=>idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
      annularWeight W (Z^(w j)) (σ j) (freq j) I)
    (fun j=>Z^(w j)) v _ _ _ _ _

theorem original_slot_sum (s : Input α) (q : Chain s) (η : Character) (v Z : ℝ) (hZ : 1<Z)
    (w : α→ℝ) (hP : ∀j,s.P j=Z^(w j)) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2))) :
    remainingLogs L a Z (q.final η v).P = ∑j∈q.indices L a,w j := by
  rw [Chain.indices,Finset.sum_map]
  apply Finset.sum_congr rfl
  intro j hj
  change Real.logb Z (s.P j.val.val.val)=w j.val.val.val
  rw [hP,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']

#print axioms original_positive_energy
#print axioms original_slot_sum

theorem allocated_plain_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (η : Character) (v : ℝ) (second : Bool) (j : Fin 2) :
    Cycle63.Physical.sourcePlainScales (commonData (withHeight s η v) C R B).toSource second j ≤
      Cycle63.Physical.sourcePlainScales s.toData.toSource second j := by
  have hn (i : Fin 2) : (1:ℝ)≤(B.val (Sum.inr i)).absNorm := norm_ge_one _ (alloc_ne s C B _)
  cases second <;> fin_cases j
  · exact div_le_self s.X₁_pos.le (hn 0)
  · exact div_le_self s.X₂_pos.le (hn 1)
  · exact div_le_self s.Y₁_pos.le (hn 0)
  · exact div_le_self s.Y₂_pos.le (hn 1)

theorem final_plain_cap (s : Input α) (q : Chain s) (η : Character) (v Z Lbound : ℝ)
    (hZ : 1<Z) (hL : 0≤Lbound)
    (hcap : ∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^Lbound)
    (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2)))
    (j : Fin 2) : finalPlain (q.final η v) second L a j≤Z^Lbound := by
  have h₁ := allocated_plain_le s q.C₁ q.R₁ q.B₁ q.η₁ q.t₁ second j
  have hp := allocated_plain_le q.first ((Ideal.span {q.p})^q.k) (q.R₁*q.C₁) q.Bp q.υ q.t₂ second j
  have h₂ := allocated_plain_le q.extracted q.E₂ q.R₂ q.B₂ η v second j
  have hsrc : Cycle63.Physical.sourcePlainScales (q.final η v).toSource second j≤Z^Lbound :=
    (h₂.trans (hp.trans h₁)).trans (hcap second j)
  have hx := source_plain_positive (q.final η v) second j
  have hn : (1:ℝ)≤(selectedPlain L a j).absNorm := norm_ge_one _
    (CenteredMomentDivisorExtraction.selectedDivisor_ne_zero L Finset.univ a (Sum.inr j))
  change max 1 (_/_)≤_
  exact max_le (Real.one_le_rpow hZ.le hL) ((div_le_self hx.le hn).trans hsrc)

#print axioms final_plain_cap
end
end OAI.SevenEighths.Cycle63FinalError
end
