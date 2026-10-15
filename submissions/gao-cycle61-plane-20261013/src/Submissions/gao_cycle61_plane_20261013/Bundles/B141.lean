/- Cycle61 successor parameter adaptation by Zhongpai Gao, with AI assistance. Nominal θ=4374299/5000000, q=67/100; exact reserves and actual source consumers are changed by scoped ownership maps. Original notices/provenance remain intact. Full source replay and independent verification are pending. -/
/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B089
import Submissions.gao_cycle61_plane_20261013.Bundles.B123
import Submissions.gao_cycle61_plane_20261013.Bundles.B125
import Submissions.gao_cycle61_plane_20261013.Bundles.B126
import Submissions.gao_cycle61_plane_20261013.Bundles.B128
import Submissions.gao_cycle61_plane_20261013.Bundles.B140
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondRadicalBudget

/- BEGIN ORIGINAL Cycle61.Physical.FinalErrorCapacity.Paid; sha256 defc454d0c6c99e99c9c53b887dc832b938f83c5121ad6ebed5f4b4490b38ef7 -/
section
                                                   
                                      

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61FinalErrorCapacity
noncomputable section
open Cycle61.Arithmetic
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
  have hpaid := Cycle61.Physical.paid_deletion_bound (F := F) hd hallowance
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
      -M*(32653211/39417600000)+padding/6 := by
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
      -M*(782473823/39417600000)+padding/6 := by
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
      -M*(60620561/2463600000)+padding/6 := by
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
end OAI.SevenEighths.Cycle61FinalErrorCapacity

end
/- END ORIGINAL Cycle61.Physical.FinalErrorCapacity.Paid -/

/- BEGIN ORIGINAL Cycle61.Physical.FinalError.Chain; sha256 056c323860e24229cd0b33673e0b26fc059907be130435374287223e616ac1ad -/
section
                                               
                                                    
                                    
                                          
                                     
                                 

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61FinalError
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
open Cycle61Moment.LowBranch Cycle61FinalNatural Cycle61FinalCapacity Cycle61FinalErrorCapacity
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
  hk : 1≤ k
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
    (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (s : Input α) (η₀ : Character) (θ : α→ RayQuotient.Characters M H)
    (w σ freq : α→ℝ) (W : ℝ→ℂ) (bslot Z Bmask : ℝ) (hZ : 1< Z)
    (hm : Matches M H hH s η₀ θ w σ freq W bslot Z) (q : Chain s)
    (η : Character) (v : ℝ) (Q : Ideal O) (hP : q.R₂*q.E₂≠0)
    (hPN : ((q.R₂*q.E₂).absNorm:ℝ)≤ Z^Bmask) (R : ℝ)
    (C D : Ideal O) (U : Finset (CommonIndex C D)) (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2))) :
    let st := retainedState Z Bmask hZ η Q (q.R₂*q.E₂) hP hPN R C D U
    let src := q.final η v
    let J := q.indices L a
    finalPositiveEnergy src second L a st.radial.keep st.radial.profile st.radial.scale =
      energy st.character st.mask 1 v
        (dilated s.W₁ (clipDilation (Cycle61.Physical.sourcePlainScales src.toSource second 0/
          (Ideal.absNorm (selectedPlain L a 0):ℝ))))
        (dilated s.W₂ (clipDilation (Cycle61.Physical.sourcePlainScales src.toSource second 1/
          (Ideal.absNorm (selectedPlain L a 1):ℝ))))
        (fun j : J=>primePool M H bslot (Z^(w j)))
        (fun (j : J) I=>idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
          annularWeight W (Z^(w j)) (σ j) (freq j) I)
        (fun j : J=>Z^(w j)) (finalPlain src second L a 0) (finalPlain src second L a 1)
        st.radial.keep st.radial.profile st.radial.scale := by
  dsimp only
  have hc := Cycle61ChildMatches.actual_twice_child_matches M H hH s η₀ θ w σ freq W bslot Z hm
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

theorem original_slot_sum (s : Input α) (q : Chain s) (η : Character) (v Z : ℝ) (hZ : 1< Z)
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
    Cycle61.Physical.sourcePlainScales (commonData (withHeight s η v) C R B).toSource second j ≤
      Cycle61.Physical.sourcePlainScales s.toData.toSource second j := by
  have hn (i : Fin 2) : (1:ℝ)≤(B.val (Sum.inr i)).absNorm := norm_ge_one _ (alloc_ne s C B _)
  cases second <;> fin_cases j
  · exact div_le_self s.X₁_pos.le (hn 0)
  · exact div_le_self s.X₂_pos.le (hn 1)
  · exact div_le_self s.Y₁_pos.le (hn 0)
  · exact div_le_self s.Y₂_pos.le (hn 1)

theorem final_plain_cap (s : Input α) (q : Chain s) (η : Character) (v Z Lbound : ℝ)
    (hZ : 1< Z) (hL : 0≤ Lbound)
    (hcap : ∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^Lbound)
    (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2)))
    (j : Fin 2) : finalPlain (q.final η v) second L a j≤ Z^Lbound := by
  have h₁ := allocated_plain_le s q.C₁ q.R₁ q.B₁ q.η₁ q.t₁ second j
  have hp := allocated_plain_le q.first ((Ideal.span {q.p})^q.k) (q.R₁*q.C₁) q.Bp q.υ q.t₂ second j
  have h₂ := allocated_plain_le q.extracted q.E₂ q.R₂ q.B₂ η v second j
  have hsrc : Cycle61.Physical.sourcePlainScales (q.final η v).toSource second j≤ Z^Lbound :=
    (h₂.trans (hp.trans h₁)).trans (hcap second j)
  have hx := source_plain_positive (q.final η v) second j
  have hn : (1:ℝ)≤(selectedPlain L a j).absNorm := norm_ge_one _
    (CenteredMomentDivisorExtraction.selectedDivisor_ne_zero L Finset.univ a (Sum.inr j))
  change max 1 (_/_)≤ _
  exact max_le (Real.one_le_rpow hZ.le hL) ((div_le_self hx.le hn).trans hsrc)

#print axioms final_plain_cap
end
end OAI.SevenEighths.Cycle61FinalError

end
/- END ORIGINAL Cycle61.Physical.FinalError.Chain -/

/- BEGIN ORIGINAL Cycle61.Physical.FinalError.Geometry; sha256 803fa2d5109fa595ff223d8e6db1b5fcde9d1311d13e9f301c5d0ef2a10cee06 -/
section
                                        

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61FinalError
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCompleteCommon CenteredMomentSecondHeightFamily ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondPhysicalBlock CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentCommonRadialData CenteredMomentCommonRawScale
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open Cycle61FinalNatural Cycle61FinalCapacity Cycle61FinalErrorCapacity
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

def errorRadius {s : Input α} (q : Chain s) (D₁ : Ideal O) (E : Finset (CommonIndex q.C₁ D₁))
    (Z Mrow amp δ reserve ξ b : ℝ) (N : ℕ) : ℝ :=
  frequencyRadius ((b^N*volume s/((q.C₁.absNorm:ℝ)*(normValue q.p)^q.k))^2/
    errorCommonRadius Z (Real.logb Z (D₁.absNorm:ℝ))
      (nominalLog q.C₁ D₁ (Ideal.span {primeSubsetGenerator (fun j:CommonIndex q.C₁ D₁=>j.val) E})
        (Z^Mrow) (volume s) Z) (Real.logb Z (q.C₁.absNorm:ℝ)) (3*amp) δ reserve q.p q.k) Z ξ

/-- Original and extracted conductor data and the actual second block.
 There is no capacity, final-width or moment-bound field. -/
structure Geometry (s : Input α) (q : Chain s) (Z Mrow amp omega ξ b J : ℝ) (N : ℕ) where
  D₁ : Ideal O
  hC₁ : Supported q.C₁
  hD₁ : Supported D₁
  heq₁ : primeSupport q.C₁=primeSupport D₁
  E : Finset (CommonIndex q.C₁ D₁)
  hmod : q.η₁.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
    Ideal.span {primeSubsetGenerator (fun j:CommonIndex q.C₁ D₁=>j.val) E*activeConductor q.C₁ D₁}
  moving_modulus : (q.υ.modulus.absNorm:ℝ)≤ J*(q.η₁.modulus.absNorm:ℝ)*Z^(errorMoving q.p Z q.k)
  δ : ℝ
  reserve : ℝ
  homega : δ+reserve=omega
  C : Ideal O
  D : Ideal O
  hC : Supported C
  hD : Supported D
  heq : primeSupport C=primeSupport D
  U : Finset (CommonIndex C D)
  τ : RayFourExpansion.RayCharacter→ Character
  family : Family q.υ C D hC hD U τ
  label : q.E₂=C ∨ q.E₂=D
  first_nonzero : frozenCoefficient q.B₁.val q.C₁ q.R₁ s.ν s.W s.P≠0
  second_nonzero : frozenCoefficient q.B₂.val q.E₂ q.R₂ q.extracted.ν q.extracted.W q.extracted.P≠0
  cols : Finset (Ideal O)
  coefficient : Ideal O→ℂ
  frequencies : Finset O
  profile : SchwartzMap ℝ ℂ
  scale : ℝ
  scale_pos : 0< scale
  bin : Fin 4→ℤ
  block_nonzero : physicalBlock q.υ q.t₂ cols coefficient C D hC hD U
    (errorRadius q D₁ E Z Mrow amp δ reserve ξ b N) frequencies profile scale bin≠0

def Geometry.radius {s : Input α} {q : Chain s} {Z Mrow amp omega ξ b J : ℝ} {N : ℕ}
    (g : Geometry s q Z Mrow amp omega ξ b J N) := errorRadius q g.D₁ g.E Z Mrow amp g.δ g.reserve ξ b N

def Geometry.nominal {s : Input α} {q : Chain s} {Z Mrow amp omega ξ b J : ℝ} {N : ℕ}
    (g : Geometry s q Z Mrow amp omega ξ b J N) :=
  errorNominal Mrow Z amp omega (errorRemoval q.p Z q.k) (errorMoving q.p Z q.k)
    q.C₁ g.D₁ g.C g.D g.U

omit [DecidableEq α] in
theorem error_state_width {s : Input α} {q : Chain s} {Z Mrow amp omega ξ b J : ℝ} {N : ℕ}
    (g : Geometry s q Z Mrow amp omega ξ b J N) (Bmask : ℝ) (hZ : 1< Z) (hb : 0< b) (hJ : 0< J)
    (χ : RayFourExpansion.RayCharacter) (Q : Ideal O) (hP : q.R₂*q.E₂≠0)
    (hPN : ((q.R₂*q.E₂).absNorm:ℝ)≤ Z^Bmask) :
    (retainedState Z Bmask hZ (g.τ χ) Q (q.R₂*q.E₂) hP hPN g.radius g.C g.D g.U).width ≤
      g.nominal+(Real.logb Z (s.η.modulus.absNorm:ℝ)+
        Real.logb Z CenteredMomentFirstPhysicalSource.fixedPresentationCost+2*(N:ℝ)*Real.logb Z b+
        ξ/2+Real.logb Z J+Real.logb Z (4*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ))) := by
  have hh := actual_error_retainedState_width s.η q.η₁ q.υ q.C₁ g.D₁ g.hC₁ g.hD₁ g.heq₁ g.E
    (Z^Mrow) (volume s) Z amp g.δ g.reserve ξ b J N q.p q.k q.hp
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) (volume_pos s) hZ hb hJ g.hmod g.moving_modulus
    g.C g.D g.hC g.hD g.U g.τ g.family q.t₂ g.cols g.coefficient g.frequencies
    g.profile g.scale g.scale_pos g.bin Bmask χ Q _ hP hPN g.block_nonzero
  rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh
  change (retainedState Z Bmask hZ (g.τ χ) Q (q.R₂*q.E₂) hP hPN g.radius g.C g.D g.U).width≤ _ at hh
  unfold Geometry.nominal errorNominal
  linarith [g.homega]

theorem error_source_capacity {s : Input α} {q : Chain s} {Z Mrow amp omega ξ b J : ℝ}
    (g : Geometry s q Z Mrow amp omega ξ b J (Fintype.card α)) (hb : 1≤ b)
    (hs : s.upper≤ b) (hZ : 1< Z) (hM : 0< Mrow) (hP : ∀j,1≤ s.P j)
    (hz : (17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow)
    (haff : CenteredMomentEnergyBands.length Z s.X₁+CenteredMomentEnergyBands.length Z s.X₂+
      Cycle61.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤ Cycle61.Arithmetic.B*Mrow)
    (η : Character) (v : ℝ) (second : Bool) (L : Ideal O)
    (a : CenteredMomentDivisorAllocation.Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2))) (z : O)
    (hne : Cycle61.Physical.sourcePositiveRow (q.final η v).toSource second L a z≠0) :
    let cell := Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
    CenteredMomentEnergyBands.length Z (Cycle61Moment.LowBranch.finalPlain (q.final η v) second L a 0)+
      CenteredMomentEnergyBands.length Z (Cycle61Moment.LowBranch.finalPlain (q.final η v) second L a 1)+
        (9/2)*CenteredMomentAllocatedChildCapacity.remainingLogs L a Z (q.final η v).P-g.nominal ≤
      Mrow*Cycle61.Arithmetic.g cell+3*amp+(errorRemoval q.p Z q.k-errorMoving q.p Z q.k)+omega+
        supportPadding (Fintype.card α) b s.b₁ s.b₂ Z := by
  exact actual_error_source_capacity (Fintype.card α) b hb s le_rfl hs q.C₁ q.R₁ q.B₁
    g.first_nonzero q.η₁ q.t₁ (Ideal.span {q.p}) (Ideal.span_singleton_eq_bot.not.mpr q.hp)
    q.k q.coprime q.Bp η v g.C g.D q.E₂ q.R₂ g.label q.B₂ g.second_nonzero
    g.D₁ g.hD₁.1 g.hC g.hD g.heq g.U L a Z Mrow amp omega (errorMoving q.p Z q.k)
    hZ hM hP (actual_prime_widths q.p q.hp Z hZ q.k q.hk).2.2 hz haff second z hne

#print axioms error_state_width
#print axioms error_source_capacity
end
end OAI.SevenEighths.Cycle61FinalError

end
/- END ORIGINAL Cycle61.Physical.FinalError.Geometry -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorModulus; sha256 6cd87597e9eb19624818aaee558a056907b6bf3d1c7ba2fe39a7ae7a1cdcb5d7 -/
section
                                                            
                                                              

set_option autoImplicit false
set_option maxHeartbeats 900000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentSecondHeightFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentChildRows CenteredMomentAmplificationRadicalFamily
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentAmplificationErrorEnergy CenteredMomentSecondRadicalBudget
local notation "O" => HeckeFamily.O

/-- The conductor furnished by actual amplification has one uniform
fixed factor and exactly the moving-prime power used in the error geometry. -/
theorem actual_error_moving_modulus (η υ : Character)(ψ : RayCharacter)
    (p : O)(hp : p≠0)(Z : ℝ)(hZ : 1< Z)(i : Fin 3)
    (hυ : υ.modulus.absNorm≤ radicalBound (childCharacter η ψ) fixedBadMask p
      (errorMovingExponent (errorIndex i))) :
    (υ.modulus.absNorm:ℝ)≤(fixedFactor:ℝ)*(η.modulus.absNorm:ℝ)*
      Z^(errorMoving p Z (errorIndex i+1)) := by
  have hh : (υ.modulus.absNorm:ℝ)≤
      (radicalBound (childCharacter η ψ) fixedBadMask p (errorMovingExponent (errorIndex i)):ℝ) := by
    exact_mod_cast hυ
  rw [radicalBound_error_power _ _ p hp Z hZ (errorIndex i) (errorIndex_cases i)] at hh
  have hm : ((childCharacter η ψ).modulus.absNorm:ℝ)≤
      (η.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm := by
    exact_mod_cast child_modulus_bound η ψ
  apply hh.trans
  calc
    _≤(((η.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)*
        (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm)*
          Z^(errorMoving p Z (errorIndex i+1)) := by
      have hz : 0< Z := zero_lt_one.trans hZ
      gcongr
    _=_ := by simp only [fixedFactor,Nat.cast_mul];ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_moving_modulus

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorModulus -/
