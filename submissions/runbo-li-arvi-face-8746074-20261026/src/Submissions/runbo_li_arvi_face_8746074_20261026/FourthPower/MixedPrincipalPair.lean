/- Copyright (c) 2026 Sil. Apache-2.0.
The actual pair of genuinely frozen, artificially masked principal rows.
All analytic estimates are supplied by MixedPrincipalMasked. The record
below contains only original data and concrete support/numeric conditions.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedPrincipalMasked

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedPrincipalPair
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentLattice CenteredMomentFiniteProfileExceptional CenteredMomentNaturalRowSource
open CenteredMomentSecondHeightFamily CenteredMomentCommonRawScale CenteredMomentCommonRawCost
open CenteredMomentFirstSectors CenteredMomentSourceProfileMass
open CenteredMomentAllocatedNaturalRadial
open CenteredMomentSourceRectangle
open MixedPrincipalCentered MixedPrincipalPositivePart MixedPrincipalFrozen MixedPrincipalMasked
open MixedCommonCoefficient MixedCommonRestriction MixedLiteralAllocation MixedDivisorMask
open MixedLiveRows MixedLiveNormalization
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Original source data, including the genuine frozen allocation.
No estimate of a row, source or energy occurs in this record. -/
structure Source (ι : Type*) [Fintype ι] (a b : ℝ) where
  S : Finset PrimeIdeal
  H : Finset PrimeIdeal
  pool : ι→Finset Id
  d : Id×Id
  hd : d.1≠0∧d.2≠0
  B : Tuple ι
  hB : ∀j,B j≠0
  G : Id
  R : Id
  Fhole : Id
  hprod : finiteTupleProduct B=G
  hR : R≠0
  hFhole : Fhole≠0
  ν : ι→Id→ℂ
  Wslot : ι→ℝ→ℂ
  P : ι→ℝ
  M : ι→ℝ
  W₁ : 𝓢(ℝ,ℂ)
  W₂ : 𝓢(ℝ,ℂ)
  hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b
  hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b
  t₁ : ℝ
  t₂ : ℝ
  X₁ : ℝ
  X₂ : ℝ
  Y₁ : ℝ
  Y₂ : ℝ
  U₁ : ℝ
  U₂ : ℝ
  T : ℝ
  L : ℝ
  hL : 0<L
  hX₁ : L≤X₁
  hX₂ : L≤X₂
  hY₁ : L≤Y₁
  hY₂ : L≤Y₂
  hXU₁ : X₁≤U₁
  hXU₂ : X₂≤U₂
  hYU₁ : Y₁≤U₁
  hYU₂ : Y₂≤U₂
  hpX : X₁*X₂=T
  hpY : Y₁*Y₂=T
  hP : ∀i,1≤P i
  hM : ∀i,1≤M i
  hpool : ∀i,pool i⊆primeValues S
  hp : ∀i I,I∈pool i→Prime I
  hpn : ∀i I,I∈pool i→Supported I∧(I.absNorm:ℝ)≤2*P i
  hν : ∀i I,‖ν i I‖≤1
  hWnorm : ∀i x,‖Wslot i x‖≤M i
  hW : ∀i,Function.support (Wslot i)⊆Set.Icc (1:ℝ) 2
  hS : ∀P∈S,Supported P.val
  hH : ∀P∈H,P.val∣Fhole
  henclose : ∀I,Supported I→
    ((I.absNorm:ℝ)≤b*(U₁/(d.1*B (Sum.inr 0)).absNorm)∨
      (I.absNorm:ℝ)≤b*(U₂/(d.2*B (Sum.inr 1)).absNorm))→
    QRH.Record1252270103KernelMass.primeSupport I⊆primeValues S

namespace Source
variable {ι : Type*} [Fintype ι] {a b : ℝ} (s : Source ι a b)

def prefixPair : Id×Id := (s.d.1*s.B (Sum.inr 0),s.d.2*s.B (Sum.inr 1))

theorem prefixPair_nonzero : s.prefixPair.1≠0∧s.prefixPair.2≠0 :=
  ⟨mul_ne_zero s.hd.1 (s.hB _),mul_ne_zero s.hd.2 (s.hB _)⟩

theorem common_nonzero : s.G≠0 := by
  rw [←s.hprod]
  exact Finset.prod_ne_zero_iff.mpr (fun j _=>s.hB j)

theorem total_pos : 0<s.T := s.hpX ▸ mul_pos (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂)

/-- Only numerical caps. In particular the conductor bound used later
is the full puncture R*G*D, not its radical and not R alone. -/
def Admissible (N : ℕ) (Bcap Z : ℝ) : Prop :=
  Fintype.card (liveIndices s.B)≤N ∧
  (s.Fhole.absNorm:ℝ)≤Z^Bcap ∧
  (∏i : liveIndices s.B,2*s.P i.val)≤Z^Bcap

def row (ha : 0<a) (χ : Character) (D : Id) : ℂ :=
  frozenWeight (punctureProduct s.S s.H) s.B*
    (normalization (s.X₁*s.X₂) s.P*
      (frozenCoefficient s.B s.G s.R s.ν s.Wslot s.P*
        maskedLiveSum χ s.S s.H s.pool s.d s.hd s.B s.hB s.G s.R D
          s.ν s.Wslot s.P
          (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
          (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
          b s.X₁ s.X₂ s.Y₁ s.Y₂))

def markedCost : ℝ :=
  (∏i : liveIndices s.B,256*s.M i.val)*(∏i : liveIndices s.B,s.M i.val)*
    2^Fintype.card (liveIndices s.B)*((∏i,s.M i)*2^Fintype.card ι)

/-- Full original volume and original prefix denominator. The reciprocal
genuine common norm survives independently of artificial D. -/
def budget (J : ℕ) (control : Finset (ℕ×ℕ)) (Z ε : ℝ) : ℝ :=
  (sourceControl control s.W₁*sourceControl control s.W₂)*Z^ε*
    (1+‖s.t₁‖+‖s.t₂‖)^J*s.markedCost*
    Real.sqrt (s.T*∏i,s.P i)/pairNorm s.d/(s.G.absNorm:ℝ)

def saving (α : ℝ) : ℝ := (max 1 (s.L/prefixNormMax s.prefixPair))^(-α)

theorem budget_nonneg (J : ℕ) (control : Finset (ℕ×ℕ)) (Z ε : ℝ) (hZ : 0≤Z) :
    0≤s.budget J control Z ε := by
  have := sourceControl_nonneg control s.W₁
  have := sourceControl_nonneg control s.W₂
  have hm : 0≤s.markedCost := by
    have h₀ : ∀i,0≤s.M i := fun i=>zero_le_one.trans (s.hM i)
    have h₁ : 0≤∏i : liveIndices s.B,256*s.M i.val :=
      Finset.prod_nonneg (fun i _=>mul_nonneg (by norm_num) (h₀ i.val))
    have h₂ : 0≤∏i : liveIndices s.B,s.M i.val := Finset.prod_nonneg (fun i _=>h₀ i.val)
    have h₃ : 0≤∏i,s.M i := Finset.prod_nonneg (fun i _=>h₀ i)
    unfold markedCost
    positivity
  have := pairNorm_pos s.hd.1 s.hd.2
  unfold budget
  positivity

theorem saving_nonneg (α : ℝ) : 0≤s.saving α :=
  Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _

/-- Exact dictionary for the live row, retaining the ordinary prefixes
and the whole genuine common puncture. -/
theorem live_mask_identity (χ : Character) (D : Id) (V₁ V₂ : ℝ→ℂ) :
    normalization (s.X₁*s.X₂) (fun i : liveIndices s.B=>s.P i.val)*
      maskedLiveSum χ s.S s.H s.pool s.d s.hd s.B s.hB s.G s.R D
        s.ν s.Wslot s.P V₁ V₂ b s.X₁ s.X₂ s.Y₁ s.Y₂=
    maskedRow χ s.S s.H (fun i : liveIndices s.B=>s.pool i.val)
      s.prefixPair s.prefixPair_nonzero D (s.R*s.G) (fun i=>s.ν i.val)
      (fun i=>s.Wslot i.val) (fun i=>s.P i.val) V₁ V₂ b s.X₁ s.X₂ s.Y₁ s.Y₂ := by
  unfold maskedLiveSum maskedRow
  have hbox := source_live_box s.pool s.d s.hd
    (plainSupportPool b s.X₁ s.Y₁) (plainSupportPool b s.X₂ s.Y₂) s.B s.hB
  change liveBox (sourcePools s.pool s.d s.hd b s.X₁ s.X₂ s.Y₁ s.Y₂) s.B s.hB=
    Fintype.piFinset (sourcePools (fun i : liveIndices s.B=>s.pool i.val)
      s.prefixPair s.prefixPair_nonzero b s.X₁ s.X₂ s.Y₁ s.Y₂) at hbox
  rw [hbox]
  rfl
end Source

/-- The same constants supply both actual row bounds, after restoring
the frozen scalar and original normalizations. No row estimate is assumed. -/
theorem uniform_frozen_masked (N : ℕ) (α Bcap a b ε δ : ℝ)
    (hα : 0≤α) (hα4 : α<4/5) (hBcap : 0≤Bcap)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hδ : 0<δ) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),(0,0)∈control ∧
      ∀Q : Id,Q≠0→∃C : ℝ,0<C ∧
      ∀(ι : Type*) [Fintype ι],∀s : Source ι a b,
      ∀Z : ℝ,1≤Z→s.Admissible N Bcap Z→
      ∀(η : Character)(z : O)(D : Id),z≠0→Squarefree D→
      (HeckeRowClosure.rowConductorBound η
        (fixedBadMask*idealGenerator ((s.R*s.G)*D)) 1 z:ℝ)≤Z^Bcap→
      CenteredExceptionalProfile.FixedInducingRow η Q fixedBadMask 1 z→
      ‖s.row ha (naturalCharacter η z) D‖≤
        C*s.budget J control Z ε*(D.absNorm:ℝ)^(δ-(1-α))*s.saving α ∧
      ‖s.row ha (naturalCharacter η z) D‖≤
        C*s.budget J control Z ε*(D.absNorm:ℝ)^(δ-1) := by
  obtain ⟨J,control,h00,hpoint⟩ := uniform_masked_principal N α Bcap a b ε δ
    hα hα4 hBcap ha hb hε hδ
  refine ⟨J,control,h00,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hpoint⟩ := hpoint Q hQ
  refine ⟨C,hC,?_⟩
  intro ι instι s Z hZ hs η z D hz hD hcond hex
  let V₁ := normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁
  let V₂ := normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂
  let c := frozenCoefficient s.B s.G s.R s.ν s.Wslot s.P
  let factor := ‖c‖/Real.sqrt (∏i,frozenScale s.B s.P i)
  let A := C*(sourceControl control s.W₁*sourceControl control s.W₂)*Z^ε*
    (1+‖s.t₁‖+‖s.t₂‖)^J*(∏i : liveIndices s.B,256*s.M i.val)*
    (∏i : liveIndices s.B,s.M i.val)*2^Fintype.card (liveIndices s.B)
  have hfactor : 0≤factor := div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hA : 0≤A := by
    have := sourceControl_nonneg control s.W₁
    have := sourceControl_nonneg control s.W₂
    have h₁ : 0≤∏i : liveIndices s.B,256*s.M i.val :=
      Finset.prod_nonneg (fun i _=>mul_nonneg (by norm_num) (zero_le_one.trans (s.hM i.val)))
    have h₂ : 0≤∏i : liveIndices s.B,s.M i.val :=
      Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.hM i.val))
    have hz0 : 0<Z := zero_lt_one.trans_le hZ
    dsimp [A]
    positivity
  have hweight : ‖frozenWeight (punctureProduct s.S s.H) s.B‖≤1 := by
    unfold frozenWeight
    split_ifs <;> norm_num
  have hrow : ‖s.row ha (naturalCharacter η z) D‖≤
      factor*‖maskedRow (naturalCharacter η z) s.S s.H
        (fun i : liveIndices s.B=>s.pool i.val) s.prefixPair s.prefixPair_nonzero D (s.R*s.G)
        (fun i=>s.ν i.val) (fun i=>s.Wslot i.val) (fun i=>s.P i.val)
        V₁ V₂ b s.X₁ s.X₂ s.Y₁ s.Y₂‖ := by
    unfold Source.row
    rw [norm_mul]
    apply (mul_le_of_le_one_left (norm_nonneg _) hweight).trans_eq
    rw [frozen_live_norm s.B (s.X₁*s.X₂) (by rw [s.hpX];exact s.total_pos.le)
      s.P (fun i=>zero_le_one.trans (s.hP i))]
    rw [s.live_mask_identity]
  have hp := hpoint s.W₁ s.W₂ s.hs₁ s.hs₂ Z hZ s.Fhole D (s.R*s.G)
    s.hFhole hs.2.1 hD (mul_ne_zero s.hR s.common_nonzero) s.S s.H s.hS s.hH
    η z hz hcond hex (liveIndices s.B) hs.1 (fun i=>s.pool i.val) (fun i=>s.ν i.val)
    (fun i=>s.Wslot i.val) (fun i=>s.P i.val) (fun i=>s.M i.val)
    (fun i=>s.hP i.val) (fun i=>s.hM i.val) (fun i=>s.hpool i.val)
    (fun i I hI=>s.hp i.val I hI) (fun i I hI=>s.hpn i.val I hI)
    (fun i I=>s.hν i.val I) (fun i x=>s.hWnorm i.val x) (fun i=>s.hW i.val)
    hs.2.2 s.prefixPair s.prefixPair_nonzero s.t₁ s.t₂ s.X₁ s.X₂ s.Y₁ s.Y₂ s.U₁ s.U₂ s.T s.L
    s.hL s.hX₁ s.hX₂ s.hY₁ s.hY₂ s.hXU₁ s.hXU₂ s.hYU₁ s.hYU₂ s.hpX s.hpY s.henclose
  have hscalar : factor*(A*Real.sqrt (s.T*∏i : liveIndices s.B,s.P i.val)/pairNorm s.prefixPair)≤
      C*s.budget J control Z ε := by
    have hc := frozen_linear_cost s.B s.hB s.G s.R s.common_nonzero s.hprod
      s.ν s.Wslot s.P s.M (fun i=>zero_lt_one.trans_le (s.hP i)) s.hν s.hWnorm s.hM
      1 2 (by norm_num) s.hW
    norm_num only [max_eq_right (show (1:ℝ)≤2 by norm_num)] at hc
    calc
      _ = A*((‖c‖/Real.sqrt (∏i,frozenScale s.B s.P i))*
          (Real.sqrt (s.T*∏i : liveIndices s.B,s.P i.val)/pairNorm s.prefixPair)) := by
        dsimp [factor];ring
      _ = A*((Real.sqrt (s.T*∏i,s.P i)/pairNorm s.d)*(‖c‖/rawReduction s.B s.P)) := by
        dsimp only [Source.prefixPair]
        rw [frozen_volume_scalar s.B s.hB s.d s.hd s.T s.total_pos.le s.P
          (fun i=>zero_lt_one.trans_le (s.hP i)) c]
      _ ≤ A*((Real.sqrt (s.T*∏i,s.P i)/pairNorm s.d)*
          (((∏i,s.M i)*2^Fintype.card ι)/(s.G.absNorm:ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc
          (div_nonneg (Real.sqrt_nonneg _) (pairNorm_pos s.hd.1 s.hd.2).le)) hA
      _ = _ := by dsimp [Source.budget,Source.markedCost,A];ring
  constructor
  · have h := hrow.trans (mul_le_mul_of_nonneg_left hp.1 hfactor)
    change _≤factor*((A*Real.sqrt (s.T*∏i : liveIndices s.B,s.P i.val)/pairNorm s.prefixPair)*
      (D.absNorm:ℝ)^(δ-(1-α))*s.saving α) at h
    calc
      _ ≤ _ := h
      _ = (factor*(A*Real.sqrt (s.T*∏i : liveIndices s.B,s.P i.val)/pairNorm s.prefixPair))*
          (D.absNorm:ℝ)^(δ-(1-α))*s.saving α := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hscalar (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (s.saving_nonneg α)
  · have h := hrow.trans (mul_le_mul_of_nonneg_left hp.2 hfactor)
    change _≤factor*((A*Real.sqrt (s.T*∏i : liveIndices s.B,s.P i.val)/pairNorm s.prefixPair)*
      (D.absNorm:ℝ)^(δ-1)) at h
    calc
      _ ≤ _ := h
      _ = (factor*(A*Real.sqrt (s.T*∏i : liveIndices s.B,s.P i.val)/pairNorm s.prefixPair))*
          (D.absNorm:ℝ)^(δ-1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hscalar (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- Actual paired artificial-divisor sum, with the better of the two
genuine prefix savings. Constants precede both source types and all data.
The two coefficient functions remain literal row expressions throughout. -/
theorem uniform_frozen_masked_pair (N : ℕ) (α Bcap a b ε δ : ℝ)
    (hα : 0≤α) (hα4 : α<4/5) (hBcap : 0≤Bcap)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hδ : 0<δ) (hgap : α+2*δ<1) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),(0,0)∈control ∧
      ∀Q : Id,Q≠0→∃C : ℝ,0<C ∧
      ∀(ι₁ ι₂ : Type u) [Fintype ι₁] [Fintype ι₂],
      ∀(s₁ : Source ι₁ a b)(s₂ : Source ι₂ a b),
      ∀Z : ℝ,1≤Z→s₁.Admissible N Bcap Z→s₂.Admissible N Bcap Z→
      ∀(η₁ η₂ : Character)(z₁ z₂ : O)(Ds : Finset Id)(μ : Id→ℂ),z₁≠0→z₂≠0→
      (∀D∈Ds,Squarefree D)→(∀D∈Ds,‖μ D‖≤1)→
      (∀D∈Ds,(HeckeRowClosure.rowConductorBound η₁
        (fixedBadMask*idealGenerator ((s₁.R*s₁.G)*D)) 1 z₁:ℝ)≤Z^Bcap)→
      (∀D∈Ds,(HeckeRowClosure.rowConductorBound η₂
        (fixedBadMask*idealGenerator ((s₂.R*s₂.G)*D)) 1 z₂:ℝ)≤Z^Bcap)→
      CenteredExceptionalProfile.FixedInducingRow η₁ Q fixedBadMask 1 z₁→
      CenteredExceptionalProfile.FixedInducingRow η₂ Q fixedBadMask 1 z₂→
      (∑D∈Ds,‖μ D‖*‖s₁.row ha (naturalCharacter η₁ z₁) D‖*
        ‖s₂.row ha (naturalCharacter η₂ z₂) D‖)≤
      C*(s₁.budget J control Z ε*s₂.budget J control Z ε)*
        min (s₁.saving α) (s₂.saving α) := by
  obtain ⟨J,control,h00,hpoint⟩ := uniform_frozen_masked N α Bcap a b ε δ
    hα hα4 hBcap ha hb hε hδ
  obtain ⟨K,hK,hmass⟩ := paired_mask_norm_mass α δ hgap
  refine ⟨J,control,h00,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hpoint⟩ := hpoint Q hQ
  refine ⟨C^2*K,mul_pos (sq_pos_of_pos hC) hK,?_⟩
  intro ι₁ ι₂ inst₁ inst₂ s₁ s₂ Z hZ hs₁ hs₂ η₁ η₂ z₁ z₂ Ds μ hz₁ hz₂ hDs hμ
    hc₁ hc₂ he₁ he₂
  let A₁ := C*s₁.budget J control Z ε
  let A₂ := C*s₂.budget J control Z ε
  have hA₁ : 0≤A₁ := mul_nonneg hC.le (s₁.budget_nonneg J control Z ε (zero_le_one.trans hZ))
  have hA₂ : 0≤A₂ := mul_nonneg hC.le (s₂.budget_nonneg J control Z ε (zero_le_one.trans hZ))
  have hsave : 0≤min (s₁.saving α) (s₂.saving α) :=
    le_min (s₁.saving_nonneg α) (s₂.saving_nonneg α)
  have hp (D : Id) (hD : D∈Ds) :
      ‖s₁.row ha (naturalCharacter η₁ z₁) D‖*‖s₂.row ha (naturalCharacter η₂ z₂) D‖≤
      (A₁*A₂)*min (s₁.saving α) (s₂.saving α)*
        ((D.absNorm:ℝ)^(δ-(1-α))*(D.absNorm:ℝ)^(δ-1)) := by
    obtain ⟨h₁,h₁₀⟩ := hpoint ι₁ s₁ Z hZ hs₁ η₁ z₁ D hz₁ (hDs D hD) (hc₁ D hD) he₁
    obtain ⟨h₂,h₂₀⟩ := hpoint ι₂ s₂ Z hZ hs₂ η₂ z₂ D hz₂ (hDs D hD) (hc₂ D hD) he₂
    by_cases hs : s₁.saving α≤s₂.saving α
    · rw [min_eq_left hs]
      apply (mul_le_mul h₁ h₂₀ (norm_nonneg _)
        (mul_nonneg (mul_nonneg hA₁ (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (s₁.saving_nonneg α))).trans_eq
      ring
    · rw [min_eq_right (le_of_not_ge hs)]
      apply (mul_le_mul h₁₀ h₂ (norm_nonneg _)
        (mul_nonneg hA₁ (Real.rpow_nonneg (Nat.cast_nonneg _) _))).trans_eq
      ring
  calc
    _ ≤ ∑D∈Ds,‖μ D‖*((A₁*A₂)*min (s₁.saving α) (s₂.saving α)*
        ((D.absNorm:ℝ)^(δ-(1-α))*(D.absNorm:ℝ)^(δ-1))) := by
      apply Finset.sum_le_sum
      intro D hD
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hp D hD) (norm_nonneg (μ D))
    _ = ((A₁*A₂)*min (s₁.saving α) (s₂.saving α))*
        (∑D∈Ds,‖μ D‖*((D.absNorm:ℝ)^(δ-(1-α))*(D.absNorm:ℝ)^(δ-1))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro D hD
      ring
    _ ≤ ((A₁*A₂)*min (s₁.saving α) (s₂.saving α))*K :=
      mul_le_mul_of_nonneg_left (hmass Ds μ (fun D hD=>(hDs D hD).ne_zero) hμ)
        (mul_nonneg (mul_nonneg hA₁ hA₂) hsave)
    _ = _ := by dsimp [A₁,A₂];ring

/-- The same actual pair, summed over an arbitrary finite set of nonzero
physical rows. The right source is evaluated at -z, as in the second
Poisson kernel. The only remaining row count is the literal cardinality. -/
theorem uniform_frozen_masked_pair_rows (N : ℕ) (α Bcap a b ε δ : ℝ)
    (hα : 0≤α) (hα4 : α<4/5) (hBcap : 0≤Bcap)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hδ : 0<δ) (hgap : α+2*δ<1) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),(0,0)∈control ∧
      ∀Q : Id,Q≠0→∃C : ℝ,0<C ∧
      ∀(ι₁ ι₂ : Type u) [Fintype ι₁] [Fintype ι₂],
      ∀(s₁ : Source ι₁ a b)(s₂ : Source ι₂ a b),
      ∀Z : ℝ,1≤Z→s₁.Admissible N Bcap Z→s₂.Admissible N Bcap Z→
      ∀(η₁ η₂ : Character)(rows : Finset O)(Ds : Finset Id)(μ : Id→ℂ),
      (∀z∈rows,z≠0)→(∀D∈Ds,Squarefree D)→(∀D∈Ds,‖μ D‖≤1)→
      (∀z∈rows,∀D∈Ds,(HeckeRowClosure.rowConductorBound η₁
        (fixedBadMask*idealGenerator ((s₁.R*s₁.G)*D)) 1 z:ℝ)≤Z^Bcap)→
      (∀z∈rows,∀D∈Ds,(HeckeRowClosure.rowConductorBound η₂
        (fixedBadMask*idealGenerator ((s₂.R*s₂.G)*D)) 1 (-z):ℝ)≤Z^Bcap)→
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow η₁ Q fixedBadMask 1 z)→
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow η₂ Q fixedBadMask 1 (-z))→
      (∑D∈Ds,‖μ D‖*∑z∈rows,‖s₁.row ha (naturalCharacter η₁ z) D‖*
        ‖s₂.row ha (naturalCharacter η₂ (-z)) D‖)≤
      (rows.card:ℝ)*(C*(s₁.budget J control Z ε*s₂.budget J control Z ε)*
        min (s₁.saving α) (s₂.saving α)) := by
  obtain ⟨J,control,h00,hpair⟩ := uniform_frozen_masked_pair N α Bcap a b ε δ
    hα hα4 hBcap ha hb hε hδ hgap
  refine ⟨J,control,h00,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hpair⟩ := hpair Q hQ
  refine ⟨C,hC,?_⟩
  intro ι₁ ι₂ inst₁ inst₂ s₁ s₂ Z hZ hs₁ hs₂ η₁ η₂ rows Ds μ hrows hDs hμ hc₁ hc₂ he₁ he₂
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑z∈rows,C*(s₁.budget J control Z ε*s₂.budget J control Z ε)*
        min (s₁.saving α) (s₂.saving α) := by
      apply Finset.sum_le_sum
      intro z hz
      simpa only [mul_assoc] using hpair ι₁ ι₂ s₁ s₂ Z hZ hs₁ hs₂ η₁ η₂ z (-z) Ds μ
        (hrows z hz) (neg_ne_zero.mpr (hrows z hz)) hDs hμ
        (hc₁ z hz) (hc₂ z hz) (he₁ z hz) (he₂ z hz)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end
end Candidate.FourthPower.MixedPrincipalPair
