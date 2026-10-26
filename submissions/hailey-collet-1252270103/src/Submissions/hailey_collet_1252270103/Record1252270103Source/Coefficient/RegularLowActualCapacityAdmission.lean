/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal final-live LOW admission after three allocations and Newton division.
The geometric guard implies cap nonnegativity; no source energy is assumed. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.RegularLowActualCapacityErasure
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.RegularLowActualCapacity
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open CenteredMomentEnergyBands QRH.Record1252270103Low QRH.Record12518109Source
open QRH.Record1252270103Restoration
local notation "O" => HeckeFamily.O
local instance regularLowAdmissionDecidable {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable (s : Input ι) (C₁ R : Ideal O) (B₁ : actualAllocations s.pools C₁)
    (τ₁ : Character) (t₁ : ℝ) (C₂ : Ideal O)
    (B₂ : actualAllocations (child s C₁ R B₁ τ₁ t₁).pools C₂)
    (τ₂ : Character) (t₂ : ℝ) (C₃ : Ideal O)
    (B₃ : actualAllocations (child (child s C₁ R B₁ τ₁ t₁)
      C₂ (R*C₁) B₂ τ₂ t₂).pools C₃) (τ₃ : Character) (t₃ : ℝ)

/-- One erasure is selected before the positive corner, its row, profiles and
rounded widths. The actual row is either zero or admitted to the original
downward global face. All three common norms and the Newton improvement remain
in the cap and in the zero/affine/upper-cap erasure cost. -/
theorem three_live_rounded_admission (w : ι → ℝ)
    (S : Finset (liveIndices B₃.val)) (N : ℕ)
    (upper Z t b F delta rho B lam h plainUpper mesh plainRound d₁ d₂ : ℝ)
    (hupper : 1 ≤ upper) (hZ : 1 < Z) (hN : Fintype.card ι ≤ N) (hu : s.upper ≤ upper)
    (hscale : ∀ i, s.P i = Z ^ w i) (ht : length Z s.X₁ + length Z s.X₂ ≤ t)
    (hw : ∀ i, 0 ≤ w i) (htotal : (∑ i, w i) ≤ b)
    (hmesh : 0 ≤ mesh) (hwm : ∀ i ∈ S, w i.val.val.val ≤ mesh)
    (hround : 0 ≤ plainRound) (hB : B ≤ 1) (hlam : 0 < lam)
    (hd : 0 ≤ delta) (hdc : delta ≤ Real.logb Z (C₁.absNorm:ℝ))
    (hh : 0 ≤ h) (hQ : 0 ≤ F-delta-rho) (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂)
    (hguard : (3*(N:ℝ)*Real.logb Z upper+2*Real.logb Z (max 1 plainUpper)+2*plainRound)+
      B*rho ≤ B*F-t-b)
    (hf₁ : frozenCoefficient B₁.val C₁ R s.ν s.W s.P ≠ 0)
    (hf₂ : frozenCoefficient B₂.val C₂ (R*C₁)
      (child s C₁ R B₁ τ₁ t₁).ν (child s C₁ R B₁ τ₁ t₁).W
      (child s C₁ R B₁ τ₁ t₁).P ≠ 0)
    (hf₃ : frozenCoefficient B₃.val C₃ ((R*C₁)*C₂)
      (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).ν
      (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).W
      (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).P ≠ 0) :
    let c := Real.logb Z (C₁.absNorm:ℝ)+Real.logb Z (C₂.absNorm:ℝ)+Real.logb Z (C₃.absNorm:ℝ)
    let f := (∑ i, w i) - ∑ i : liveIndices B₃.val, w i.val.val.val
    let loss := 3*(N:ℝ)*Real.logb Z upper+2*Real.logb Z (max 1 plainUpper)+2*plainRound
    let Pcap := t-c+f+loss-Real.logb Z d₁-Real.logb Z d₂
    let Q := F-delta-rho
    let cap := min ((B*Q-Pcap)/lam) (h*Q)
    0 ≤ cap ∧ ∃ E : Finset (liveIndices B₃.val), E ⊆ S ∧
      (∑ i ∈ S\E, w i.val.val.val) ≤ cap ∧
      (∑ i ∈ E, w i.val.val.val) ≤
        max 0 (max (b-f-(B*Q-Pcap)/lam) (b-f-h*Q))+mesh ∧
      ∀ X₁ X₂ : ℝ, 0 < X₁ → 0 < X₂ →
      X₁*X₂ = (child (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂)
        C₃ ((R*C₁)*C₂) B₃ τ₃ t₃).X₁ *
        (child (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂)
        C₃ ((R*C₁)*C₂) B₃ τ₃ t₃).X₂ →
      ∀ (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
        (pool : κ → Finset (Ideal O)) (β : κ → Ideal O → ℂ) (scales : κ → ℝ) (height : ℝ)
        (n₁ n₂ : ℝ), 0 ≤ n₁ → 0 ≤ n₂ →
      n₁ ≤ length Z (X₁/d₁)+plainRound → n₂ ≤ length Z (X₂/d₂)+plainRound →
      squarefreePositiveSlotRow η m A z W₁ W₂ plainUpper pool β scales height (X₁/d₁) (X₂/d₂) = 0 ∨
        (SourceFace.mk B lam 0 B 0 h).Admissible n₁ n₂ (∑ i ∈ S\E, w i.val.val.val) Q := by
  intro c f loss Pcap Q cap
  have hcap : 0 ≤ cap := three_live_cap_nonneg s C₁ R B₁ τ₁ t₁ C₂ B₂ τ₂ t₂ C₃ B₃
    w Z b F t delta rho B lam h loss d₁ d₂ hZ hw htotal hB hlam hd hdc hh hQ hd₁ hd₂ hguard
  obtain ⟨E,hE,hleft,hcost⟩ := three_live_erasure s C₁ R B₁ τ₁ t₁ C₂ B₂ τ₂ t₂ C₃ B₃
    w S b cap mesh hw htotal hmesh hwm hcap
  have hleft' : (∑ i ∈ S\E, w i.val.val.val) ≤ cap := by
    convert hleft using 1
  refine ⟨hcap,E,hE,hleft',?_,?_⟩
  · simpa only [cap,raw_erasure_cost] using hcost
  · intro X₁ X₂ hX₁ hX₂ hprod η m A z W₁ W₂ pool β scales height n₁ n₂ hn₁ hn₂ hn₁cap hn₂cap
    have hcorner := three_positive_corner_capacity_or_zero
      s C₁ R B₁ τ₁ t₁ C₂ B₂ τ₂ t₂ C₃ B₃ τ₃ t₃ w N upper Z t
      hupper hZ hN hu hscale ht hf₁ hf₂ hf₃ X₁ X₂ d₁ d₂ plainUpper hX₁ hX₂
      (zero_lt_one.trans_le hd₁) (zero_lt_one.trans_le hd₂) hprod η m A z W₁ W₂ pool β scales height
    rcases hcorner with hz|hc
    · exact Or.inl hz
    · apply Or.inr
      have hpair : (length Z (X₁/d₁)+plainRound)+(length Z (X₂/d₂)+plainRound) ≤ Pcap := by
        dsimp only [Pcap,c,f,loss]
        linarith only [hc]
      exact global_first_cap B lam h Pcap Q
        (length Z (X₁/d₁)+plainRound) (length Z (X₂/d₂)+plainRound) n₁ n₂
        (∑ i ∈ S\E, w i.val.val.val) hlam hpair hn₁ hn₂
        (Finset.sum_nonneg (fun i _ => hw i.val.val.val)) hn₁cap hn₂cap hleft'

end
end QRH.Record1252270103Source.RegularLowActualCapacity
#print axioms QRH.Record1252270103Source.RegularLowActualCapacity.three_live_rounded_admission
