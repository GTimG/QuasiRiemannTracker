/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual three-allocation large-width ledger, including the precise lower-support loss.
No count, energy bound, or substituted active source is a premise. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedHighSlotsImage
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.HighScalar.AllocationWidth
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedHighSlots
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open Record12518109Natural CommonSupply MarkedPlain
local notation "O" => HeckeFamily.O
variable {ι : Type} [Fintype ι]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable (s : Input ι) (C₁ R : Ideal O) (B₁ : actualAllocations s.pools C₁)
    (τ₁ : Character) (t₁ : ℝ) (C₂ : Ideal O)
    (B₂ : actualAllocations (child s C₁ R B₁ τ₁ t₁).pools C₂)
    (τ₂ : Character) (t₂ : ℝ) (C₃ : Ideal O)
    (B₃ : actualAllocations (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).pools C₃)
    (hf₁ : frozenCoefficient B₁.val C₁ R s.ν s.W s.P≠0)
    (hf₂ : frozenCoefficient B₂.val C₂ (R*C₁)
      (child s C₁ R B₁ τ₁ t₁).ν (child s C₁ R B₁ τ₁ t₁).W (child s C₁ R B₁ τ₁ t₁).P≠0)
    (hf₃ : frozenCoefficient B₃.val C₃ ((R*C₁)*C₂)
      (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).ν
      (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).W
      (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).P≠0)

include hf₁ hf₂ hf₃

/-- Both earlier common factors and the actual forced common factor enter
through their ideal norms; the tiny-width loss uses the original cardinal cap. -/
theorem actual_large_width_ledger (N : ℕ) (lo Z wmin : ℝ) (hN : Fintype.card ι≤N)
    (hlo : 0<lo) (hs : lo≤s.lower) (hZ : 1<Z) (hmin : 0≤wmin)
    (w : ι→ℝ) (hscale : ∀i,s.P i=Z^(w i)) :
    (∑i,w i)-Real.logb Z (C₁.absNorm:ℝ)-Real.logb Z (C₂.absNorm:ℝ)-
      Real.logb Z (C₃.absNorm:ℝ)+3*(N:ℝ)*Real.logb Z (min 1 lo)-(N:ℝ)*wmin≤
      ∑i∈largeSlots (finalImage B₁.val B₂.val B₃.val) w wmin,w i := by
  have hh:=HighScalar.actual_three_stage_live_width N lo hlo s hN hs C₁ R B₁ hf₁ τ₁ t₁
    C₂ (R*C₁) B₂ hf₂ τ₂ t₂ C₃ ((R*C₁)*C₂) B₃ hf₃ Z hZ
  simp_rw [hscale,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh
  have hsum:=sum_originalSlots (finalEmbedding B₁.val B₂.val B₃.val)
    (finalEmbedding B₁.val B₂.val B₃.val).injective w
  change (∑i : liveIndices B₃.val,w i.val.val.val)=∑i∈finalImage B₁.val B₂.val B₃.val,w i at hsum
  rw [hsum] at hh
  have hl:=large_width_lower (finalImage B₁.val B₂.val B₃.val) w wmin N
    ((Finset.card_le_univ _).trans hN) hmin
  linarith only [hh,hl]

/-- One actual ledger works for every collision subset of the full final
original image. The support loss is from the lower endpoint, with its sign retained. -/
theorem actual_selected_slot_ledger (N : ℕ) (lo Z wmin b δ allowance : ℝ)
    (hN : Fintype.card ι≤N) (hlo : 0<lo) (hs : lo≤s.lower) (hZ : 1<Z)
    (hmin : 0≤wmin) (w : ι→ℝ) (hscale : ∀i,s.P i=Z^(w i)) (hw : ∀i,0≤w i)
    (htotal : b-δ≤∑i,w i) (hupper : (∑i,w i)≤b)
    (hloss : δ-3*(N:ℝ)*Real.logb Z (min 1 lo)+(N:ℝ)*wmin≤2*allowance) :
    let full:=finalImage B₁.val B₂.val B₃.val
    let live:=∑i∈largeSlots full w wmin,w i
    0≤live ∧ live≤b ∧ b-2*allowance≤live+Real.logb Z (C₁.absNorm:ℝ)+
      Real.logb Z (C₂.absNorm:ℝ)+Real.logb Z (C₃.absNorm:ℝ) ∧
    ∀T : Finset ι,T⊆full →
      let small:=∑i∈largeSlots T w wmin,w i
      0≤small ∧ small≤live ∧ (∑i∈T,w i)+(live-small)≤∑i∈full,w i := by
  intro full live
  have hh:=actual_large_width_ledger s C₁ R B₁ τ₁ t₁ C₂ B₂ τ₂ t₂ C₃ B₃
    hf₁ hf₂ hf₃ N lo Z wmin hN hlo hs hZ hmin w hscale
  refine ⟨Finset.sum_nonneg (fun i _=>hw i),
    (Finset.sum_le_univ_sum_of_nonneg hw).trans hupper,?_,?_⟩
  · dsimp only [live,full]
    linarith only [hh,htotal,hloss]
  · intro T hT small
    obtain ⟨h₀,h₁,_⟩:=subset_large_widths full T w wmin b hT hw hupper
    exact ⟨h₀,h₁,subset_width_conservation full T w wmin hT hw⟩

/-- Canonical lower support at one removes the annular width loss exactly.
All three actual nonzero frozen coefficients remain premises. -/
theorem canonical_selected_slot_ledger (N : ℕ) (Z wmin b δ allowance : ℝ)
    (hN : Fintype.card ι≤N) (hs : 1≤s.lower) (hZ : 1<Z)
    (hmin : 0≤wmin) (w : ι→ℝ) (hscale : ∀i,s.P i=Z^(w i)) (hw : ∀i,0≤w i)
    (htotal : b-δ≤∑i,w i) (hupper : (∑i,w i)≤b)
    (hloss : δ+(N:ℝ)*wmin≤2*allowance) :
    let full:=finalImage B₁.val B₂.val B₃.val
    let live:=∑i∈largeSlots full w wmin,w i
    0≤live ∧ live≤b ∧ b-2*allowance≤live+Real.logb Z (C₁.absNorm:ℝ)+
      Real.logb Z (C₂.absNorm:ℝ)+Real.logb Z (C₃.absNorm:ℝ) ∧
    ∀T : Finset ι,T⊆full →
      let small:=∑i∈largeSlots T w wmin,w i
      0≤small ∧ small≤live ∧ (∑i∈T,w i)+(live-small)≤∑i∈full,w i := by
  apply actual_selected_slot_ledger s C₁ R B₁ τ₁ t₁ C₂ B₂ τ₂ t₂ C₃ B₃ hf₁ hf₂ hf₃
    N 1 Z wmin b δ allowance hN zero_lt_one hs hZ hmin w hscale hw htotal hupper
  simpa using hloss

end
end QRH.Record1252270103Source.Admission.SelectedHighSlots
#print axioms QRH.Record1252270103Source.Admission.SelectedHighSlots.actual_large_width_ledger
#print axioms QRH.Record1252270103Source.Admission.SelectedHighSlots.actual_selected_slot_ledger
#print axioms QRH.Record1252270103Source.Admission.SelectedHighSlots.canonical_selected_slot_ledger
