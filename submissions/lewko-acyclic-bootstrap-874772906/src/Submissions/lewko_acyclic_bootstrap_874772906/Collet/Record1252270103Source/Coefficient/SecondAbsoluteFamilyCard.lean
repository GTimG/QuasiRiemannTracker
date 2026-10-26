/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
One polynomial envelope for the literal complete retained family and every
ratio restriction. Its constant precedes all moving families and slot types. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.SecondAbsoluteLabelCard
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.SecondAbsoluteEnvelope
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentSourceMass CenteredMomentOriginalCommonHarmonic
open CenteredMomentSectorLocalization Record1252270103Second Cycle61InitialMass
open QRH.Record1252270103Source.SecondSectorDatum
open QRH.Record1252270103Source.Admission.ModifiedFibers
local notation "O" => HeckeFamily.O
local instance absoluteFamilySumDecidable {ι:Type*} :
    DecidableEq (ι⊕Fin 2) := Classical.decEq _

theorem eventually_complete_family_card (A D₀ B L Cr:ℝ)
    (hA:0≤A) (hD₀:0≤D₀) (hB:0≤B) (hL:0≤L) (hCr:0<Cr) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1≤Z ∧
    ∀{α Label:Type*} [Fintype α] [DecidableEq α] [Fintype Label]
      (slots:Label→Finset α) (s:∀l,Input (slots l))
      (modifier:∀l,Tuple (slots l)→ℂ) (R seed:Label→Ideal O)
      (W:𝓢(ℝ,ℂ)) (H Tsec:Label→ℝ) (ξ Cl Bl:ℝ),
      (∀l,Squarefree (seed l)) → (∀l,(s l).W₁ 0=0) → (∀l,(s l).W₂ 0=0) →
      (∀l,0<H l) → (∀l,Z^(-D₀)≤H l) → (∀l,H l≤Z^A) →
      (∀l,frequencyRadius (Tsec l) Z ξ≤Cr*Z^L) →
      (∀l,sourceRadius (s l)≤Z^B) → 0≤Cl →
      (Fintype.card Label:ℝ)≤Cl*Z^Bl →
      (Fintype.card (CompleteFamily slots s modifier R seed W H Tsec
        (fun _=>Z) (fun _=>ξ)):ℝ)≤C*Cl*Z^(Bl+3*B+1) ∧
      ∀keep:CompleteFamily slots s modifier R seed W H Tsec (fun _=>Z) (fun _=>ξ)→Prop,
        (Fintype.card {q // keep q}:ℝ)≤C*Cl*Z^(Bl+3*B+1) := by
  obtain ⟨Cs,hCs,hsub⟩:=common_subset_card_bound
  obtain ⟨Cd,hCd,hdyads⟩:=second_absolute_envelope_subpower A D₀ B L Cr 1
    hA hD₀ hB hL hCr (by norm_num)
  let C:ℝ:=128^2*Cs*Cd
  refine ⟨C,by dsimp [C];positivity,?_⟩
  filter_upwards [hdyads,eventually_ge_atTop (1:ℝ)] with Z hd hZ
  refine ⟨hZ,?_⟩
  intro α Label instα instDec instLabel slots s modifier R seed W H Tsec ξ Cl Bl
    hseed hz₁ hz₂ hH hHlo hHhi hR hsource hCl hlabel
  have hz:0<Z:=zero_lt_one.trans_le hZ
  let box:=secondAbsoluteBox Z A D₀ B L Cr
  have hboxcard:(box.card:ℝ)≤Cd*Z := by
    rw [show box.card=Fintype.card (SecondAbsoluteEnvelope Z A D₀ B L Cr) from
      second_absolute_box_card Z A D₀ B L Cr]
    simpa only [Real.rpow_one] using hd
  have hpower:Z^B*Z^B*Z^B*Z=Z^(3*B+1) := by
    nth_rw 4 [←Real.rpow_one Z]
    rw [←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz]
    congr 1
    ring
  have hblock (l:Label) :
      (Fintype.card (CompleteBlock (s l) (modifier l) (R l) (seed l) W
        (H l) (Tsec l) Z ξ):ℝ)≤C*Z^(3*B+1) := by
    have hc:(Fintype.card (CompleteBlock (s l) (modifier l) (R l) (seed l) W
        (H l) (Tsec l) Z ξ):ℝ)≤
        (Fintype.card (BlockIndex (s l) (modifier l) (R l) (seed l) (H l) (Tsec l) Z ξ):ℝ) := by
      exact_mod_cast Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    apply hc.trans
    apply (block_card_in_box (s l) (modifier l) (R l) (seed l) (hseed l) (hz₁ l) (hz₂ l)
      (H l) (Tsec l) Z ξ (Z^B) Cs (Real.rpow_nonneg hz.le _) hCs.le (hsource l) hsub box
      (modified_dyad_absolute Z A D₀ B L Cr hZ hA hD₀ hB hL hCr
        (s l) (modifier l) (R l) (seed l) (hseed l) (hz₁ l) (hz₂ l)
        (H l) (Tsec l) ξ (hH l) (hHlo l) (hHhi l) (hR l) (hsource l))).trans
    calc
      _≤(128*Z^B)^2*(Cs*Z^B)*(Cd*Z) :=
        mul_le_mul_of_nonneg_left hboxcard (by positivity)
      _=C*(Z^B*Z^B*Z^B*Z) := by dsimp [C];ring
      _=C*Z^(3*B+1) := by rw [hpower]
  have hfamily:(Fintype.card (CompleteFamily slots s modifier R seed W H Tsec
      (fun _=>Z) (fun _=>ξ)):ℝ)≤C*Cl*Z^(Bl+3*B+1) := by
    change (Fintype.card (Σl:Label,CompleteBlock (s l) (modifier l) (R l) (seed l) W
      (H l) (Tsec l) Z ξ):ℝ)≤_
    simp only [Fintype.card_sigma,Nat.cast_sum]
    calc
      _≤∑_l:Label,C*Z^(3*B+1) := Finset.sum_le_sum (fun l _=>hblock l)
      _=(Fintype.card Label:ℝ)*(C*Z^(3*B+1)) := by simp
      _≤(Cl*Z^Bl)*(C*Z^(3*B+1)) :=
        mul_le_mul_of_nonneg_right hlabel (by dsimp [C];positivity)
      _=C*Cl*(Z^Bl*Z^(3*B+1)) := by ring
      _=C*Cl*Z^(Bl+3*B+1) := by rw [←Real.rpow_add hz];congr 2;ring
  refine ⟨hfamily,?_⟩
  intro keep
  apply le_trans _ hfamily
  exact_mod_cast Fintype.card_le_of_injective Subtype.val Subtype.val_injective

end
end QRH.Record1252270103Source.SecondAbsoluteEnvelope
#print axioms QRH.Record1252270103Source.SecondAbsoluteEnvelope.eventually_complete_family_card
