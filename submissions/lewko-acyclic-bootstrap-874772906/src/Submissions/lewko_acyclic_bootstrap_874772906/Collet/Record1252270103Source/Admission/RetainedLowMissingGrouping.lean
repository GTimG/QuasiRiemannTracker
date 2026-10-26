/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite collection extends the missing-ideal argument in Record12518109Raw.MissingSum. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.RetainedLowMissingRadical
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.RetainedLow
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment CompletedGauss
open Record12518109Raw RayFourExpansion
local notation "O" => HeckeFamily.O
variable {left : Bool} {u₀ : O} {unit : FirstSourceLabel→O}
local notation "Key" => NonzeroJointSourceLabel left u₀ unit

def missingRayFiber (labels : Finset Key) (ray₁ ray₂ : Key→RayCharacter)
    (H : Ideal O) (r ψ : RayCharacter) : Finset Key :=
  labels.filter (fun l=>(firstSourceMissing left l.val.1,(ray₁ l,ray₂ l))=(H,(r,ψ)))

theorem mem_missingRayFiber (labels : Finset Key) (ray₁ ray₂ : Key→RayCharacter)
    (H : Ideal O) (r ψ : RayCharacter) (l : Key) :
    l∈missingRayFiber labels ray₁ ray₂ H r ψ ↔
      l∈labels ∧ firstSourceMissing left l.val.1=H ∧ ray₁ l=r ∧ ray₂ l=ψ := by
  simp [missingRayFiber]

theorem missing_ray_partition (labels : Finset Key) (ray₁ ray₂ : Key→RayCharacter)
    (cost : Key→ℝ) :
    (∑l∈labels,cost l)=
      ∑H∈labels.image (fun l=>firstSourceMissing left l.val.1),
        ∑r : RayCharacter,∑ψ : RayCharacter,
          ∑l∈missingRayFiber labels ray₁ ray₂ H r ψ,cost l := by
  let tag:=fun l : Key=>(firstSourceMissing left l.val.1,(ray₁ l,ray₂ l))
  let tags:=(labels.image (fun l=>firstSourceMissing left l.val.1)).product
    ((Finset.univ : Finset RayCharacter).product (Finset.univ : Finset RayCharacter))
  have ht (l : Key) (hl : l∈labels) : tag l∈tags := by
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hl,
      Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_univ _⟩⟩
  have he:=(Finset.sum_fiberwise_of_maps_to ht cost).symm
  calc
    _ = ∑x∈(labels.image (fun l=>firstSourceMissing left l.val.1)).product
        ((Finset.univ : Finset RayCharacter).product (Finset.univ : Finset RayCharacter)),
        ∑l∈labels.filter (fun l=>tag l=x),cost l := he
    _ = ∑H∈labels.image (fun l=>firstSourceMissing left l.val.1),
        ∑p∈(Finset.univ : Finset RayCharacter).product (Finset.univ : Finset RayCharacter),
          ∑l∈labels.filter (fun l=>tag l=(H,p)),cost l :=
      Finset.sum_product _ _ _
    _ = _ := Finset.sum_congr rfl (fun H _=>Finset.sum_product _ _ _)

theorem missing_nonzero (labels : Finset Key)
    (hsupported : ∀l∈labels,Supported l.val.1.1.1) (l : Key) (hl : l∈labels) :
    firstSourceMissing left l.val.1≠0 := by
  have hd:=first_missing_dvd left l.val.1 (hsupported l hl).1
  intro hz
  rw [hz] at hd
  exact (hsupported l hl).1 (zero_dvd_iff.mp hd)

theorem missing_ray_weighted_sum
    (labels : Finset Key) (ray₁ ray₂ : Key→RayCharacter)
    (cost : Key→ℝ) (R : Ideal O) (hR : R≠0)
    (Z lo hi ε γ E : ℝ) (hZ : 0<Z) (hε : 0≤ε) (hγ : 0≤γ) (hE : 0≤E)
    (hsupported : ∀l∈labels,Supported l.val.1.1.1)
    (hlo : ∀l∈labels,Z^lo≤((firstSourceMissing left l.val.1).absNorm:ℝ))
    (hhi : ∀l∈labels,((firstSourceMissing left l.val.1).absNorm:ℝ)≤Z^hi)
    (hfiber : ∀H∈labels.image (fun l=>firstSourceMissing left l.val.1),
      ∀r ψ : RayCharacter,
      (∑l∈missingRayFiber labels ray₁ ray₂ H r ψ,cost l)≤
        E*((∏I∈primeSupport (R*H),I).absNorm:ℝ)^ε) :
    (∑l∈labels,cost l*((firstSourceMissing left l.val.1).absNorm:ℝ)^(-γ))≤
      128*(Fintype.card RayCharacter:ℝ)^2*E*((∏I∈primeSupport R,I).absNorm:ℝ)^ε*
        Z^(hi*(1+ε)-γ*lo) := by
  let missing:=fun l : Key=>firstSourceMissing left l.val.1
  let Hs:=labels.image missing
  let V:=E*((∏I∈primeSupport R,I).absNorm:ℝ)^ε*Z^(hi*ε-γ*lo)
  have hV : 0≤V := by dsimp [V];positivity
  have hcard : (Hs.card:ℝ)≤128*Z^hi:=Cycle61.Physical.missing_radical_card
    Hs Z hi hZ.le
    (by intro H hH;obtain ⟨l,hl,rfl⟩:=Finset.mem_image.mp hH
        exact missing_nonzero labels hsupported l hl)
    (by intro H hH;obtain ⟨l,hl,rfl⟩:=Finset.mem_image.mp hH;exact hhi l hl)
  have hf (H : Ideal O) (hH : H∈Hs) (r ψ : RayCharacter) :
      (∑l∈missingRayFiber labels ray₁ ray₂ H r ψ,cost l*(missing l).absNorm^(-γ))≤V := by
    obtain ⟨l₀,hl₀,he₀⟩:=Finset.mem_image.mp hH
    have hH0 : H≠0:=he₀ ▸ missing_nonzero labels hsupported l₀ hl₀
    have hpow : 0≤(H.absNorm:ℝ)^(-γ):=Real.rpow_nonneg (Nat.cast_nonneg _) _
    calc
      _ = (∑l∈missingRayFiber labels ray₁ ray₂ H r ψ,cost l)*(H.absNorm:ℝ)^(-γ) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro l hl
        have hh:=(mem_missingRayFiber labels ray₁ ray₂ H r ψ l).mp hl
        change cost l*((firstSourceMissing left l.val.1).absNorm:ℝ)^(-γ)=_
        rw [hh.2.1]
      _ ≤ (E*((∏I∈primeSupport (R*H),I).absNorm:ℝ)^ε)*(H.absNorm:ℝ)^(-γ) :=
        mul_le_mul_of_nonneg_right (hfiber H (Finset.mem_image.mpr ⟨l₀,hl₀,he₀⟩) r ψ) hpow
      _ ≤ V := by
        dsimp only [V]
        rw [mul_assoc E, mul_assoc E]
        apply mul_le_mul_of_nonneg_left _ hE
        apply weighted_missing_radical_bound R H hR hH0 Z lo hi ε γ hZ hε hγ
        · exact he₀ ▸ hlo l₀ hl₀
        · exact he₀ ▸ hhi l₀ hl₀
  rw [missing_ray_partition labels ray₁ ray₂]
  calc
    _ ≤ ∑_H∈Hs,∑_r : RayCharacter,∑_ψ : RayCharacter,V := by
      apply Finset.sum_le_sum
      intro H hH
      exact Finset.sum_le_sum (fun r _=>Finset.sum_le_sum (fun ψ _=>hf H hH r ψ))
    _ = (Hs.card:ℝ)*((Fintype.card RayCharacter:ℝ)^2*V) := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring
    _ ≤ (128*Z^hi)*((Fintype.card RayCharacter:ℝ)^2*V) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg (sq_nonneg _) hV)
    _ = _ := by
      dsimp only [V]
      have he : Z^hi*Z^(hi*ε-γ*lo)=Z^(hi*(1+ε)-γ*lo) := by
        rw [←Real.rpow_add hZ]
        congr 1
        ring
      calc
        _ = 128*(Fintype.card RayCharacter:ℝ)^2*E*((∏I∈primeSupport R,I).absNorm:ℝ)^ε*
          (Z^hi*Z^(hi*ε-γ*lo)) := by ring
        _ = _ := by rw [he]
end
end QRH.Record1252270103Source.Admission.RetainedLow
#print axioms QRH.Record1252270103Source.Admission.RetainedLow.missing_ray_partition
#print axioms QRH.Record1252270103Source.Admission.RetainedLow.missing_ray_weighted_sum
