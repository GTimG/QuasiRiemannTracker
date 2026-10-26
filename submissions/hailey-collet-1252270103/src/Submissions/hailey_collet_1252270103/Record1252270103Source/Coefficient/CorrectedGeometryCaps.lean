/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual ideal norm caps discharge every finite Newton-count inlet. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CorrectedGeometry
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.NewtonNormGeometry
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open QRH.Record1252270103Low QRH.Record1252270103Source.High.CorrectedCentered
open QRH.Record1252270103Source.ForcedCost
local notation "O"=>ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

theorem corrected_source_geometry_of_caps (s : Input ι) (W₁ W₂ : 𝓢(ℝ,ℂ))
    (b Z BA Bpool Bplain BD ell : ℝ) (depth : ℕ) (A₁ A₂ Df K R : Ideal O)
    (P : Finset (Ideal O))
    (hW₁ : s.W₁=(W₁:ℝ→ℂ)) (hW₂ : s.W₂=(W₂:ℝ→ℂ)) (hb₁ : s.b₁≤b) (hb₂ : s.b₂≤b)
    (hb : 0≤b) (hZ : 1<Z) (hell : 0<ell) (hR : R≠0) (hA₁ : A₁≠0) (hA₂ : A₂≠0)
    (hDR : Df∣R) (hA : ((A₁*A₂).absNorm:ℝ)≤Z^BA) (hD : (Df.absNorm:ℝ)≤Z^BD)
    (hP : 0<P.card) (hp : ∀p∈P,Prime p) (h16 : ∀p∈P,16≤p.absNorm)
    (hfloor : ∀p∈P,Z^ell≤(p.absNorm:ℝ)) (hupper : ∀p∈P,(p.absNorm:ℝ)≤Z^Bpool)
    (havoid : ∀p∈P,∀i I,I∈s.slots i→¬p∣I)
    (hsize : 2*(BD/ell+depth+1)≤P.card) (hdepth : Bplain/ell≤depth)
    (hplain : b^2*(s.X₁*s.X₂)≤Z^Bplain) :
    CorrectedSourceGeometry s W₁ W₂ b Z BA Bpool depth A₁ A₂ Df K R P := by
  have hDf : Df≠0 := fun h=>hR (by simpa only [h,zero_dvd_iff] using hDR)
  refine ⟨hW₁,hW₂,hb₁,hb₂,hR,hA₁,hA₂,hDR,hA,hP,hp,h16,hupper,havoid,
    actual_newton_budget P Df hDf depth hp Z ell BD hZ hell hfloor hD hsize,?_⟩
  intro n hn hsf hne
  apply frozen_profile_newton_count P depth hp Z ell Bplain hZ hell hfloor hdepth
    W₁ W₂ A₁ A₂ b s.X₁ s.X₂ s.Y₁ s.Y₂ hb s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos
    s.same_product hplain _ _ n hn hne
  · rw [←hW₁]
    exact fun x hx=>(s.support₁ hx).trans hb₁
  · rw [←hW₂]
    exact fun x hx=>(s.support₂ hx).trans hb₂

/-- Allocation keeps every live original marked pool and shortens the actual
ordinary factors. Only the updated frozen/correction norm caps are supplied. -/
theorem corrected_child_geometry_of_caps (s : Input ι) (C R : Ideal O) (hC : C≠0)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (b Z BA Bpool Bplain BD ell : ℝ) (depth : ℕ)
    (A₁ A₂ Df K : Ideal O) (P : Finset (Ideal O))
    (hW₁ : s.W₁=(W₁:ℝ→ℂ)) (hW₂ : s.W₂=(W₂:ℝ→ℂ)) (hb₁ : s.b₁≤b) (hb₂ : s.b₂≤b)
    (hb : 0≤b) (hZ : 1<Z) (hell : 0<ell) (hR : R≠0) (hA₁ : A₁≠0) (hA₂ : A₂≠0)
    (hDR : Df∣R)
    (hA : (((A₁*B.val (Sum.inr 0))*(A₂*B.val (Sum.inr 1))).absNorm:ℝ)≤Z^BA)
    (hD : ((Df*C).absNorm:ℝ)≤Z^BD)
    (hP : 0<P.card) (hp : ∀p∈P,Prime p) (h16 : ∀p∈P,16≤p.absNorm)
    (hfloor : ∀p∈P,Z^ell≤(p.absNorm:ℝ)) (hupper : ∀p∈P,(p.absNorm:ℝ)≤Z^Bpool)
    (havoid : ∀p∈P,∀i I,I∈s.slots i→¬p∣I)
    (hsize : 2*(BD/ell+depth+1)≤P.card) (hdepth : Bplain/ell≤depth)
    (hplain : b^2*(s.X₁*s.X₂)≤Z^Bplain) :
    CorrectedSourceGeometry (child s C R B τ t) W₁ W₂ b Z BA Bpool depth
      (A₁*B.val (Sum.inr 0)) (A₂*B.val (Sum.inr 1)) (Df*C)
      (K*Collision.markedProduct B.val) (R*C) P := by
  have hX₁ : (child s C R B τ t).X₁≤s.X₁ :=
    div_le_self s.X₁_pos.le (alloc_norm_ge_one s C B (Sum.inr 0))
  have hX₂ : (child s C R B τ t).X₂≤s.X₂ :=
    div_le_self s.X₂_pos.le (alloc_norm_ge_one s C B (Sum.inr 1))
  apply corrected_source_geometry_of_caps (child s C R B τ t) W₁ W₂
    b Z BA Bpool Bplain BD ell depth _ _ _ _ _ P hW₁ hW₂ hb₁ hb₂ hb hZ hell
    (mul_ne_zero hR hC) (mul_ne_zero hA₁ (alloc_ne s C B _))
    (mul_ne_zero hA₂ (alloc_ne s C B _)) (mul_dvd_mul hDR (dvd_refl C)) hA hD
    hP hp h16 hfloor hupper (fun p hp i I hI=>havoid p hp i.val I hI) hsize hdepth
  exact (mul_le_mul_of_nonneg_left
    (mul_le_mul hX₁ hX₂ (child s C R B τ t).X₂_pos.le s.X₁_pos.le) (sq_nonneg b)).trans hplain
end
end OAI.SevenEighths.Record1252270103Source
#print axioms OAI.SevenEighths.Record1252270103Source.corrected_source_geometry_of_caps
#print axioms OAI.SevenEighths.Record1252270103Source.corrected_child_geometry_of_caps
