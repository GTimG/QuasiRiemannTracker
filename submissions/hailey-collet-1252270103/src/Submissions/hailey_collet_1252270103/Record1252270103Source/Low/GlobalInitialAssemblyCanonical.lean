/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The single retained canonical norm and its exact original-slot subset dictionary. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.GlobalInitialAssemblyReindex
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.GlobalInitialFiniteJoin
import Submissions.hailey_collet_1252270103.Record1252270103Source.Collision.SourceLift
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
open CenteredMomentDetectorEnergyInitialState QuadraticInitialBound ConcreteTraceCRT CenteredMomentPrimeSlot
open QRH.Record12518109Source QRH.Record1252270103Source QRH.Record1252270103Source.Collision
local notation "O"=>HeckeFamily.O
variable {α : Type} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)

def CanonicalMarkedAt (face : SourceFace) (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W)
    (hsW : Function.support W⊆Set.Icc (1:ℝ) 2) (bΦ mesh ε Z : ℝ)
    (η η₀ : Character) (Q R₀ : Ideal O) (degree : ℕ) (controls : Finset (ℕ×ℕ)) (C : ℝ) : Prop :=
  ∀hZ : 1<Z,∀T : Finset α,
  ∀(θ : T→RayQuotient.Characters rayM H)(w v : T→ℝ)(t height : ℝ),
    (∀i,0≤w i) → (∀i,w i≤mesh) → 0≤height → (∀i,|v i|≤height) →
  ∀p : Profiles (1/4) (9/4),∀X₁ X₂ : ℝ,∀hX₁ : 0<X₁,∀hX₂ : 0<X₂,
    face.Admissible (length Z X₁) (length Z X₂) (∑i,w i) 1 →
  ∀(rows : Finset O)(Φ : 𝓢(ℝ,ℂ)),Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ → (∀x,0≤(Φ x).re) →
  markedFiniteEnergy
    (initialInput rayM H hH W hW hsW Z (zero_lt_one.trans hZ) η η₀ R₀ θ w v t p (by norm_num)
      X₁ X₂ X₁ X₂ hX₁ hX₂ hX₁ hX₂ rfl)
    R₀ 1 (9/4) X₁ X₂ rows (initialKeep η (internalQ Q η₀)) Φ Z≤
    C*diagonalControl Φ*(p.control controls)^2*(1+|t|+height)^degree*Z^(1+ε)

lemma embedding_width_le {ι J : Type*} [Fintype ι] [Fintype J] (f : J↪ι)
    (w : ι→ℝ) (hw : ∀i,0≤w i) : (∑j,w (f j))≤∑i,w i := by
  classical
  have he:=(slotRangeEquiv f).sum_comp (fun i:slotRange f=>w i)
  simp only [slotRangeEquiv_coe] at he
  rw [he,Finset.sum_coe_sort]
  exact Finset.sum_le_univ_sum_of_nonneg hw

theorem canonical_marked_projected (B lam cap : ℝ) (hlam : 0≤lam)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hsW : Function.support W⊆Set.Icc (1:ℝ) 2)
    (bΦ mesh ε Z : ℝ) (hZ : 1<Z) (η η₀ : Character) (Q R₀ : Ideal O)
    (degree : ℕ) (controls : Finset (ℕ×ℕ)) (C : ℝ)
    (hsource : CanonicalMarkedAt (α:=α) rayM H hH (globalFace B lam cap) W hW hsW
      bΦ mesh ε Z η η₀ Q R₀ degree controls C) :
    ProjectedInitialAffineAt (α:=α) rayM H hH (globalFace B lam cap) W (1/4) (9/4)
      bΦ mesh (33/50) (33/50) 1 1 ε Z η η₀ Q R₀ degree controls C := by
  intro T θ w σ v t height hw hmesh hσlo hσhi hh hv M hMlo hMhi Φ hsΦ hΦ p X₁ X₂ hX₁ hX₂ hadm
  have hM : M=1:=by linarith
  subst M
  have hσ : σ=(fun _=>33/50):=funext (fun i=>le_antisymm (hσhi i) (hσlo i))
  subst σ
  dsimp only
  intro rows J _ f
  classical
  let g : J↪α:=f.trans ⟨Subtype.val,Subtype.val_injective⟩
  let F:=slotRange g
  let e : J≃F:=slotRangeEquiv g
  let θ' : F→RayQuotient.Characters rayM H:=fun i=>θ (f (e.symm i))
  let w' : F→ℝ:=fun i=>w (f (e.symm i))
  let v' : F→ℝ:=fun i=>v (f (e.symm i))
  have hsum : (∑i,w' i)≤∑i,w i := by
    rw [show (∑i,w' i)=∑j,w (f j) from e.symm.sum_comp (fun j=>w (f j))]
    exact embedding_width_le f w hw
  have hface:=(globalFace_downward hlam (length_nonneg Z X₁ hZ) (length_nonneg Z X₂ hZ)
    (Finset.sum_nonneg (fun i _=>hw i)) hadm (length_nonneg Z X₁ hZ) (length_nonneg Z X₂ hZ)
    (Finset.sum_nonneg (fun i _=>hw (f (e.symm i)))) le_rfl le_rfl hsum)
  have hb:=hsource hZ F θ' w' v' t height (fun i=>hw _) (fun i=>hmesh _) hh (fun i=>hv _)
    p X₁ X₂ hX₁ hX₂ hface rows Φ hsΦ hΦ
  let S:=fun i:T=>primePool rayM H 2 (Z^(w i))
  let β:=fun (i:T) I=>idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I*
    HeckePrimeAnnular.annularWeight W (Z^(w i)) (33/50) (v i) I
  let atoms:=Finset.univ.biUnion S
  have hp : ∀I∈atoms,Prime I := by
    intro I hI
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hI
    exact (Finset.mem_filter.mp hi).2.1
  have he (z : O) :
      markedPositiveRow η (fixedBadMask*idealGenerator R₀) 1 z (p.profile 0) (p.profile 1) (9/4)
        (fun i:F=>S (f (e.symm i))) (fun i:F=>β (f (e.symm i)))
        (fun i:F=>Z^(w (f (e.symm i)))) t X₁ X₂=
      markedPositiveRow η (fixedBadMask*idealGenerator R₀) 1 z (p.profile 0) (p.profile 1) (9/4)
        (fun j=>S (f j)) (fun j=>β (f j)) (fun j=>Z^(w (f j))) t X₁ X₂ :=
    markedPositiveRow_equiv η _ 1 z _ _ (9/4) (fun j=>S (f j)) (fun j=>β (f j))
      (fun j=>Z^(w (f j))) t X₁ X₂ e.symm
  have hnorm (z : O) := weightedPlain_marked_row_norm η (fixedBadMask*idealGenerator R₀) 1 z t
    (p.profile 0) (p.profile 1) (9/4) X₁ X₂ (initialKeep η (internalQ Q η₀)) Φ Z
    (fun j=>S (f j)) (fun j=>β (f j)) (fun j=>Z^(w (f j))) atoms
    (fun j I hI=>Finset.mem_biUnion.mpr ⟨f j,Finset.mem_univ _,hI⟩) hp hX₁ hX₂
    (fun j=>(Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).le) hΦ
  simp only [Real.rpow_one]
  change (∑z∈rows,if initialKeep η (internalQ Q η₀) z then
    ‖markedPositiveRow η (fixedBadMask*idealGenerator R₀) 1 z (p.profile 0) (p.profile 1) (9/4)
      (fun i:F=>S (f (e.symm i))) (fun i:F=>β (f (e.symm i)))
      (fun i:F=>Z^(w (f (e.symm i)))) t X₁ X₂‖^2*(Φ (‖eisEmbedding z‖^2/Z)).re else 0)≤_ at hb
  simp only [he] at hb
  convert hb using 1
  apply Finset.sum_congr rfl
  intro z hz
  exact hnorm z

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.embedding_width_le
#print axioms QRH.Record1252270103Low.canonical_marked_projected
