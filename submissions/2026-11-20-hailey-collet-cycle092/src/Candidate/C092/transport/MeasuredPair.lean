/- Copyright (c) 2026 Hailey Collet. Apache-2.0. Large measured-response branch
of P.1 on the original fixed-cofactor core. -/
import Candidate.C092.transport.MeasuredOperator
namespace QRH.Cycle092.MeasuredPair
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open Filter Set OAI OAI.SevenEighths CanonicalRowCompletion ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily CenteredMomentSourceMass
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentPrimeSlot CenteredMomentWholeSlotDeletion Qrh.JointDetector WholeWordAmplification
open QRH.Cycle092.OrdinaryColumn
local notation "O" => ActualEisensteinCubic.O
local instance c092LocalInst_Candidate_C092_transport_MeasuredPair_2f4ecbd41aba7aeb_001 (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

def response {α : Type} [Fintype α] [DecidableEq α] (rayM : Ideal O) [NeZero rayM]
    (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H) {Z bΦ : ℝ}
    (st : NaturalState Z 0 bΦ) (η₀ : Character) (W : ℝ → ℂ) (T : Finset α)
    (θ : T → RayQuotient.Characters rayM H) (w σ v : T → ℝ) (t pay : ℝ) (z : O) :=
  LowActual.originalResponse st.character st.mask 1 t Z pay w
    (fun k => primePool rayM H 2 (Z^w k))
    (fun k I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I * HeckePrimeAnnular.annularWeight W (Z^w k) (σ k) (v k) I)
    (fun k => Z^w k) z

theorem response_on_root {α : Type} [Fintype α] [DecidableEq α] (rayM : Ideal O) [NeZero rayM]
    (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H) {Z bΦ : ℝ}
    (st : NaturalState Z 0 bΦ) (η₀ : Character) (W : ℝ → ℂ) (T : Finset α)
    (θ : T → RayQuotient.Characters rayM H) (w σ v : T → ℝ) (t pay : ℝ)
    (root : NonzeroIdeal) (u : FreeRow) :
    response rayM H hH st η₀ W T θ w σ v t pay (rowMap (u,root)) ≤
      let d := ActualSlotData.data rayM H hH st η₀ W T θ w σ v (fun _ => 0) t root
      LowActual.response Z pay d.width (fun j => ‖d.polynomial j u.val‖^2) := by
  dsimp only; apply (LowActual.response_le_iff ..).2
  refine ⟨LowActual.response_nonneg ..,?_⟩; intro k
  have ⟨_,hall⟩ := (LowActual.response_le_iff ..).mp (le_refl (LowActual.response Z pay
    (ActualSlotData.data rayM H hH st η₀ W T θ w σ v (fun _ => 0) t root).width
    (fun j => ‖(ActualSlotData.data rayM H hH st η₀ W T θ w σ v (fun _ => 0) t root).polynomial j u.val‖^2)))
  specialize hall ((Fintype.equivFin α) k.val)
  rw [(ActualSlotData.data_active rayM H hH st η₀ W T θ w σ v (fun _ => 0) t root k).1,
    ActualSlotData.data_polynomial_active] at hall
  exact hall

/-- The finite dictionary, buffer, characters, profiles and all caps are chosen after the mesh.
The ordinary length product may carry a fixed annulus and dictionary factor. -/
theorem energy (amax loss : ℝ) (ha : 1 ≤ amax) (hl : 0 < loss) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ (α : Type) [Fintype α] [DecidableEq α] (W : ℝ → ℂ), Continuous W →
    Function.support W ⊆ Icc (1:ℝ) 2 → ∀ b : ℝ, 0 < b → ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
    1 < Z ∧ ∀ (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (bΦ : ℝ) (st : NaturalState Z 0 bΦ) (η₀ : Character) (T : Finset α)
    (θ : T → RayQuotient.Characters rayM H) (w σ v : T → ℝ) (t mesh pay V Y : ℝ) (root : NonzeroIdeal) (cores : Finset FreeRow),
      0 ≤ mesh → mesh ≤ μ → (∀ k, 0 ≤ w k) → (∀ k, w k ≤ mesh) → (∀ k, σ k ∈ Icc (33/50:ℝ) (33/50)) →
      Z^(2*b) ≤ pay → (∀ u ∈ cores, 5002/10000 < response rayM H hH st η₀ W T θ w σ v t pay (rowMap (u,root))) →
      98/100 ≤ V → 1 ≤ Y → Y ≤ Z^amax → Y ≤ Z^V → (∀ u ∈ cores, rowNorm u ≤ Y) →
    ∀ (η₁ η₂ : Character) (m A₁ A₂ : O), goodLambda ∣ m → (2:O) ∣ m →
    ∀ (W₁ W₂ : ℝ → ℂ) (t₁ t₂ P Q B₁ B₂ : ℝ), 0 < P → 0 < Q →
      Function.support W₁ ⊆ Iic (9/4:ℝ) → Function.support W₂ ⊆ Iic (9/4:ℝ) →
      (∀ I ∈ idealBall (9/4*P), ‖W₁ ((I.absNorm:ℝ)/P)‖ ≤ B₁) → (∀ I ∈ idealBall (9/4*Q), ‖W₂ ((I.absNorm:ℝ)/Q)‖ ≤ B₂) →
      P*Q*Z^(∑ i,w i) ≤ Z^(9179599/10000000:ℝ) →
      (∑ u ∈ cores, (‖original η₁ m A₁ (rowMap (u,root)) W₁ t₁ P‖^2 * ‖original η₂ m A₂ (rowMap (u,root)) W₂ t₂ Q‖^2)*
        RefinedSupplier.slotMass rayM H hH st η₀ W θ w σ v t (rowMap (u,root))) ≤ C*Z^(V-305/10000+loss)*(B₁^2*B₂^2) := by
  obtain ⟨μ,hμ,hmesh⟩ := MeasuredOperator.operator amax (loss/2) ha (by positivity)
  refine ⟨μ,hμ,?_⟩; intro α _ _ W hW hs b hb
  obtain ⟨B,hB,hd⟩ := ActualSlotData.data_bounded W hW hs
  obtain ⟨C,hC,he⟩ := hmesh B b (zero_le_one.trans hB) hb
  let n := Fintype.card α
  let D := wordDivisorConstant (n+2) (loss/2) (by positivity)
  have hD : 0 < D := wordDivisorConstant_pos _ _ _
  have hBp : 0 < B := zero_lt_one.trans_le hB
  refine ⟨((n:ℝ)+1)*C*D*(128*(9/4))^2*B^n,by positivity,?_⟩
  filter_upwards [he,(tendsto_rpow_atTop (show (0:ℝ) < 919/1000-9179599/10000000 by norm_num)).eventually_ge_atTop ((9/4:ℝ)^2*2^n)] with Z h hcollar
  obtain ⟨hZ,hop⟩ := h; have hZ0 := zero_lt_one.trans hZ
  refine ⟨hZ,?_⟩; intro rayM _ H hH bΦ st η₀ T θ w σ v t mesh pay V Y root cores hm hm' hw hwm hσ hp hmeas hV hY hYa hYV hrad η₁ η₂ m A₁ A₂ hm₁ hm₂ W₁ W₂ t₁ t₂ P Q B₁ B₂ hP hQ hs₁ hs₂ hW₁ hW₂ hcap
  let X := Z^(919/1000:ℝ)
  have hX : 1 ≤ X := Real.one_le_rpow hZ.le (by norm_num)
  have hXz : X ≤ Z := (Real.rpow_le_rpow_of_exponent_le hZ.le (show (919/1000:ℝ) ≤ 1 by norm_num)).trans_eq (Real.rpow_one Z)
  have hbd := hd α rayM H hH Z bΦ st η₀ T θ w σ v (fun _ => 0) t root mesh hZ hm hw hwm hσ
  have hn := hop n _ cores mesh V Y X pay hm hm' hbd hp (fun u hu => (hmeas u hu).trans_le (response_on_root rayM H hH st η₀ W T θ w σ v t pay root u)) hV hY hYa hYV hrad hX le_rfl
  have hsup : (9/4*P)*(9/4*Q*((2:ℝ)^n*Z^(∑ i,w i))) ≤ X := by
    calc
      _ = ((9/4:ℝ)^2*2^n)*(P*Q*Z^(∑ i,w i)) := by ring
      _ ≤ Z^(919/1000-9179599/10000000:ℝ)*Z^(9179599/10000000:ℝ) := mul_le_mul hcollar hcap (by positivity) (by positivity)
      _ = _ := by rw [←Real.rpow_add hZ0]; norm_num [X]
  have hs := ActualColumn.pair_at α rayM H hH st η₀ W T θ w σ v t root mesh B hbd cores η₁ η₂ m A₁ A₂ hm₁ hm₂ W₁ W₂ t₁ t₂ (9/4) (9/4) P Q B₁ B₂ (n*(C*Z^(V-305/10000+loss/2))) X (loss/2) hZ0 (by norm_num) (by norm_num) hP hQ hs₁ hs₂ hW₁ hW₂ (by positivity) hX (by positivity) hsup hn
  have hx := Real.rpow_le_rpow (zero_le_one.trans hX) hXz (by positivity : 0 ≤ loss/2)
  apply hs.trans
  calc
    _ ≤ ((n:ℝ)+1)*(C*Z^(V-305/10000+loss/2))*(D*Z^(loss/2)*((128*(9/4)*B₁^2)*((128*(9/4)*B₂^2)*B^n))) := by dsimp only [D,n] at *; gcongr <;> linarith
    _ = _ := by rw [show V-305/10000+loss = (V-305/10000+loss/2)+(loss/2) by ring,Real.rpow_add hZ0 (V-305/10000+loss/2) (loss/2)]; ring

#print axioms energy
end
end QRH.Cycle092.MeasuredPair
