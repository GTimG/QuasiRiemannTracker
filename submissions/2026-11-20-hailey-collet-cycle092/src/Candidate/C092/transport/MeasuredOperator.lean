/- Copyright (c) 2026 Hailey Collet. Apache-2.0. Cover by the actual observed
large marks; the maximizing index can change from row to row. -/
import Candidate.C092.transport.MeasuredMark
namespace QRH.Cycle092.MeasuredOperator
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths CanonicalRowCompletion ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open Qrh.JointDetector Qrh.JointDetector.FineDetectorWords
local notation "O" => ActualEisensteinCubic.O

theorem cover {α : Type*} {N : ℕ} (s : Finset α) (p : Fin N → α → Prop) [∀ j,DecidablePred (p j)]
    (f : α → ℝ) (hf : ∀ x ∈ s, 0 ≤ f x) (hp : ∀ x ∈ s, ∃ j, p j x) :
    ∑ x ∈ s,f x ≤ ∑ j, ∑ x ∈ s.filter (p j), f x := by
  simp only [Finset.sum_filter]; rw [Finset.sum_comm]; apply Finset.sum_le_sum
  intro x hx; obtain ⟨j,hj⟩ := hp x hx
  simpa [hj] using (Finset.single_le_sum (f:=fun i => if p i x then f x else 0)
    (fun i _ => by split <;> simp_all only [le_refl]) (Finset.mem_univ j))

theorem operator (amax loss : ℝ) (ha : 1 ≤ amax) (hl : 0 < loss) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ B b : ℝ, 0 ≤ B → 0 < b →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (N : ℕ) (d : SelectedSlotData N) (cores : Finset FreeRow)
        (mesh V Y X pay : ℝ), 0 ≤ mesh → mesh ≤ μ → d.Bounded Z mesh B → Z^(2*b) ≤ pay →
        (∀ z ∈ cores, 5002/10000 < LowActual.response Z pay d.width (fun j => ‖d.polynomial j z.val‖^2)) →
        98/100 ≤ V → 1 ≤ Y → Y ≤ Z^amax → Y ≤ Z^V → (∀ z ∈ cores, rowNorm z ≤ Y) →
        1 ≤ X → X ≤ Z^(919/1000:ℝ) → ∀ (S : Finset (Ideal O)) (c : S → ℂ),
        (∀ I ∈ S, (I.absNorm : ℝ) ≤ X) →
          (∑ z : cores.image Subtype.val, ‖FineDetectorWords.ordinaryPolynomial S c z.val‖^2) ≤
            N*(C*Z^(V-305/10000+loss))*∑ I, ‖c I‖^2 := by
  classical
  obtain ⟨μ,hμ,hmesh⟩ := SelectedMark.operator amax loss ha hl
  refine ⟨μ,hμ,?_⟩; intro B b hB hb
  obtain ⟨C,hC,he⟩ := hmesh B b hB hb
  refine ⟨C,hC,?_⟩
  filter_upwards [he, (tendsto_rpow_atTop hb).eventually_ge_atTop (256*B)] with Z hh hbig
  obtain ⟨hZ,hop⟩ := hh; refine ⟨hZ,?_⟩
  intro N d cores mesh V Y X pay hm hm' hd hp hmeas hV hY hYa hYV hrad hX hX' S c hS
  let p (j : Fin N) (z : FreeRow) : Prop := b ≤ d.width j ∧ Z^((5001/10000:ℝ)*d.width j) ≤ ‖d.polynomial j z.val‖^2
  let f (z : FreeRow) := ‖FineDetectorWords.ordinaryPolynomial S c z.val‖^2
  have hpos : 1 ≤ pay := (Real.one_le_rpow hZ.le (by positivity : 0 ≤ 2*b)).trans hp
  have hpay : (256*B)*Z^b ≤ pay := by
    calc
      _ ≤ Z^b*Z^b := mul_le_mul_of_nonneg_right hbig (by positivity)
      _ = Z^(2*b) := by rw [two_mul,Real.rpow_add (zero_lt_one.trans hZ)]
      _ ≤ _ := hp
  have hc := cover cores p f (fun _ _ => sq_nonneg _) (fun z hz => MeasuredMark.exists_wide d hd hZ hb hpos hpay z.val (hmeas z hz))
  let K := C*Z^(V-305/10000+loss)*(∑ I, ‖c I‖^2)
  have hj (j : Fin N) : ∑ z ∈ cores.filter (p j), f z ≤ K := by
    by_cases hw : b ≤ d.width j
    · have hh := hop N d j (cores.filter (p j)) mesh V Y X hm hm' hd hw (fun z hz => (Finset.mem_filter.mp hz).2.2) hV hY hYa hYV (fun z hz => hrad z (Finset.mem_filter.mp hz).1) hX hX' S c hS
      rw [Finset.sum_coe_sort _ (fun z : O => ‖FineDetectorWords.ordinaryPolynomial S c z‖^2),Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)] at hh
      exact hh
    · have hz : cores.filter (p j) = ∅ := Finset.filter_eq_empty_iff.mpr (fun _ _ hx => hw hx.1)
      rw [hz,Finset.sum_empty]; dsimp [K]; positivity
  rw [Finset.sum_coe_sort _ (fun z : O => ‖FineDetectorWords.ordinaryPolynomial S c z‖^2),Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)]
  exact hc.trans ((Finset.sum_le_sum (fun j _ => hj j)).trans_eq (by simp [K,mul_assoc]))

#print axioms operator
end
end QRH.Cycle092.MeasuredOperator
