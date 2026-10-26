/- Copyright (c) 2026 Sil. Apache-2.0.
Actual selected-prime products have an annular product, rather than a
single dyadic, upper endpoint. Keep the exact selected-volume average
and the resulting fourth-power scale; pay its fixed padding only once.

-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstAveragedWindow
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedSupplierPositive

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedSelectedVolume
universe u v
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open MixedPrincipalPair MixedPrincipalWindow MixedSupplierFourthRow MixedSupplierPositive
open MixedFirstAveragedWindow
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type u} [Fintype α] {ι : Type v} [Fintype ι] {a b : ℝ}

def volume (q : Data α) : ℝ := ∏j : q.J,q.P j.val.val
def padding (q : Data α) : ℝ := (2:ℝ)^(Fintype.card q.J)
def scale (q : Data α) : ℝ := padding q*volume q

theorem padding_pos (q : Data α) : 0<padding q := by
  unfold padding
  positivity

theorem volume_pos (q : Data α) (hP : ∀i,0<q.P i) : 0<volume q :=
  Finset.prod_pos (fun j _=>hP j.val.val)

theorem scale_pos (q : Data α) (hP : ∀i,0<q.P i) : 0<scale q :=
  mul_pos (padding_pos q) (volume_pos q hP)

/-- No extra cardinality assumption is needed for the actual selected
subtype: its map into the original finite slot type is injective. -/
theorem selected_card_le (q : Data α) : Fintype.card q.J≤Fintype.card α :=
  Fintype.card_le_of_injective (fun j : q.J=>j.val.val)
    (fun i j he=>Subtype.ext (Subtype.ext he))

theorem padding_le (q : Data α) (N : ℕ) (hN : Fintype.card α≤N) :
    padding q≤(2:ℝ)^N :=
  pow_le_pow_right₀ (by norm_num) ((selected_card_le q).trans hN)

/-- This uses the actual amplitudes' active pools and the actual image
of supported selected assignments. No hypothetical product window. -/
theorem selected_products_norm (q : Data α)
    (hpool : ∀i,∀I∈q.pool i,(I.absNorm:ℝ)≤2*q.P i)
    (F : Id) (hF : F∈selectedProducts q) : (F.absNorm:ℝ)≤scale q := by
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hF
  exact selected_product_annular_upper q y (Finset.mem_filter.mp hy).1 hpool

/-- The denominator is the literal product of selected slot scales. -/
theorem average_exact (q : Data α) (hP : ∀i,0<q.P i) (A : ℝ) :
    A/volume q=padding q*(A/scale q) := by
  have hc : padding q≠0 := (padding_pos q).ne'
  have hp : volume q≠0 := (volume_pos q hP).ne'
  unfold scale
  field_simp <;> ring

/-- Constants precede the actual supplier data, source, weights, heights
and windows. The only weight premise is its pointwise finite cap; no
energy estimate or fifth-free assertion is assumed. The output keeps
K4=16*K*(2^#J*Psel)^4 and its own single division by the padded scale. -/
theorem actual_selected_volume_average (ε : ℝ) (hε : 0<ε) :
    ∃C0 : ℝ,0<C0 ∧ ∀q : Data α,
      (∀i,0<q.P i)→
      (∀i,∀I∈q.pool i,(I.absNorm:ℝ)≤2*q.P i)→
    ∀s : Source ι a b,∀ha : 0<a,
    ∀(C G seed D : Id)(hG : G≠0)(τ : Character)(t : ℝ),
    ∀(right : Bool)(V : ℝ→ℂ)(X θ : ℝ)(rows : Finset O),
      (∀z∈rows,z≠0)→
    ∀(w : Id→ℝ)(K L : ℝ),0<K→0≤L→
      (∀F∈selectedProducts q,0≤w F∧w F≤L)→
      (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤K)→
    (∑F∈selectedProducts q,w F*
      ∑z∈rows,‖selectedRow s ha C G seed D hG τ t right V X θ F z‖^2)/volume q≤
      padding q*(L*C0*(16*K*(scale q)^4)^ε*
        outputEnergy s ha C G seed D hG τ t right V X θ K (scale q)) := by
  obtain ⟨C0,hC0,hbound⟩ :=
    actual_selected_window_average (ι:=ι) (a:=a) (b:=b) ε hε
  refine ⟨C0,hC0,?_⟩
  intro q hP hpool s ha C G seed D hG τ t right V X θ rows hrows w K L hK hL hw hzN
  have hscale := scale_pos q hP
  have hFN (F : Id) (hF : F∈selectedProducts q) : (F.absNorm:ℝ)≤2*scale q :=
    (selected_products_norm q hpool F hF).trans (by linarith)
  have he := hbound s ha C G seed D hG τ t right V X θ
    (selectedProducts q) rows (selected_products_supported q) hrows
    w (scale q) K L hscale hK hL hw hFN hzN
  rw [average_exact q hP]
  exact mul_le_mul_of_nonneg_left he (padding_pos q).le

/-- Equality of the actual physical scale, not replacement by a smaller
kernel or monotonicity of a windowed energy. -/
theorem fourth_scale_exact (q : Data α) (K : ℝ) :
    16*K*(scale q)^4=(padding q)^4*(16*K*(volume q)^4) := by
  unfold scale
  ring

/-- In particular the physical scale itself has no new fixed exponent.
This cap is uniform before the actual slot pools and before K. -/
theorem eventually_fourth_scale (N : ℕ) (loss : ℝ) (hloss : 0<loss) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀q : Data α,Fintype.card α≤N→
      ∀K : ℝ,0≤K→16*K*(scale q)^4≤Z^loss*(16*K*(volume q)^4) := by
  have hc : ∀ᶠZ : ℝ in atTop,((2:ℝ)^N)^4≤Z^loss :=
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hloss)) _
  filter_upwards [hc,Filter.eventually_gt_atTop (1:ℝ)] with Z hc hZ
  refine ⟨hZ,?_⟩
  intro q hN K hK
  rw [fourth_scale_exact]
  exact mul_le_mul_of_nonneg_right
    ((pow_le_pow_left₀ (padding_pos q).le (padding_le q N hN) 4).trans hc)
    (by positivity)

theorem fourth_prefactor_exact (q : Data α) (K ε : ℝ) (hK : 0≤K) :
    padding q*(16*K*(scale q)^4)^ε=
      (padding q*((padding q)^4)^ε)*(16*K*(volume q)^4)^ε := by
  rw [fourth_scale_exact,Real.mul_rpow (by positivity) (by positivity)]
  ring

/-- One fixed constant controls all choices of the selected subset.
Its threshold is chosen before q, not once for each small slot. -/
theorem eventually_padding_cost (N : ℕ) (ε loss : ℝ)
    (hε : 0≤ε) (hloss : 0<loss) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀q : Data α,Fintype.card α≤N→
      padding q*((padding q)^4)^ε≤Z^loss := by
  have hc : ∀ᶠZ : ℝ in atTop,
      (2:ℝ)^N*(((2:ℝ)^N)^4)^ε≤Z^loss :=
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hloss)) _
  filter_upwards [hc,Filter.eventually_gt_atTop (1:ℝ)] with Z hc hZ
  refine ⟨hZ,?_⟩
  intro q hN
  have hp := padding_le q N hN
  apply le_trans _ hc
  exact mul_le_mul hp
    (Real.rpow_le_rpow (by positivity)
      (pow_le_pow_left₀ (padding_pos q).le hp 4) hε)
    (Real.rpow_nonneg (by positivity) _) (by positivity)

/-- The explicit padding of the prefactor costs an arbitrarily small
power, uniformly in K and in all actual pool scales. The output energy
still has the exact padded scale and must be estimated at that scale. -/
theorem eventually_fourth_prefactor (N : ℕ) (ε loss : ℝ)
    (hε : 0≤ε) (hloss : 0<loss) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀q : Data α,Fintype.card α≤N→
      ∀K : ℝ,0≤K→padding q*(16*K*(scale q)^4)^ε≤
        Z^loss*(16*K*(volume q)^4)^ε := by
  filter_upwards [eventually_padding_cost (α:=α) N ε loss hε hloss] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro q hN K hK
  rw [fourth_prefactor_exact q K ε hK]
  exact mul_le_mul_of_nonneg_right (hZ.2 q hN)
    (Real.rpow_nonneg (by positivity) _)

end
end Candidate.FourthPower.MixedSelectedVolume
