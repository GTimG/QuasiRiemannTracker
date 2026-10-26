/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Attained cell weights stay paired with their own radial source budgets. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.RetainedLowErasedCollected
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.RegularLowBudgetControlSum
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalLowCellPayment
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.RetainedLow
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths Filter HeckeFamily CanonicalQuadraticSieve
open CenteredMomentEnergyBands Cycle61InitialMass CenteredMomentFiniteProfileExceptional
open Record12518109Raw QRH.Record1252270103Restoration QRH.Record1252270103KernelMass
open OAI.SevenEighths.Record1252270103Low
open LowErasure RegularLowScaleGrouping RegularLowBudgetControl
local notation "O"=>HeckeFamily.O

lemma raw_length_cap (Z X B : ℝ) (hZ : 1<Z) (hB : 0≤B) (hX : X≤Z^B) :
    length Z X≤B := by
  rw [←length_power Z B hZ hB]
  unfold length
  exact (Real.logb_le_logb hZ (by positivity) (by positivity)).mpr
    (max_le_max_left 1 hX)

def paidCellRows {Row Slot : Type*} [DecidableEq Slot] (rows : Finset Row)
    (select : Row→Finset Slot) (tag : Row→Fin 3→ℤ) (value : Row→ℂ)
    (F : Finset Slot) (k : Fin 3→ℤ) : Finset Row :=
  ((rows.filter (fun r=>value r≠0)).filter (fun r=>select r=F)).filter (fun r=>tag r=k)

lemma sdiff_classical_eq {Slot : Type*} [DecidableEq Slot] (T F : Finset Slot) :
    @SDiff.sdiff (Finset Slot)
      (@Finset.instSDiff Slot (fun a b=>Classical.propDecidable (a=b))) T F=T\F := by
  ext j;simp only [Finset.mem_sdiff]

theorem paid_cell_budgets (rayCount N : ℕ) (width Bscale₀ Mmin Mmax : ℝ)
    (hwidth : 0<width) (hscale : 0≤Bscale₀) (hMmin : 0<Mmin)
    (a b : ℝ) (ha : 0<a) (TP : Finset (ℕ×ℕ))
    (CP DP Craw : ℝ) (hCP : 0≤CP) (hDP : 0≤DP) (hCraw : 0≤Craw)
    (degreeP : ℕ) (Φ : 𝓢(ℝ,ℂ)) (Bmask εmask δ Brestore εwindow : ℝ)
    (hεmask : 0≤εmask) (hεwindow : 0<εwindow) :
    ∃J : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(Row Slot : Type)[DecidableEq Slot](rows : Finset Row)(T : Finset Slot),T.card≤N →
    ∀(p : Profiles a b)(t height εsource loss factor Cslot target massLoss gapH εlow d q : ℝ),
      0≤height → 0≤factor → 1≤Cslot → 0≤εlow → 0≤d →
    ∀(R : Ideal O),R≠0 → (R.absNorm:ℝ)≤Z^Bmask →
    ∀(X₁ X₂ weight x₀ x₁ radius side : Row→ℝ)(select : Row→Finset Slot)
      (value : Row→ℂ)(w : Slot→ℝ)(hi Bmissing γ lo : ℝ),hi≤Bmissing →
      (∀r∈rows,select r⊆T) → (∀r∈rows,0≤weight r) →
      (∀r∈rows,value r≠0 → X₁ r≤Z^Bscale₀ ∧ X₂ r≤Z^Bscale₀) →
      (∀r∈rows,value r≠0 → Mmin≤radius r ∧ radius r≤Mmax) →
      (∀r∈rows,value r≠0 → weight r≤factor*Z^(massLoss+x₀ r-side r)) →
      (∀r∈rows,value r≠0 → hi≤x₁ r+gapH) →
      (∀r∈rows,value r≠0 → x₀ r+x₁ r+radius r-side r+q*∑j∈T\select r,w j≤target) →
      let live:=rows.filter (fun r=>value r≠0)
      let tag:=fun r=>key width Z (X₁ r) (X₂ r) (radius r)
      ∃A : Finset Slot→(Fin 3→ℤ)→ℝ,(∀F k,0≤A F k) ∧
        (∀r∈rows,value r≠0 → weight r≤A (select r) (tag r)) ∧
      (∑F∈T.powerset,∑k∈(live.filter (fun r=>select r=F)).image tag,
        cellBudget rayCount a b ha TP CP DP Craw degreeP Φ p
          Z t height εsource loss δ Brestore εmask R (radial width Mmax k)
          (Z^(exponentBinUpper width k 0)) (Z^(exponentBinUpper width k 1)) (A F k)
          (erasurePayment Z q (Cslot*Z^(2*εlow*d)) w T F) (hi*(1+εmask)-γ*lo))≤
      C*(p.control S)^2*(1+|t|+height)^J*factor*Cslot^N*
        Z^(target+massLoss+width+gapH+εmask*Bmissing+2*εlow*d*N-γ*lo+
          εsource+loss+2*δ+Bmask*εmask+εwindow) := by
  let bound:=max Bscale₀ Mmax
  let Kbox:=(Finset.Icc (⌊-bound/width⌋:ℤ) ⌊bound/width⌋).card^3
  obtain ⟨J,S,C,hC,hcontrol⟩:=global_raw_restored_budget_sum rayCount (2^N*Kbox)
    a b ha TP CP DP Craw hCP hDP hCraw degreeP Φ (Bscale₀+width) Bmask εmask δ Brestore
    εwindow (by linarith) hεmask hεwindow
  refine ⟨J,S,C,hC,?_⟩
  filter_upwards [hcontrol] with Z hz
  refine ⟨hz.1,?_⟩
  intro Row Slot _ rows T hTN p t height εsource loss factor Cslot target massLoss gapH εlow d q
    hheight hfactor hCslot hεlow hd R hR hRcap X₁ X₂ weight x₀ x₁ radius side select value w
    hi Bmissing γ lo hmissing hselect hweight hraw hradius hmass hH hprice live tag
  have hZ:=hz.1
  have hZ0:=zero_lt_one.trans hZ
  have hc (F : Finset Slot)(k : Fin 3→ℤ) :
      ∃A : ℝ,0≤A ∧ (∀r∈paidCellRows rows select tag value F k,weight r≤A) ∧
        A*erasurePayment Z q (Cslot*Z^(2*εlow*d)) w T F*
          Z^(radial width Mmax k+hi*(1+εmask)-γ*lo)≤
        factor*Cslot^N*Z^(target+massLoss+width+gapH+εmask*Bmissing+2*εlow*d*N-γ*lo) := by
    let cell:=paidCellRows rows select tag value F k
    have hmem (r : Row)(hr : r∈cell) : r∈rows ∧ value r≠0 ∧ select r=F ∧ tag r=k := by
      obtain ⟨hr,hk⟩:=Finset.mem_filter.mp hr
      obtain ⟨hr,hF⟩:=Finset.mem_filter.mp hr
      obtain ⟨hr,hn⟩:=Finset.mem_filter.mp hr
      exact ⟨hr,hn,hF,hk⟩
    by_cases hn : cell.Nonempty
    · obtain ⟨A,hA,hdom,_,hp⟩:=High.GlobalPhysical.low_cell_weight_payment cell hn
        weight x₀ x₁ radius side w T F N Z factor massLoss q Cslot εlow d
        (radial width Mmax k) hi Bmissing εmask width gapH target (-γ*lo)
        hZ hfactor hCslot hεlow hd hεmask
        (by rw [sdiff_classical_eq];exact (Finset.card_le_card Finset.sdiff_subset).trans hTN) hmissing
        (fun r hr=>hweight r (hmem r hr).1)
        (fun r hr=>hmass r (hmem r hr).1 (hmem r hr).2.1)
        (fun r hr=>(same_key_radial width Z (X₁ r) (X₂ r) (radius r) Mmin Mmax hwidth k
          (hmem r hr).2.2.2 (hradius r (hmem r hr).1 (hmem r hr).2.1).1
          (hradius r (hmem r hr).1 (hmem r hr).2.1).2).2.2.2)
        (fun r hr=>hH r (hmem r hr).1 (hmem r hr).2.1)
        (by
          intro r hr
          rw [sdiff_classical_eq]
          simpa only [(hmem r hr).2.2.1] using hprice r (hmem r hr).1 (hmem r hr).2.1)
      exact ⟨A,hA,hdom,by convert hp using 1 <;> ring⟩
    · refine ⟨0,le_refl _,?_,?_⟩
      · intro r hr;exact False.elim (hn ⟨r,hr⟩)
      · simp only [zero_mul];positivity
  choose A hA hdom hpaid using hc
  refine ⟨A,hA,?_,?_⟩
  · intro r hr hn
    exact hdom (select r) (tag r) r (by simp [paidCellRows,hr,hn])
  let cells:=T.powerset.sigma (fun F=>(live.filter (fun r=>select r=F)).image tag)
  have hbox (r : Row)(hr : r∈live)(i : Fin 3) :
      -bound≤coordinates Z (X₁ r) (X₂ r) (radius r) i ∧
        coordinates Z (X₁ r) (X₂ r) (radius r) i≤bound := by
    have hr':=Finset.mem_filter.mp hr
    have hx:=hraw r hr'.1 hr'.2
    have hm:=hradius r hr'.1 hr'.2
    have hb : 0≤bound:=hscale.trans (le_max_left _ _)
    fin_cases i
    · change -bound≤length Z (X₁ r) ∧ length Z (X₁ r)≤bound
      exact ⟨by linarith [length_nonneg Z (X₁ r) hZ],
        (raw_length_cap Z (X₁ r) Bscale₀ hZ hscale hx.1).trans (le_max_left _ _)⟩
    · change -bound≤length Z (X₂ r) ∧ length Z (X₂ r)≤bound
      exact ⟨by linarith [length_nonneg Z (X₂ r) hZ],
        (raw_length_cap Z (X₂ r) Bscale₀ hZ hscale hx.2).trans (le_max_left _ _)⟩
    · change -bound≤radius r ∧ radius r≤bound
      exact ⟨by linarith,hm.2.trans (le_max_right _ _)⟩
  have hcard : cells.card≤2^N*Kbox := by
    calc
      cells.card=∑F∈T.powerset,((live.filter (fun r=>select r=F)).image tag).card :=
        Finset.card_sigma _ _
      _≤∑_F∈T.powerset,Kbox := by
        apply Finset.sum_le_sum
        intro F _
        exact scale_keys_card (live.filter (fun r=>select r=F)) X₁ X₂ radius Z width bound hwidth
          (fun r hr=>hbox r (Finset.mem_filter.mp hr).1)
      _=2^T.card*Kbox := by simp
      _≤2^N*Kbox:=Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hTN)
  have hcap (i : (F : Finset Slot)×(Fin 3→ℤ))(hi' : i∈cells) :
      Z^(exponentBinUpper width i.2 0)≤Z^(Bscale₀+width) ∧
        Z^(exponentBinUpper width i.2 1)≤Z^(Bscale₀+width) := by
    obtain ⟨_,hk⟩:=Finset.mem_sigma.mp hi'
    obtain ⟨r,hr,hk⟩:=Finset.mem_image.mp hk
    have hn:=Finset.mem_filter.mp (Finset.mem_filter.mp hr).1
    have he:=same_key_enclosure width Z (X₁ r) (X₂ r) (radius r) hwidth i.2 hk
    have hx:=hraw r hn.1 hn.2
    exact ⟨Real.rpow_le_rpow_of_exponent_le hZ.le
        (by linarith only [he.2.1,raw_length_cap Z (X₁ r) Bscale₀ hZ hscale hx.1]),
      Real.rpow_le_rpow_of_exponent_le hZ.le
        (by linarith only [he.2.2.2.1,raw_length_cap Z (X₂ r) Bscale₀ hZ hscale hx.2])⟩
  have hs:=hz.2 ((F : Finset Slot)×(Fin 3→ℤ)) cells hcard p t height εsource loss factor Cslot
    (target+massLoss+width+gapH+εmask*Bmissing+2*εlow*d*N-γ*lo) N
    hheight hfactor (by linarith) R hR hRcap
    (fun i=>radial width Mmax i.2) (fun i=>Z^(exponentBinUpper width i.2 0))
    (fun i=>Z^(exponentBinUpper width i.2 1)) (fun i=>A i.1 i.2)
    (fun i=>erasurePayment Z q (Cslot*Z^(2*εlow*d)) w T i.1)
    (fun _=>hi*(1+εmask)-γ*lo)
    (fun i hi'=>(hcap i hi').1) (fun i hi'=>(hcap i hi').2)
    (fun i _=>hA i.1 i.2) (by intro i _;unfold erasurePayment;positivity)
    (by intro i _;convert hpaid i.1 i.2 using 1 <;> ring)
  have he:=Finset.sum_sigma' T.powerset
    (fun F=>(live.filter (fun r=>select r=F)).image tag)
    (fun F k=>cellBudget rayCount a b ha TP CP DP Craw degreeP Φ p
      Z t height εsource loss δ Brestore εmask R (radial width Mmax k)
      (Z^(exponentBinUpper width k 0)) (Z^(exponentBinUpper width k 1)) (A F k)
      (erasurePayment Z q (Cslot*Z^(2*εlow*d)) w T F) (hi*(1+εmask)-γ*lo))
  exact he.trans_le hs

end
end QRH.Record1252270103Source.Admission.RetainedLow
#print axioms QRH.Record1252270103Source.Admission.RetainedLow.raw_length_cap
#print axioms QRH.Record1252270103Source.Admission.RetainedLow.paid_cell_budgets
