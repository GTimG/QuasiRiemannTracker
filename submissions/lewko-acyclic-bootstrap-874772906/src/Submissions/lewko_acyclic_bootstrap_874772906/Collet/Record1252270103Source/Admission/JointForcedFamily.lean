/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
One simultaneous heterogeneous family after complete forced-prime extraction.
The allocation constant precedes all live types and moving row data. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.JointForcedSelection
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.JointForced
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAddedZeroUniform CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open Record1252270103Source Record1252270103Second
local notation "O"=>ActualEisensteinCubic.O
universe u v

/-- Exact finite weighted double Cauchy. No summability, energy hypothesis,
or extra count of the original row family is introduced. -/
theorem joint_forced_row_bound {Row:Type v} (rows:Finset Row)
    (ι:Row→Type u) [∀u,Fintype (ι u)] (s:∀u,Input (ι u))
    (modifier:∀u,Tuple (ι u)→ℂ) (R L:Row→Ideal O) (hL:∀u∈rows,L u≠0)
    (τ:Row→Character) (t:Row→ℝ) (z:Row→O) (weight:Row→ℝ)
    (hw:∀u∈rows,0≤weight u) :
    (∑u∈rows,‖normalizedRow (s u) (modifier u) (R u) (L u) (τ u) (t u) (z u)‖^2*weight u)≤
      ∑u∈rows,(((forcedLabels (L u) (forcedSource (s u) (modifier u) (R u) (L u))).card:ℝ)*
        ∑C:forcedLabels (L u) (forcedSource (s u) (modifier u) (R u) (L u)),
          ((actualAllocations (s u).pools (C:Ideal O)).card:ℝ)*
            ∑B:actualAllocations (s u).pools (C:Ideal O),
              (‖frozenCoefficient B C (R u) (s u).ν (s u).W (s u).P‖^2/rawReduction B.val (s u).P)*
                ‖normalizedRow (child (s u) C (R u) B (τ u) (t u))
                  (pulledModifier B (modifier u)) ((R u)*C) 1 (τ u) (t u) (z u)‖^2)*weight u := by
  apply Finset.sum_le_sum
  intro u hu
  exact mul_le_mul_of_nonneg_right
    (normalized_forced_row_bound (s u) (modifier u) (R u) (L u) (hL u hu) (τ u) (t u) (z u)) (hw u hu)

/-- The actual valuation-two support supplies C|L²; the complete L-prime
extraction supplies L|C. A single constant covers every live type below N. -/
theorem uniform_selected_child (N:ℕ) (ε:ℝ) (hε:0<ε) :
    ∃K₀:ℝ,0<K₀ ∧ ∀{ι:Type u} [Fintype ι],Fintype.card ι≤N→
      ∀(s:Input ι) (A₁ A₂ D K R L:Ideal O) (F:Ideal O→ℂ),Squarefree L→
      ∀(τ:Character) (t:ℝ) (z:O),
      normalizedRow s (Collision.markedSourceModifier A₁ A₂ D K F) R L τ t z≠0→
      ∃p:ChildIndex s (Collision.markedSourceModifier A₁ A₂ D K F) R L,
        frozenCoefficient p.2 p.1 R s.ν s.W s.P≠0 ∧
        0<childValue s (Collision.markedSourceModifier A₁ A₂ D K F) R L τ t z p ∧
        L∣(p.1:Ideal O) ∧ (p.1:Ideal O)∣L^2 ∧
        ‖normalizedRow s (Collision.markedSourceModifier A₁ A₂ D K F) R L τ t z‖^2≤
          K₀*(L.absNorm:ℝ)^ε*forcedProfileCost s/(L.absNorm:ℝ)*
            childValue s (Collision.markedSourceModifier A₁ A₂ D K F) R L τ t z p := by
  obtain ⟨K₀,hK₀,hmass⟩:=Record1252270103Second.marked_forced_allocation_mass_uniform N ε hε
  refine ⟨K₀,hK₀,?_⟩
  intro ι inst hcard s A₁ A₂ D K R L F hL τ t z hn
  obtain ⟨p,hp,hpos,hbound⟩:=selected_child s (Collision.markedSourceModifier A₁ A₂ D K F)
    R L hL.ne_zero τ t z hn
  refine ⟨p,hp,hpos,forcedSource_label_seed s _ R L hL.ne_zero p.1,
    marked_forced_label_dvd_square s A₁ A₂ D K R L F hL p.1,?_⟩
  apply hbound.trans
  have h:=div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hmass ι hcard s A₁ A₂ D K R L F hL)
      (mul_nonneg (forcedProfileCost_nonneg s) hpos.le)) (Nat.cast_nonneg L.absNorm)
  convert h using 1; ring

/-- The retained family is literally a subset of the original finite rows. -/
def nonzeroRows {Row:Type v} (rows:Finset Row)
    (ι:Row→Type u) [∀u,Fintype (ι u)] (s:∀u,Input (ι u))
    (modifier:∀u,Tuple (ι u)→ℂ) (R L:Row→Ideal O)
    (τ:Row→Character) (t:Row→ℝ) (z:Row→O):Finset Row :=
  rows.filter (fun u=>normalizedRow (s u) (modifier u) (R u) (L u) (τ u) (t u) (z u)≠0)

lemma nonzeroRows_card {Row:Type v} (rows:Finset Row)
    (ι:Row→Type u) [∀u,Fintype (ι u)] (s:∀u,Input (ι u))
    (modifier:∀u,Tuple (ι u)→ℂ) (R L:Row→Ideal O)
    (τ:Row→Character) (t:Row→ℝ) (z:Row→O) :
    (nonzeroRows rows ι s modifier R L τ t z).card≤rows.card := Finset.card_filter_le ..

/-- Simultaneous selected-child theorem. Moving seeds, ordinary factors,
characters, punctures, scales and correction multipliers remain literal.
The original row weights survive, and no per-child family count is paid. -/
theorem uniform_joint_selected_family (N:ℕ) (ε:ℝ) (hε:0<ε) :
    ∃K₀:ℝ,0<K₀ ∧ ∀{Row:Type v} (rows:Finset Row)
      (ι:Row→Type u) [∀u,Fintype (ι u)] (s:∀u,Input (ι u)),
      (∀u∈rows,Fintype.card (ι u)≤N)→
      ∀(A₁ A₂ D K R L:Row→Ideal O) (F:Row→Ideal O→ℂ),
      (∀u∈rows,Squarefree (L u))→∀(τ:Row→Character) (t:Row→ℝ) (z:Row→O) (weight:Row→ℝ),
      (∀u∈rows,0≤weight u)→
      let modifier:=fun u=>Collision.markedSourceModifier (ι:=ι u) (A₁ u) (A₂ u) (D u) (K u) (F u)
      let live:=nonzeroRows rows ι s modifier R L τ t z
      ∃pick:(u:live)→ChildIndex (s u) (modifier u) (R u) (L u),
        (∀u:live,frozenCoefficient (pick u).2 (pick u).1 (R u) (s u).ν (s u).W (s u).P≠0 ∧
          0<childValue (s u) (modifier u) (R u) (L u) (τ u) (t u) (z u) (pick u) ∧
          L u∣((pick u).1:Ideal O) ∧ ((pick u).1:Ideal O)∣(L u)^2) ∧
        (∑u∈rows,‖normalizedRow (s u) (modifier u) (R u) (L u) (τ u) (t u) (z u)‖^2*weight u)≤
          K₀*∑u:live,((L u).absNorm:ℝ)^ε*forcedProfileCost (s u)/((L u).absNorm:ℝ)*
            childValue (s u) (modifier u) (R u) (L u) (τ u) (t u) (z u) (pick u)*weight u := by
  obtain ⟨K₀,hK₀,hselect⟩:=uniform_selected_child.{u} N ε hε
  refine ⟨K₀,hK₀,?_⟩
  intro Row rows ι inst s hcard A₁ A₂ D K R L F hL τ t z weight hw
  dsimp only
  let modifier:=fun u=>Collision.markedSourceModifier (ι:=ι u) (A₁ u) (A₂ u) (D u) (K u) (F u)
  let live:=nonzeroRows rows ι s modifier R L τ t z
  have hex (u:live) := hselect (hcard u (Finset.mem_filter.mp u.property).1) (s u)
    (A₁ u) (A₂ u) (D u) (K u) (R u) (L u) (F u)
    (hL u (Finset.mem_filter.mp u.property).1) (τ u) (t u) (z u) (Finset.mem_filter.mp u.property).2
  choose pick hp using hex
  refine ⟨pick,fun u=>⟨(hp u).1,(hp u).2.1,(hp u).2.2.1,(hp u).2.2.2.1⟩,?_⟩
  have he:(∑u∈rows,‖normalizedRow (s u) (modifier u) (R u) (L u) (τ u) (t u) (z u)‖^2*weight u)=
      ∑u:live,‖normalizedRow (s u) (modifier u) (R u) (L u) (τ u) (t u) (z u)‖^2*weight u := by
    rw [Finset.sum_coe_sort live (fun u:Row=>
      ‖normalizedRow (s u) (modifier u) (R u) (L u) (τ u) (t u) (z u)‖^2*weight u)]
    simp only [live,nonzeroRows,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro u hu
    by_cases hn:normalizedRow (s u) (modifier u) (R u) (L u) (τ u) (t u) (z u)=0
    · simp [hn]
    · simp [hn]
  change (∑u∈rows,‖normalizedRow (s u) (modifier u) (R u) (L u) (τ u) (t u) (z u)‖^2*weight u)≤_
  rw [he,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u hu
  have h:=mul_le_mul_of_nonneg_right (hp u).2.2.2.2 (hw u (Finset.mem_filter.mp u.property).1)
  convert h using 1; ring

end
end QRH.Record1252270103Source.Admission.JointForced
#print axioms QRH.Record1252270103Source.Admission.JointForced.joint_forced_row_bound
#print axioms QRH.Record1252270103Source.Admission.JointForced.uniform_selected_child
#print axioms QRH.Record1252270103Source.Admission.JointForced.nonzeroRows_card
#print axioms QRH.Record1252270103Source.Admission.JointForced.uniform_joint_selected_family
