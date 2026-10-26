/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Geometry of actual selected seed-one children, preserving original slot images. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalForcedDictionary
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.FirstFamilySingletons
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.ForcedCost.CenteredScale
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedForcedGeometry
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAddedZeroUniform CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput CenteredMomentSecondHeightFamily
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentEnergyReindex
open Record1252270103Second Record1252270103Source
open High.GlobalPhysical JointForced QRH.Record1252270103Low ConcretePrimeRowBridge
open CenteredMomentAmplificationChildSourceCaps
local notation "O"=>ActualEisensteinCubic.O
variable {ι α J:Type*} [Fintype ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

/-- All four raw corners contract under the actual ordinary divisor norms. -/
theorem child_raw_le (s:Input ι) (C R:Ideal O) (B:actualAllocations s.pools C)
    (τ:Character) (t:ℝ) :
    (child s C R B τ t).X₁≤s.X₁ ∧ (child s C R B τ t).X₂≤s.X₂ ∧
    (child s C R B τ t).Y₁≤s.Y₁ ∧ (child s C R B τ t).Y₂≤s.Y₂ :=
  ⟨div_le_self s.X₁_pos.le (ForcedCost.alloc_norm_ge_one s C B _),
    div_le_self s.X₂_pos.le (ForcedCost.alloc_norm_ge_one s C B _),
    div_le_self s.Y₁_pos.le (ForcedCost.alloc_norm_ge_one s C B _),
    div_le_self s.Y₂_pos.le (ForcedCost.alloc_norm_ge_one s C B _)⟩

/-- True parent caps transport without rounding or changing either corner. -/
theorem child_raw_caps (s:Input ι) (C R:Ideal O) (B:actualAllocations s.pools C)
    (τ:Character) (t U₁ U₂ V₁ V₂:ℝ)
    (hX₁:s.X₁≤U₁) (hX₂:s.X₂≤U₂) (hY₁:s.Y₁≤V₁) (hY₂:s.Y₂≤V₂) :
    (child s C R B τ t).X₁≤U₁ ∧ (child s C R B τ t).X₂≤U₂ ∧
    (child s C R B τ t).Y₁≤V₁ ∧ (child s C R B τ t).Y₂≤V₂ := by
  obtain ⟨h₁,h₂,h₃,h₄⟩:=child_raw_le s C R B τ t
  exact ⟨h₁.trans hX₁,h₂.trans hX₂,h₃.trans hY₁,h₄.trans hY₂⟩

/-- The logarithmic upper widths follow the actual positive raw corners. -/
theorem child_log_width_le (s:Input ι) (C R:Ideal O) (B:actualAllocations s.pools C)
    (τ:Character) (t Z:ℝ) (hZ:1<Z) :
    Real.logb Z (child s C R B τ t).X₁≤Real.logb Z s.X₁ ∧
    Real.logb Z (child s C R B τ t).X₂≤Real.logb Z s.X₂ ∧
    Real.logb Z (child s C R B τ t).Y₁≤Real.logb Z s.Y₁ ∧
    Real.logb Z (child s C R B τ t).Y₂≤Real.logb Z s.Y₂ := by
  obtain ⟨h₁,h₂,h₃,h₄⟩:=child_raw_le s C R B τ t
  exact ⟨Real.logb_le_logb_of_le hZ (child s C R B τ t).X₁_pos h₁,
    Real.logb_le_logb_of_le hZ (child s C R B τ t).X₂_pos h₂,
    Real.logb_le_logb_of_le hZ (child s C R B τ t).Y₁_pos h₃,
    Real.logb_le_logb_of_le hZ (child s C R B τ t).Y₂_pos h₄⟩

/-- Profile functions and caps are inherited exactly; the row character,
height and puncture are the actual chosen child parameters. -/
theorem child_fields (s:Input ι) (C R:Ideal O) (B:actualAllocations s.pools C)
    (τ:Character) (t:ℝ) :
    (child s C R B τ t).W₁=s.W₁ ∧ (child s C R B τ t).W₂=s.W₂ ∧
    (child s C R B τ t).b₁=s.b₁ ∧ (child s C R B τ t).b₂=s.b₂ ∧
    (child s C R B τ t).lower=s.lower ∧ (child s C R B τ t).upper=s.upper ∧
    (child s C R B τ t).η=τ ∧ (child s C R B τ t).t=t ∧
    (child s C R B τ t).m=fixedBadMask*idealGenerator (R*C) ∧
    (child s C R B τ t).A=1 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem child_card_cap (s:Input ι) (C R:Ideal O) (B:actualAllocations s.pools C)
    (N:ℕ) (hN:Fintype.card ι≤N) : Fintype.card (liveIndices B.val)≤N :=
  (live_card_le B.val).trans hN

/-- Arbitrary full singleton subfamilies of the selected child are exact
image subsets of the original ambient family through its existing embedding. -/
theorem inherited_full_slots_image [Fintype α] [Fintype J]
    (s:Input ι) (C R:Ideal O) (B:actualAllocations s.pools C) (τ:Character) (t:ℝ)
    (f:ι↪α) (slots:α→Finset (Ideal O)) (coeff:α→Ideal O→ℂ) (scale:α→ℝ)
    (hs:∀i,s.slots i=slots (f i)) (hc:∀i,restoredSlotCoeff s i=coeff (f i))
    (hp:∀i,s.P i=scale (f i)) (g:J↪liveIndices B.val)
    (η:Character) (m A z:O) (height:ℝ) :
    (∏j,normalizedSlot η m A z ((child s C R B τ t).slots (g j))
      (restoredSlotCoeff (child s C R B τ t) (g j)) height ((child s C R B τ t).P (g j)))=
      ∏i:slotRange (g.trans (inheritedSlotEmbedding B.val f)),
        normalizedSlot η m A z (slots i) (coeff i) height (scale i) := by
  obtain ⟨hs',hc',hp'⟩:=inherited_slot_fields s C R B τ t f slots coeff scale hs hc hp
  simp_rw [hs',hc',hp']
  exact FirstFamily.full_slots_image η m A z height slots coeff scale
    (g.trans (inheritedSlotEmbedding B.val f))

/-- Explicit original-image dictionary after two earlier common allocations
and the selected forced allocation. No ordinary active source is involved. -/
theorem third_child_full_slots_image [Fintype J]
    (s:Input ι) (C R:Ideal O) (B:actualAllocations s.pools C) (τ:Character) (t:ℝ)
    (D:Ideal O) (E:actualAllocations (child s C R B τ t).pools D) (ψ:Character) (v:ℝ)
    (Q:Ideal O) (H:actualAllocations (child (child s C R B τ t) D (R*C) E ψ v).pools Q)
    (χ:Character) (w:ℝ) (f:J↪liveIndices H.val) (η:Character) (m A z:O) (height:ℝ) :
    (∏j,normalizedSlot η m A z
      ((child (child (child s C R B τ t) D (R*C) E ψ v) Q ((R*C)*D) H χ w).slots (f j))
      (restoredSlotCoeff (child (child (child s C R B τ t) D (R*C) E ψ v) Q ((R*C)*D) H χ w) (f j))
      height ((child (child (child s C R B τ t) D (R*C) E ψ v) Q ((R*C)*D) H χ w).P (f j)))=
      ∏i:slotRange (FirstFamily.childEmbedding B.val
        (FirstFamily.childEmbedding E.val (FirstFamily.childEmbedding H.val f))),
        normalizedSlot η m A z (s.slots i) (restoredSlotCoeff s i) height (s.P i) :=
  FirstFamily.full_slots_image η m A z height s.slots (restoredSlotCoeff s) s.P
    (FirstFamily.childEmbedding B.val (FirstFamily.childEmbedding E.val (FirstFamily.childEmbedding H.val f)))

theorem third_child_card_cap (s:Input ι) (C R:Ideal O) (B:actualAllocations s.pools C)
    (τ:Character) (t:ℝ) (D:Ideal O)
    (E:actualAllocations (child s C R B τ t).pools D) (ψ:Character) (v:ℝ)
    (Q:Ideal O) (H:actualAllocations (child (child s C R B τ t) D (R*C) E ψ v).pools Q)
    (N:ℕ) (hN:Fintype.card ι≤N) : Fintype.card (liveIndices H.val)≤N :=
  (live_card_le H.val).trans ((live_card_le E.val).trans ((live_card_le B.val).trans hN))

/-- Selection changes child data, not the original encoded row. Restricting
the original injective key to the nonzero mother rows preserves injectivity. -/
theorem nonzero_rows_key_injective {Row Key:Type*} (rows:Finset Row)
    (κ:Row→Type*) [∀u,Fintype (κ u)] (s:∀u,Input (κ u))
    (modifier:∀u,Tuple (κ u)→ℂ) (R L:Row→Ideal O)
    (τ:Row→Character) (t:Row→ℝ) (z:Row→O) (key:Row→Key)
    (hkey:Set.InjOn key (rows:Set Row)) :
    Function.Injective (fun u:nonzeroRows rows κ s modifier R L τ t z=>key u.val) := by
  intro u v h
  apply Subtype.ext
  exact hkey (Finset.mem_filter.mp u.property).1 (Finset.mem_filter.mp v.property).1 h

end
end QRH.Record1252270103Source.Admission.SelectedForcedGeometry
#print axioms QRH.Record1252270103Source.Admission.SelectedForcedGeometry.child_raw_le
#print axioms QRH.Record1252270103Source.Admission.SelectedForcedGeometry.inherited_full_slots_image
#print axioms QRH.Record1252270103Source.Admission.SelectedForcedGeometry.third_child_full_slots_image
#print axioms QRH.Record1252270103Source.Admission.SelectedForcedGeometry.nonzero_rows_key_injective
