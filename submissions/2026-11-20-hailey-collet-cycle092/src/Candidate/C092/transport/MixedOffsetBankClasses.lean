/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact common subclasses of all bank dyads, with unchanged weights. -/
import Candidate.C092.transport.MixedOffsetBankNative
set_option autoImplicit false
namespace QRH.Cycle092.MixedOffsetBank
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification HeckeDyadic HeckeDetectorWitnessRows
open HeckeDetectorSupportedWitness HeckeDetectorFiberPartition

abbrev Descriptor (Label : Type*) (L : ℕ) := Label × (Offset→Fin L) × (Offset→Fin L)

def descriptor {Row Label : Type*} {L : ℕ}
    (label : Row→Label) (left right : Offset→Row→Fin L) (u : Row) : Descriptor Label L :=
  (label u,(fun j=>left j u),fun j=>right j u)

def classRows {Row Label : Type*} {L : ℕ} (rows : Finset Row)
    (label : Row→Label) (left right : Offset→Row→Fin L) (σ : Descriptor Label L) : Finset Row :=
  rows.filter (fun u=>descriptor label left right u=σ)

theorem class_subset {Row Label : Type*} {L : ℕ} (rows : Finset Row)
    (label : Row→Label) (left right : Offset→Row→Fin L) (σ : Descriptor Label L) :
    classRows rows label left right σ⊆rows := Finset.filter_subset _ _

theorem descriptor_count {Label : Type*} [Fintype Label] (L : ℕ) :
    Fintype.card (Descriptor Label L)=Fintype.card Label*(L^65537)*(L^65537) := by
  simp only [Descriptor,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,mul_assoc]

/-- Freezing every offset is a fixed finite descriptor partition; dyadic
factors are retained explicitly rather than hidden as one chosen pair. -/
theorem card_partition {Row Label : Type*} [Fintype Label] {L : ℕ} (rows : Finset Row)
    (label : Row→Label) (left right : Offset→Row→Fin L) :
    rows.card=∑σ : Descriptor Label L,(classRows rows label left right σ).card := by
  simpa only [classRows,Finset.sum_coe_sort] using
    (Finset.card_eq_sum_card_fiberwise (s:=rows) (t:=Finset.univ)
      (f:=descriptor label left right) (by intro u hu;exact Finset.mem_univ _))

/-- Any original row weight is kept literally on each subclass. -/
theorem weighted_partition {Row Label : Type*} [Fintype Label] {L : ℕ} (rows : Finset Row)
    (label : Row→Label) (left right : Offset→Row→Fin L) (weight : Row→ℝ) :
    (∑u∈rows,weight u)=∑σ : Descriptor Label L,∑u∈classRows rows label left right σ,weight u := by
  symm
  exact Finset.sum_fiberwise_of_maps_to (g:=descriptor label left right)
    (fun u hu=>Finset.mem_univ _) weight

theorem class_fields {Row Label : Type*} {L : ℕ} (rows : Finset Row)
    (label : Row→Label) (left right : Offset→Row→Fin L) (σ : Descriptor Label L)
    (u : Row) (hu : u∈classRows rows label left right σ) :
    label u=σ.1 ∧ (∀j,left j u=σ.2.1 j) ∧ ∀j,right j u=σ.2.2 j := by
  have he: descriptor label left right u=σ := (Finset.mem_filter.mp hu).2
  exact ⟨congrArg Prod.fst he,fun j=>congrArg (fun t:Descriptor Label L=>t.2.1 j) he,
    fun j=>congrArg (fun t:Descriptor Label L=>t.2.2 j) he⟩

/-- Every common subclass lies inside the actual native fiber at every
cutoff. Hence separate source-count upper bounds all bound this ONE set. -/
theorem class_subset_fiber {Row Label Slot : Type*} [Fintype Label]
    (rows : Finset Row) (χ : Row→Label→Character) (U a ε t₀ γ T allowance : ℝ) (i : ℕ)
    (w : ∀j : Offset,∀u,SupportedWitness (χ u) U a ε (cutoff t₀ γ j) T allowance i)
    (label : Row→Label) (hlabel : ∀j u,u∈rows → (w j u).label=label u)
    (slots : Finset Slot) (mesh : ℝ) (hm : 0 < mesh) (widths : Slot→ℝ) (physical : Row→Slot→ℂ)
    (bin : BinLabel slots ((2*a-1)/2) mesh)
    (hamp : ∀u∈rows,amplitudeLabel slots U ((2*a-1)/2) mesh hm widths physical u=bin)
    (σ : Descriptor Label (dyadicLength U)) (j : Offset) :
    classRows rows label (fun k u=>(w k u).left) (fun k u=>(w k u).right) σ ⊆
      fiber rows χ U a ε (cutoff t₀ γ j) T allowance i (w j) slots mesh hm widths physical
        bin σ.1 (σ.2.1 j) (σ.2.2 j) := by
  intro u hu
  have hmem:=class_subset rows label (fun k u=>(w k u).left) (fun k u=>(w k u).right) σ hu
  have hf:=class_fields rows label (fun k u=>(w k u).left) (fun k u=>(w k u).right) σ u hu
  exact Finset.mem_filter.mpr ⟨hmem,hamp u hmem,(hlabel j u hmem).trans hf.1,hf.2.1 j,hf.2.2 j⟩

/-- This is ordinary monotonicity of ONE finite cardinality, not a product
of count estimates from different offsets. -/
theorem common_count {Row : Type*} (common larger : Finset Row) (hsub : common⊆larger)
    (C U E : ℝ) (hcount : (larger.card:ℝ)≤C*U^E) :
    (common.card:ℝ)≤C*U^E := by
  have h : (common.card:ℝ)≤(larger.card:ℝ) := by exact_mod_cast Finset.card_le_card hsub
  exact h.trans hcount

#print axioms card_partition
#print axioms weighted_partition
#print axioms class_subset_fiber
end
end QRH.Cycle092.MixedOffsetBank
