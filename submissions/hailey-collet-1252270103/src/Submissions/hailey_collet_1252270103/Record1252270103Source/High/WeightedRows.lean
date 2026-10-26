/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Complete actual amplitude-bin and same-zero dyadic-fiber weighted count. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.WeightedFiber
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
open HeckeDetectorPhysicalSelection HeckeDetectorRowwisePolynomial
open HeckeDetectorFiberPartition HeckeDetectorDyadicProfiles HeckeDetectorInverseFiberCount
variable {Row Label Slot : Type*} [Fintype Label]
variable (B lam h : ℝ)
def binCutoff (slots : Finset Slot) (widths : Slot→ℝ) (a binWidth : ℝ)
    (_bin : BinLabel slots ((2*a-1)/2) binWidth) : ℝ := cutoff (2*a-1) B lam h (∑s∈slots,widths s) 1

def adaptiveKey (slots : Finset Slot) (widths : Slot → ℝ)
    (Q : Row → Slot → ℂ) (χ : Row → Label → Character)
    (U a ε T allowance binWidth : ℝ) (i : ℕ) (hbin : 0 < binWidth)
    (witness : ∀ bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness (χ u) U a ε (binCutoff B lam h slots widths a binWidth bin) T allowance i)
    (u : Row) : BinLabel slots ((2*a-1)/2) binWidth × Label ×
        Fin (dyadicLength U) × Fin (dyadicLength U) :=
  let b := amplitudeLabel slots U ((2*a-1)/2) binWidth hbin widths Q u
  (b,(witness b u).label,(witness b u).left,(witness b u).right)

def adaptiveFiber (rows : Finset Row) (slots : Finset Slot) (widths : Slot → ℝ)
    (Q : Row → Slot → ℂ) (χ : Row → Label → Character)
    (U a ε T allowance binWidth : ℝ) (i : ℕ) (hbin : 0 < binWidth)
    (witness : ∀ bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness (χ u) U a ε (binCutoff B lam h slots widths a binWidth bin) T allowance i)
    (bin : BinLabel slots ((2*a-1)/2) binWidth) (j : Label)
    (J K : Fin (dyadicLength U)) : Finset Row :=
  rows.filter (fun u => adaptiveKey B lam h slots widths Q χ U a ε T allowance binWidth i hbin witness u =
    (bin,j,J,K))

theorem adaptiveFiber_fields
    (rows : Finset Row) (slots : Finset Slot) (widths : Slot → ℝ)
    (Q : Row → Slot → ℂ) (χ : Row → Label → Character)
    (U a ε T allowance binWidth : ℝ) (i : ℕ) (hbin : 0 < binWidth)
    (witness : ∀ bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness (χ u) U a ε (binCutoff B lam h slots widths a binWidth bin) T allowance i)
    (bin : BinLabel slots ((2*a-1)/2) binWidth) (j : Label)
    (J K : Fin (dyadicLength U)) (u : Row)
    (hu : u ∈ adaptiveFiber B lam h rows slots widths Q χ U a ε T allowance binWidth i hbin witness bin j J K) :
    u ∈ rows ∧ (witness bin u).label=j ∧ (witness bin u).left=J ∧
      (witness bin u).right=K ∧ ∀s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth (Q u s) =
        binValue slots ((2*a-1)/2) binWidth bin s := by
  obtain ⟨hrow,hkey⟩ := Finset.mem_filter.mp hu
  have hb : amplitudeLabel slots U ((2*a-1)/2) binWidth hbin widths Q u = bin :=
    congrArg Prod.fst hkey
  have hw : (witness bin u).label=j ∧ (witness bin u).left=J ∧ (witness bin u).right=K := by
    dsimp [adaptiveKey] at hkey
    rw [hb] at hkey
    simpa only [Prod.mk.injEq,true_and] using hkey
  refine ⟨hrow,hw.1,hw.2.1,hw.2.2,?_⟩
  intro s hs
  have hv := congrArg (fun b : BinLabel slots ((2*a-1)/2) binWidth => (b ⟨s,hs⟩).val) hb
  simpa only [amplitudeLabel,binValue,dite_eq_left hs] using hv

theorem adaptive_fiber_sum (rows : Finset Row) (slots : Finset Slot) (widths : Slot → ℝ)
    (Q : Row → Slot → ℂ) (χ : Row → Label → Character)
    (U a ε T allowance binWidth : ℝ) (i : ℕ) (hbin : 0 < binWidth)
    (witness : ∀ bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness (χ u) U a ε (binCutoff B lam h slots widths a binWidth bin) T allowance i)
    (f : Row → ℝ) :
    (∑u∈rows,f u) = ∑bin,∑j,∑J,∑K,
      ∑u∈adaptiveFiber B lam h rows slots widths Q χ U a ε T allowance binWidth i hbin witness bin j J K,f u := by
  have hh := Finset.sum_fiberwise_of_maps_to (s:=rows) (t:=Finset.univ)
    (g:=adaptiveKey B lam h slots widths Q χ U a ε T allowance binWidth i hbin witness)
    (f:=f) (by intro u hu; exact Finset.mem_univ _)
  simpa only [Fintype.sum_prod_type,adaptiveFiber] using hh.symm

theorem weighted_row_sum
    (hB0 : 22/23≤B) (hB1 : B≤1) (hlam : 1<lam) (hh0 : 0≤h) (hh1 : h<1)
    (rows : Finset Row) (slots : Finset Slot)
    (χ : Row→Label→Character) (Q : Row→Slot→ℂ) (widths : Slot→ℝ)
    (U a ε T allowance mesh binWidth ζ εm C height : ℝ)
    (i : ℕ) (hU : 1<U) (ha0 : 1/2≤2*a-1) (ha : 2*a-1≤3/4)
    (hε : 0≤ε) (hε1 : ε≤1/100) (hmesh : 0≤mesh) (hbin : 0<binWidth)
    (hζ : 0<ζ) (hC : 0<C) (hheight : 0≤height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hw : ∀s∈slots,0<widths s) (hwm : ∀s∈slots,widths s≤mesh)
    (hL : 0≤∑s∈slots,widths s)
    (witness : ∀bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness (χ u) U a ε (binCutoff B lam h slots widths a binWidth bin) T allowance i)
    (hQ : ∀u∈rows,∀s∈slots,‖Q u s‖≤(U^(widths s))^((2*a-1)/2+binWidth))
    (hmom : ∀bin j J K,OrdinaryFiberMoments
      (adaptiveFiber B lam h rows slots widths Q χ U a ε T allowance binWidth i hbin witness bin j J K)
      slots χ Q widths U a ε (binCutoff B lam h slots widths a binWidth bin)
        B lam h εm C height j J K) :
    (∑u∈rows,‖∏s∈slots,Q u s‖^2) ≤
      ((Fintype.card (BinLabel slots ((2*a-1)/2) binWidth) : ℝ)*
        Fintype.card Label*(dyadicLength U : ℝ)^2*(192*(1+height)*C))*
      U^(rho (2*a-1)+(2*a-1)*(∑s∈slots,widths s)-gain (2*a-1) B lam h (∑s∈slots,widths s) 1+
        155*ε+mesh+εm+(2*a-1)*ζ+2*binWidth*(∑s∈slots,widths s)) := by
  let A := 192*(1+height)*C
  let E := rho (2*a-1)+(2*a-1)*(∑s∈slots,widths s)-gain (2*a-1) B lam h (∑s∈slots,widths s) 1+
    155*ε+mesh+εm+(2*a-1)*ζ+2*binWidth*(∑s∈slots,widths s)
  have hf (bin : BinLabel slots ((2*a-1)/2) binWidth) (j : Label)
      (J K : Fin (dyadicLength U)) :
      (∑u∈adaptiveFiber B lam h rows slots widths Q χ U a ε T allowance binWidth i hbin witness bin j J K,
        ‖∏s∈slots,Q u s‖^2)≤A*U^E := by
    let F := adaptiveFiber B lam h rows slots widths Q χ U a ε T allowance binWidth i hbin witness bin j J K
    by_cases hne : F.Nonempty
    · have hfields (u : Row) (hu : u∈F) := adaptiveFiber_fields B lam h rows slots widths Q χ U a ε
        T allowance binWidth i hbin witness bin j J K u hu
      have hc := feedback_fiber_count F hne slots χ Q widths
        (binValue slots ((2*a-1)/2) binWidth bin) U a ε T allowance mesh binWidth ζ εm C height B lam h hB0 hB1 hlam hh0 hh1
        i hU ha0 ha hε hε1 hmesh hbin hζ hC hheight hfreq hw hwm hL
        (witness bin) j J K (fun u hu=>(hfields u hu).2.1)
        (fun u hu=>(hfields u hu).2.2.1) (fun u hu=>(hfields u hu).2.2.2.1)
        (fun u hu=>(hfields u hu).2.2.2.2) (hmom bin j J K)
      have hh := weighted_bound_of_card F slots Q widths
        (binValue slots ((2*a-1)/2) binWidth bin) U (2*a-1) binWidth A
        (155*ε+mesh+εm+(2*a-1)*ζ) B lam h hU hbin hw hL
        (fun u hu=>(hfields u hu).2.2.2.2)
        (fun u hu=>hQ u (hfields u hu).1) (by simpa only [A,add_assoc] using hc)
      convert hh using 1 <;> dsimp [E] <;> congr 2 <;> ring
    · have he : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      change (∑u∈F,_)≤_
      rw [he,Finset.sum_empty]
      dsimp [A]
      positivity
  rw [adaptive_fiber_sum B lam h rows slots widths Q χ U a ε T allowance binWidth i hbin witness]
  calc
    _ ≤ ∑bin : BinLabel slots ((2*a-1)/2) binWidth,∑j : Label,
        ∑J : Fin (dyadicLength U),∑K : Fin (dyadicLength U),A*U^E := by
      exact Finset.sum_le_sum (fun bin _=>Finset.sum_le_sum (fun j _=>
        Finset.sum_le_sum (fun J _=>Finset.sum_le_sum (fun K _=>hf bin j J K))))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; dsimp [A]; ring

end
end QRH.Record1252270103Source.High
#print axioms QRH.Record1252270103Source.High.weighted_row_sum
