/- Repeated marks: the complete amplitude-bin and same-zero dyadic-fiber weighted count with one
detector cutoff per amplitude bin. Fork of Collet's High/WeightedFiber.lean and
High/WeightedRows.lean (Apache-2.0): the bin cutoff is the cutoff of the bin's amplitude class,
the fiber moments include the replicated inverse moment, and the gain is `gainRep copies`. -/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.FiberK
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.WeightedRows
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace QRH.RepeatedMarks.Source
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
open HeckeDetectorPhysicalSelection HeckeDetectorRowwisePolynomial
open HeckeDetectorFiberPartition HeckeDetectorDyadicProfiles HeckeDetectorInverseFiberCount
open QRH.Record1252270103Source.High
variable {Row Label Slot : Type*} [Fintype Label]

theorem weighted_bound_of_card_K (copies : ℕ)
    (rows : Finset Row) (slots : Finset Slot) (Q : Row→Slot→ℂ) (widths g : Slot→ℝ)
    (U ν binWidth A loss B lam h : ℝ) (hU : 1<U) (hbin : 0<binWidth)
    (hw : ∀s∈slots,0<widths s) (hL : 0≤∑s∈slots,widths s)
    (hbins : ∀u∈rows,∀s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) (ν/2) binWidth (Q u s)=g s)
    (hQ : ∀u∈rows,∀s∈slots,‖Q u s‖≤(U^(widths s))^(ν/2+binWidth))
    (hcard : (rows.card : ℝ)≤A*U^(rho ν+ν*(∑s∈slots,widths s)-
      gainRep copies ν B lam h (∑s∈slots,widths s) 1-
      2*weightedMean slots widths g*(∑s∈slots,widths s)+loss)) :
    (∑u∈rows,‖∏s∈slots,Q u s‖^2) ≤ A*
      U^(rho ν+ν*(∑s∈slots,widths s)-gainRep copies ν B lam h (∑s∈slots,widths s) 1+
        loss+2*binWidth*(∑s∈slots,widths s)) := by
  let S := ∑s∈slots,widths s
  let q := weightedMean slots widths g
  have hmeanS : q*S=∑s∈slots,widths s*g s := by
    by_cases hLp : 0<∑s∈slots,widths s
    · exact div_mul_cancel₀ _ hLp.ne'
    · have hzero : (∑s∈slots,widths s)=0 := by linarith
      have hempty := slots_empty_of_width_sum_zero slots widths hw hzero
      subst slots
      simp [S,q]
  have hprod (u : Row) (hu : u∈rows) : ‖∏s∈slots,Q u s‖^2≤U^(2*q*S+2*binWidth*S) := by
    have hh := HeckePrimeAmplitudeBins.product_upper slots widths (Q u) U (ν/2) binWidth
      hU hbin hw (hQ u hu)
    have hg : (∑s∈slots,widths s*HeckePrimeAmplitudeBins.amplitude
        (U^(widths s)) (ν/2) binWidth (Q u s))=∑s∈slots,widths s*g s :=
      Finset.sum_congr rfl (fun s hs=>by rw [hbins u hu s hs])
    rw [hg,←hmeanS] at hh
    have hh' := (sq_le_sq₀ (norm_nonneg _) (Real.rpow_nonneg (by linarith) _)).mpr hh
    convert hh' using 1
    rw [←Real.rpow_natCast,←Real.rpow_mul (by linarith : (0:ℝ)≤U)]
    congr 1
    ring
  calc
    _ ≤ ∑u∈rows,U^(2*q*S+2*binWidth*S) := Finset.sum_le_sum hprod
    _ = (rows.card : ℝ)*U^(2*q*S+2*binWidth*S) := by simp
    _ ≤ (A*U^(rho ν+ν*S-gainRep copies ν B lam h S 1-2*q*S+loss))*U^(2*q*S+2*binWidth*S) :=
      mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg (by linarith) _)
    _ = _ := by rw [mul_assoc,←Real.rpow_add (by linarith : 0<U)]; congr 1; congr 1; ring

variable (copies : ℕ) (B lam h : ℝ)

/-- The detector cutoff of an amplitude bin: the cutoff of its amplitude class. -/
def binCutoffK (slots : Finset Slot) (widths : Slot→ℝ) (a binWidth : ℝ)
    (bin : BinLabel slots ((2*a-1)/2) binWidth) : ℝ :=
  classCutoff slots widths (binValue slots ((2*a-1)/2) binWidth bin) copies (2*a-1) B lam h

def adaptiveKeyK (slots : Finset Slot) (widths : Slot → ℝ)
    (Q : Row → Slot → ℂ) (χ : Row → Label → Character)
    (U a ε T allowance binWidth : ℝ) (i : ℕ) (hbin : 0 < binWidth)
    (witness : ∀ bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness (χ u) U a ε (binCutoffK copies B lam h slots widths a binWidth bin)
        T allowance i)
    (u : Row) : BinLabel slots ((2*a-1)/2) binWidth × Label ×
        Fin (dyadicLength U) × Fin (dyadicLength U) :=
  let b := amplitudeLabel slots U ((2*a-1)/2) binWidth hbin widths Q u
  (b,(witness b u).label,(witness b u).left,(witness b u).right)

def adaptiveFiberK (rows : Finset Row) (slots : Finset Slot) (widths : Slot → ℝ)
    (Q : Row → Slot → ℂ) (χ : Row → Label → Character)
    (U a ε T allowance binWidth : ℝ) (i : ℕ) (hbin : 0 < binWidth)
    (witness : ∀ bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness (χ u) U a ε (binCutoffK copies B lam h slots widths a binWidth bin)
        T allowance i)
    (bin : BinLabel slots ((2*a-1)/2) binWidth) (j : Label)
    (J K : Fin (dyadicLength U)) : Finset Row :=
  rows.filter (fun u => adaptiveKeyK copies B lam h slots widths Q χ U a ε T allowance binWidth i
    hbin witness u = (bin,j,J,K))

theorem adaptiveFiberK_fields
    (rows : Finset Row) (slots : Finset Slot) (widths : Slot → ℝ)
    (Q : Row → Slot → ℂ) (χ : Row → Label → Character)
    (U a ε T allowance binWidth : ℝ) (i : ℕ) (hbin : 0 < binWidth)
    (witness : ∀ bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness (χ u) U a ε (binCutoffK copies B lam h slots widths a binWidth bin)
        T allowance i)
    (bin : BinLabel slots ((2*a-1)/2) binWidth) (j : Label)
    (J K : Fin (dyadicLength U)) (u : Row)
    (hu : u ∈ adaptiveFiberK copies B lam h rows slots widths Q χ U a ε T allowance binWidth i
      hbin witness bin j J K) :
    u ∈ rows ∧ (witness bin u).label=j ∧ (witness bin u).left=J ∧
      (witness bin u).right=K ∧ ∀s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth (Q u s) =
        binValue slots ((2*a-1)/2) binWidth bin s := by
  obtain ⟨hrow,hkey⟩ := Finset.mem_filter.mp hu
  have hb : amplitudeLabel slots U ((2*a-1)/2) binWidth hbin widths Q u = bin :=
    congrArg Prod.fst hkey
  have hw : (witness bin u).label=j ∧ (witness bin u).left=J ∧ (witness bin u).right=K := by
    dsimp [adaptiveKeyK] at hkey
    rw [hb] at hkey
    simpa only [Prod.mk.injEq,true_and] using hkey
  refine ⟨hrow,hw.1,hw.2.1,hw.2.2,?_⟩
  intro s hs
  have hv := congrArg (fun b : BinLabel slots ((2*a-1)/2) binWidth => (b ⟨s,hs⟩).val) hb
  simpa only [amplitudeLabel,binValue,dite_eq_left hs] using hv

theorem adaptive_fiber_sum_K (rows : Finset Row) (slots : Finset Slot) (widths : Slot → ℝ)
    (Q : Row → Slot → ℂ) (χ : Row → Label → Character)
    (U a ε T allowance binWidth : ℝ) (i : ℕ) (hbin : 0 < binWidth)
    (witness : ∀ bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness (χ u) U a ε (binCutoffK copies B lam h slots widths a binWidth bin)
        T allowance i)
    (f : Row → ℝ) :
    (∑u∈rows,f u) = ∑bin,∑j,∑J,∑K,
      ∑u∈adaptiveFiberK copies B lam h rows slots widths Q χ U a ε T allowance binWidth i hbin
        witness bin j J K,f u := by
  have hh := Finset.sum_fiberwise_of_maps_to (s:=rows) (t:=Finset.univ)
    (g:=adaptiveKeyK copies B lam h slots widths Q χ U a ε T allowance binWidth i hbin witness)
    (f:=f) (by intro u hu; exact Finset.mem_univ _)
  simpa only [Fintype.sum_prod_type,adaptiveFiberK] using hh.symm

theorem weighted_row_sum_K (hcopies : 1 ≤ copies)
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
      ∀u,SupportedWitness (χ u) U a ε (binCutoffK copies B lam h slots widths a binWidth bin)
        T allowance i)
    (hQ : ∀u∈rows,∀s∈slots,‖Q u s‖≤(U^(widths s))^((2*a-1)/2+binWidth))
    (hmom : ∀bin j J K,FiberMomentsK
      (adaptiveFiberK copies B lam h rows slots widths Q χ U a ε T allowance binWidth i hbin
        witness bin j J K)
      slots copies χ Q widths U a ε (binCutoffK copies B lam h slots widths a binWidth bin)
        B lam h εm C height j J K) :
    (∑u∈rows,‖∏s∈slots,Q u s‖^2) ≤
      ((Fintype.card (BinLabel slots ((2*a-1)/2) binWidth) : ℝ)*
        Fintype.card Label*(dyadicLength U : ℝ)^2*(192*(1+height)*C))*
      U^(rho (2*a-1)+(2*a-1)*(∑s∈slots,widths s)-
        gainRep copies (2*a-1) B lam h (∑s∈slots,widths s) 1+
        155*ε+mesh+εm+(2*a-1)*ζ+2*binWidth*(∑s∈slots,widths s)) := by
  let A := 192*(1+height)*C
  let E := rho (2*a-1)+(2*a-1)*(∑s∈slots,widths s)-
    gainRep copies (2*a-1) B lam h (∑s∈slots,widths s) 1+
    155*ε+mesh+εm+(2*a-1)*ζ+2*binWidth*(∑s∈slots,widths s)
  have hf (bin : BinLabel slots ((2*a-1)/2) binWidth) (j : Label)
      (J K : Fin (dyadicLength U)) :
      (∑u∈adaptiveFiberK copies B lam h rows slots widths Q χ U a ε T allowance binWidth i hbin
        witness bin j J K, ‖∏s∈slots,Q u s‖^2)≤A*U^E := by
    let F := adaptiveFiberK copies B lam h rows slots widths Q χ U a ε T allowance binWidth i hbin
      witness bin j J K
    by_cases hne : F.Nonempty
    · have hfields (u : Row) (hu : u∈F) := adaptiveFiberK_fields copies B lam h rows slots widths
        Q χ U a ε T allowance binWidth i hbin witness bin j J K u hu
      have hc := feedback_fiber_count_K F hne slots copies hcopies χ Q widths
        (binValue slots ((2*a-1)/2) binWidth bin) U a ε T allowance mesh binWidth ζ εm C height
        B lam h hB0 hB1 hlam hh0 hh1
        i hU ha0 ha hε hε1 hmesh hbin hζ hC hheight hfreq hw hwm hL
        (witness bin) j J K (fun u hu=>(hfields u hu).2.1)
        (fun u hu=>(hfields u hu).2.2.1) (fun u hu=>(hfields u hu).2.2.2.1)
        (fun u hu=>(hfields u hu).2.2.2.2) (hmom bin j J K)
      have hh := weighted_bound_of_card_K copies F slots Q widths
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
  rw [adaptive_fiber_sum_K copies B lam h rows slots widths Q χ U a ε T allowance binWidth i hbin
    witness]
  calc
    _ ≤ ∑bin : BinLabel slots ((2*a-1)/2) binWidth,∑j : Label,
        ∑J : Fin (dyadicLength U),∑K : Fin (dyadicLength U),A*U^E := by
      exact Finset.sum_le_sum (fun bin _=>Finset.sum_le_sum (fun j _=>
        Finset.sum_le_sum (fun J _=>Finset.sum_le_sum (fun K _=>hf bin j J K))))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; dsimp [A]; ring

end
end QRH.RepeatedMarks.Source
