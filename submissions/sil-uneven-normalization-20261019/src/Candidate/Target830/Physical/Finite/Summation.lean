import Candidate.Target830.Physical.Finite.Cells

/- Original module: Candidate.Target830.Physical.Finite.Geometry. -/
section
/- Private .874836 actual numerator specialization; predecessor attribution retained. Apache-2.0. -/

set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Physical.FiniteNumerator
noncomputable section
open scoped Classical BigOperators
open Filter OAI.SevenEighths ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical
open OAI.SevenEighths.Target830.Physical FinalAssembly Target830PhysicalHighTransport
open OAI.SevenEighths.Target830.Physical.Assembly

/-- All cell geometry is uniform before the live row labels. -/
theorem actual_cell_geometry (A : ChosenData) (η : Character) (τ : ℝ) (n : ℕ) :
    ∀ᶠZ : ℝ in atTop,∀idx grid : FreeRow→ℕ,
      ActualBufferedSelection A.F.modulus ⊤ le_top A.F.S A.F.exclusions A.F.maximal
        η rowPadding A.D.e τ n Z idx grid →
      ∀k i j : ℕ,(cellRows A.D A.F Z idx grid k i j).Nonempty →
        CellFacts A.D A.F η Z τ (cellRows A.D A.F Z idx grid k i j)
          (sourceDyadConductor Z A.D.t k) (51/100+A.D.e*j) i := by
  filter_upwards [sourceDyad_geometry_eventually (1/200) OAI.SevenEighths.Target830.dPlus A.D.t
    (OAI.SevenEighths.Target830.h+rowPadding) (by norm_num) (by norm_num) A.D.t_pos
    (padded_row_cutoff A.D A.P),eventually_gt_atTop (1:ℝ)] with Z hgeo hZ
  intro idx grid hsel k i j hne
  let R := selectedRows A.D A.F Z grid
  let Rij := cellRows A.D A.F Z idx grid k i j
  have hsubk : Rij⊆R∩dyadicRows 1 k := Finset.filter_subset _ _
  have hsub : Rij⊆R := hsubk.trans Finset.inter_subset_left
  have hrows:=selected_rows_facts A.D A.F Z grid
  have hg:=hgeo R (fun u hu=>⟨(hrows u hu).1,(hrows u hu).2.1,(hrows u hu).2.2.2⟩) k
    (hne.mono hsubk)
  obtain ⟨u,hu⟩ := hne
  have hmem := (mem_cubeBinRows (R∩dyadicRows 1 k) idx grid i j u).mp hu
  have hgu := ((mem_supportedNonfloorRows A.F.S A.F.maximal _ grid u).mp (hsub hu)).2.2
  have hjpos : (0:ℝ)< j := by exact_mod_cast Nat.pos_of_ne_zero (hmem.2.2 ▸ hgu)
  have ha : (51/100:ℝ)<51/100+A.D.e*j := by nlinarith [A.D.e_pos]
  have hai : 51/100+A.D.e*j≤7/8 := by simpa only [hmem.2.2] using (hsel.2.1 u).2.1
  have hZp : 0< Z := zero_lt_one.trans hZ
  refine ⟨hg.2.2.1,hg.2.2.2.1,ha,hai,?_,?_,?_,?_,?_,?_⟩
  · intro u hu
    exact ⟨(hrows u (hsub hu)).1,(hrows u (hsub hu)).2.1,
      (hrows u (hsub hu)).2.2.1,hg.2.2.2.2.2 u (hsubk hu)⟩
  · intro u hu
    constructor
    · rw [←Real.rpow_mul hZp.le]
      apply (Real.rpow_le_rpow_of_exponent_le hZ.le ?_).trans (hrows u (hsub hu)).2.1
      have hd:=hg.2.2.2.1
      have hcap : OAI.SevenEighths.Target830.dPlus≤1 := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,OAI.SevenEighths.Target830.dPlus,OAI.SevenEighths.Target830.h]
      nlinarith
    · exact (hg.2.2.2.2.2 u (hsubk hu)).trans
        (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [A.D.t_pos]))
  · intro u hu
    simpa only [sourceDyadConductor,add_sub_cancel_right] using (hg.2.2.2.2.1 u (hsubk hu)).1
  · intro u hu
    exact (hsel.2.2 u ((mem_supportedNonfloorRows A.F.S A.F.maximal _ grid u).mp (hsub hu)).1
      (hrows u (hsub hu)).2.2.1).1
  · intro u hu
    have hb:=(hsel.2.1 u).2.2.2.2.1
    have hm:=(mem_cubeBinRows (R∩dyadicRows 1 k) idx grid i j u).mp hu
    rwa [hm.2.1,hm.2.2] at hb
  · intro u hu
    have hb:=(hsel.2.1 u).2.2.1
    have hm:=(mem_cubeBinRows (R∩dyadicRows 1 k) idx grid i j u).mp hu
    simpa only [hm.2.1,hm.2.2,Nat.cast_mul,Nat.cast_ofNat] using hb
end
end OAI.SevenEighths.Target830.Physical.FiniteNumerator

#print axioms OAI.SevenEighths.Target830.Physical.FiniteNumerator.actual_cell_geometry
end

/- Original module: Candidate.Target830.Physical.Finite.Summation. -/
section
/- Private .874836 actual numerator specialization; predecessor attribution retained. Apache-2.0. -/

set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Physical.FiniteNumerator
noncomputable section
open scoped Classical BigOperators
open Filter OAI.SevenEighths ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical
open OAI.SevenEighths.Target830.Physical FinalAssembly Target830PhysicalHighTransport
open OAI.SevenEighths.Target830.Physical.Assembly

def FullWCellsAt (A : ChosenData) (τ : ℝ) (n : ℕ) (η : Character) (C Z : ℝ) : Prop :=
  ∀idx grid : FreeRow→ℕ,
    ActualBufferedSelection A.F.modulus ⊤ le_top A.F.S A.F.exclusions A.F.maximal
      η rowPadding A.D.e τ n Z idx grid →
    ∀k∈smallDyadicIndices (Z^(OAI.SevenEighths.Target830.h+rowPadding)),
    ∀i∈Finset.range (n+1),∀j∈Finset.range (⌊(49/100:ℝ)/A.D.e⌋₊+1),
      (cellRows A.D A.F Z idx grid k i j).Nonempty →
      ‖fullW A.D A.F η Z (cellRows A.D A.F Z idx grid k i j)
        (fun _=>51/100+A.D.e*j) (fun _=>(3*i+1:ℕ)*Z^τ)/normalizer A.D A.F Z‖ ≤
        C*Z^(cellTarget+A.D.t/8)

/-- The genuine normalized full-W cell theorem fixes its degree before height. -/
def ActualFullWCellInput (A : ChosenData) (J : ℝ) : Prop :=
  ∀τ : ℝ,HeightAdmissible A.D A.P J τ → ∀n : ℕ,∀η : Character,
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,∀C0 : ℝ,1≤ C0 →
      SourceMomentBound A.D (baselineSource A.D A.F) A.counts η Z τ
        (C0*Z^A.D.t) (Z^(2*τ)) →
      FullWCellsAt A τ n η (C*C0*(η.modulus.absNorm:ℝ)^(2*A.P.eps)) Z

theorem cell_exponent_le (A : ChosenData) :
    cellTarget+A.D.t/4≤ HeckeZeroSupremum.beta+Assembly.signalShift-A.P.sigma := by
  have ht:=A.P.t_padding
  have hs:=A.P.sigma_small
  have hc:=A.count_budget
  have he:=A.D.epsilon_pos
  have htp:=A.D.t_pos
  dsimp [cellTarget,Scalar.sourceReserve]
  linarith

theorem fullW_sum_bound (A : ChosenData) (τ : ℝ) (n : ℕ) (η : Character)
    (C : ℝ) (hC : 0< C) :
    ∃Csum : ℝ,0< Csum ∧ ∀ᶠZ : ℝ in atTop,
      FullWCellsAt A τ n η C Z → ∀idx grid : FreeRow→ℕ,
      ActualBufferedSelection A.F.modulus ⊤ le_top A.F.S A.F.exclusions A.F.maximal
        η rowPadding A.D.e τ n Z idx grid →
      ‖fullW A.D A.F η Z (selectedRows A.D A.F Z grid)
        (fun u=>51/100+A.D.e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normalizer A.D A.F Z‖ ≤
        Csum*Z^(HeckeZeroSupremum.beta+Assembly.signalShift-A.P.sigma) := by
  have ht:=A.D.t_pos
  obtain ⟨Cd,hCd,hdyad⟩:=canonical_dyad_cost (A.D.t/8) (by positivity)
  let m : ℕ:=⌊(49/100:ℝ)/A.D.e⌋₊
  refine ⟨Cd*(n+1:ℕ)*(m+1:ℕ)*C,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ)] with Z hZ
  intro hcell idx grid hsel
  have hZp : 0< Z:=zero_lt_one.trans_le hZ
  have hrows:=selected_rows_facts A.D A.F Z grid
  have hb:=fullW_cells_norm_bound A.F.S A.F.exclusions A.F.maximal η
    (selectedRows A.D A.F Z grid) (primePool A.D A.F Z) (poolOutside A.D A.F Z)
    (fun _ y=>(A.F.w y:ℂ)) (fun j=> Z^(A.D.length j)) A.F.W A.F.W
    (Z^OAI.SevenEighths.Target830.x) (Z^OAI.SevenEighths.Target830.y) Z A.D.e (Z^τ) (Z^(OAI.SevenEighths.Target830.h+rowPadding))
    idx grid n m (normalizer A.D A.F Z) (C*Z^(cellTarget+A.D.t/8)) (by positivity)
    (fun u hu=>⟨(hrows u hu).1,(hrows u hu).2.2.2⟩)
    (fun u _=>⟨(hsel.1 u).2.1,(hsel.1 u).2.2.1⟩) (hcell idx grid hsel)
  have htop : OAI.SevenEighths.Target830.h+rowPadding≤1 := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,OAI.SevenEighths.Target830.h,rowPadding]
  have hd:=hdyad Z (OAI.SevenEighths.Target830.h+rowPadding) hZ htop
  have hexp:=Real.rpow_le_rpow_of_exponent_le hZ (cell_exponent_le A)
  calc
    _ ≤ ((smallDyadicIndices (Z^(OAI.SevenEighths.Target830.h+rowPadding))).card:ℝ)*(n+1:ℕ)*(m+1:ℕ)*
        (C*Z^(cellTarget+A.D.t/8)) := hb
    _ ≤ (Cd*Z^(A.D.t/8))*(n+1:ℕ)*(m+1:ℕ)*(C*Z^(cellTarget+A.D.t/8)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd (by positivity)) (by positivity))
        (by positivity)
    _ = (Cd*(n+1:ℕ)*(m+1:ℕ)*C)*Z^(cellTarget+A.D.t/4) := by
      have hp : Z^(A.D.t/8)*Z^(cellTarget+A.D.t/8)=Z^(cellTarget+A.D.t/4) := by
        rw [←Real.rpow_add hZp]
        congr 1
        ring
      calc
        _ = (Cd*(n+1:ℕ)*(m+1:ℕ)*C)*(Z^(A.D.t/8)*Z^(cellTarget+A.D.t/8)) := by ring
        _ = _ := by rw [hp]
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)
end
end OAI.SevenEighths.Target830.Physical.FiniteNumerator

#print axioms OAI.SevenEighths.Target830.Physical.FiniteNumerator.cell_exponent_le
#print axioms OAI.SevenEighths.Target830.Physical.FiniteNumerator.fullW_sum_bound
end
