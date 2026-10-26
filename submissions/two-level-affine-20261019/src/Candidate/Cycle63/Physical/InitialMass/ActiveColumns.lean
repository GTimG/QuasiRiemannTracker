import Candidate.Cycle63.Physical.InitialMass.AnnularSourceEnergy

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open RayFourExpansion ConcreteTraceCRT CenteredMomentSmooth
open CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O

abbrev FirstColumnIndex {Label : Type*} (s : Label→FirstBlockSource) :=
  (l : Label) × ↥(s l).divisors × RayCharacter × RayCharacter

def firstSectorColumn {Label : Type*} (s : Label→FirstBlockSource)
    (q : FirstSector s) : FirstColumnIndex s := ⟨q.1,q.2.1,q.2.2.1,q.2.2.2.1⟩

def firstColumnRows {Label : Type*} (s : Label→FirstBlockSource)
    (V : Fin 4→ℝ→ℂ) (j : FirstColumnIndex s) : Finset O :=
  (s j.1).rows.filter (fun z=>
    V 0 (Real.log ((s j.1).K/‖eisEmbedding (s j.1).e‖^2/
      ‖eisEmbedding (s j.1).r‖^2/(s j.1).K0))≠0 ∧
      V 1 (Real.log (‖eisEmbedding z‖^2/(s j.1).H0))≠0 ∧ Squarefree j.2.1.val)

/-- Separates only the row coordinate. The common ideal, residual divisor
and both ray indices are retained together in the outer Hilbert index. -/
theorem actual_first_active_columns {Label : Type*} [Fintype Label]
    (s : Label→FirstBlockSource) (V : Fin 4→ℝ→ℂ)
    (F : FirstColumnIndex s→O→ℝ) :
    (∑q∈firstActiveSectors s V,F (firstSectorColumn s q) q.2.2.2.2.val)=
      ∑j : FirstColumnIndex s,∑z∈firstColumnRows s V j,F j z := by
  rw [firstActiveSectors,Finset.sum_filter]
  simp only [Finset.sum_filter,Fintype.sum_sigma,
    Fintype.sum_prod_type,firstSectorColumn,firstRho,firstX,firstColumnRows]
  refine Finset.sum_congr rfl fun l hl => Finset.sum_congr rfl fun L hL => Finset.sum_congr rfl fun χ hχ => Finset.sum_congr rfl fun ψ hψ => ?_
  exact Finset.sum_coe_sort (s l).rows (fun z=>
    if V 0 (Real.log ((s l).K/‖eisEmbedding (s l).e‖^2/‖eisEmbedding (s l).r‖^2/(s l).K0))≠0 ∧
      V 1 (Real.log (‖eisEmbedding z‖^2/(s l).H0))≠0 ∧ Squarefree L.val then F ⟨l,L,χ,ψ⟩ z else 0)

theorem actual_first_column_annulus {Label : Type*} [Fintype Label]
    (s : Label→FirstBlockSource) (j : FirstColumnIndex s) (z : O)
    (hz : z∈firstColumnRows s (fun _=>logAnnulus) j) :
    (s j.1).H0/4≤‖eisEmbedding z‖^2 ∧ ‖eisEmbedding z‖^2≤(s j.1).H0 := by
  have hmem := Finset.mem_filter.mp hz
  let q : FirstSector s := ⟨j.1,j.2.1,j.2.2.1,j.2.2.2,⟨z,hmem.1⟩⟩
  exact actual_first_active_annulus s q (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hmem.2⟩)

def firstLiveColumns {Label : Type*} [Fintype Label]
    (s : Label→FirstBlockSource) (V : Fin 4→ℝ→ℂ) : Finset (FirstColumnIndex s) :=
  Finset.univ.filter (fun j=>(firstColumnRows s V j).Nonempty)

theorem actual_first_live_squarefree {Label : Type*} [Fintype Label]
    (s : Label→FirstBlockSource) (V : Fin 4→ℝ→ℂ) (j : FirstColumnIndex s)
    (hj : j∈firstLiveColumns s V) : Squarefree j.2.1.val := by
  obtain ⟨z,hz⟩ := (Finset.mem_filter.mp hj).2
  exact (Finset.mem_filter.mp hz).2.2.2

theorem actual_first_live_columns {Label : Type*} [Fintype Label]
    (s : Label→FirstBlockSource) (V : Fin 4→ℝ→ℂ)
    (F : FirstColumnIndex s→O→ℝ) :
    (∑q∈firstActiveSectors s V,F (firstSectorColumn s q) q.2.2.2.2.val)=
      ∑j∈firstLiveColumns s V,∑z∈firstColumnRows s V j,F j z := by
  rw [actual_first_active_columns]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j hj hnot
  have hempty : firstColumnRows s V j=∅ := Finset.not_nonempty_iff_eq_empty.mp
    (fun h=>hnot (Finset.mem_filter.mpr ⟨hj,h⟩))
  rw [hempty,Finset.sum_empty]

open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstPhysicalSource
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentFirstAllocationGaussEnergy

/-- The localized Hilbert sum feeds directly into actual common allocation
and child energies, preserving its full outer label and both ray indices. -/
theorem actual_active_common_live_energy {Label ι : Type*} [Fintype Label] [Fintype ι]
    (reflected : Bool) (src : Label→FirstBlockSource) (N : ℕ) (a b : ℝ) (ha : 0<a) (s : Input ι)
    (hcard : Fintype.card ι≤N) (haS : a≤ s.lower) (hbS : s.upper≤b)
    (C : FirstColumnIndex src→ Ideal O) (R seed : Ideal O)
    (hC : ∀j,Supported (C j)) (hseed : ∀j,seed∣C j)
    (τ : FirstColumnIndex src→ Character) (t weight : FirstColumnIndex src→ℝ)
    (hw : ∀j,0≤weight j) :
    (∑q∈firstActiveSectors src (fun _=>logAnnulus),
      weight (firstSectorColumn src q)*
        ‖allocatedPolynomial (original s R seed) (C (firstSectorColumn src q))
          q.2.1.val (τ (firstSectorColumn src q)) (t (firstSectorColumn src q))
          (volume s) (firstSignedRow reflected q.2.2.2.2.val)‖^2)≤
      ∑j∈firstLiveColumns src (fun _=>logAnnulus),
        weight j*((max 1 b)^N*((actualAllocations s.pools (C j)).card:ℝ)/(C j).absNorm*
          ∑B : actualAllocations s.pools (C j),
            if frozenCoefficient B.val (C j) R s.ν s.W s.P≠0 then
              (frozenControl B.val s.M)^2*childNormalizedGaussSource s (C j) R j.2.1.val B
                (τ j) (t j) CenteredMomentFirstAnnularMajorant.profile (src j.1).H0
            else 0) := by
  have he := actual_first_live_columns src (fun _=>logAnnulus)
    (fun j z=>weight j*‖allocatedPolynomial (original s R seed) (C j) j.2.1.val
      (τ j) (t j) (volume s) (firstSignedRow reflected z)‖^2)
  change _ = ∑j∈firstLiveColumns src (fun _=>logAnnulus),∑z∈firstColumnRows src (fun _=>logAnnulus) j,
    weight j*‖allocatedPolynomial (original s R seed) (C j) j.2.1.val
      (τ j) (t j) (volume s) (firstSignedRow reflected z)‖^2 at he
  apply le_trans (le_of_eq he)
  simp_rw [←Finset.mul_sum]
  exact actual_joint_annular_live_energy reflected (firstLiveColumns src (fun _=>logAnnulus)) N a b ha s hcard haS hbS C R seed hC hseed τ t
    (fun j=>j.2.1.val) (fun j=>(src j.1).H0) weight (firstColumnRows src (fun _=>logAnnulus))
    (fun j=>(src j.1).H0_pos) hw (actual_first_column_annulus src)

end
end OAI.SevenEighths.Cycle63InitialMass
