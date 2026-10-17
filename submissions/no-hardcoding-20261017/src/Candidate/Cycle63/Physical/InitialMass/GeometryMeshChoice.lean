/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryLossSchedule
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorCoprime
import Candidate.Cycle63.Physical.FirstBranches.FixedComparison
import Candidate.Cycle63.Physical.AmplifierSupport

set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open Filter HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAllocatedRayDictionary
open CenteredMomentPrimePool CenteredMomentAmplificationSlotGap CenteredMomentAmplificationEligibility
open CenteredMomentPrimeElements CompletedGauss
local notation "O" => HeckeFamily.O

/-- The analytic mesh is fixed before a chosen slot dictionary or its size. -/
def geometryAnalyticMesh (Mmin Mmax εaffine Mcap Bmask L : ℝ) : ℝ :=
  let μ:=geometryLossUnit Mmin εaffine
  min (Cycle63FirstActual.comparisonMesh Mmin Mmax εaffine)
    (min (Cycle25.Energy.commonMesh Mcap Bmask L (μ/8))
      (min (μ/8) (Mmin*Cycle63.Arithmetic.amplifierFloor/4)))/2

theorem geometry_analytic_mesh_admission (Mmin Mmax εaffine Mcap Bmask L : ℝ)
    (hmin : 0<Mmin)(hmax : Mmin≤Mmax)(hε : 0<εaffine)
    (hcap : 0<Mcap)(hmask : 0≤Bmask) :
    let μ:=geometryLossUnit Mmin εaffine
    let mesh:=geometryAnalyticMesh Mmin Mmax εaffine Mcap Bmask L
    0<mesh ∧ mesh≤Cycle63FirstActual.comparisonMesh Mmin Mmax εaffine ∧
      mesh≤Cycle25.Energy.commonMesh Mcap Bmask L (μ/8) ∧ mesh≤μ/8 ∧
      mesh<Mmin*Cycle63.Arithmetic.amplifierFloor/2 := by
  intro μ mesh
  have hu : 0<μ := geometry_loss_unit_pos Mmin εaffine hmin hε
  have hc := Cycle63FirstActual.comparisonMesh_pos Mmin Mmax εaffine hmin hmax hε
  have ho := Cycle25.Energy.commonMesh_pos Mcap Bmask L (μ/8) hcap.le hmask (by positivity)
  have hfl := Cycle63.Arithmetic.amplifierFloor_pos
  have hm : 0<mesh := by dsimp [mesh,geometryAnalyticMesh];change 0<min _ (min _ (min (μ/8) _))/2;positivity
  have ha : 2*mesh≤Cycle63FirstActual.comparisonMesh Mmin Mmax εaffine := by
    dsimp [mesh,geometryAnalyticMesh];linarith [min_le_left
      (Cycle63FirstActual.comparisonMesh Mmin Mmax εaffine)
      (min (Cycle25.Energy.commonMesh Mcap Bmask L (μ/8)) (min (μ/8) (Mmin*Cycle63.Arithmetic.amplifierFloor/4)))]
  have ht : 2*mesh≤min (Cycle25.Energy.commonMesh Mcap Bmask L (μ/8))
      (min (μ/8) (Mmin*Cycle63.Arithmetic.amplifierFloor/4)) := by
    dsimp [mesh,geometryAnalyticMesh];linarith [min_le_right
      (Cycle63FirstActual.comparisonMesh Mmin Mmax εaffine)
      (min (Cycle25.Energy.commonMesh Mcap Bmask L (μ/8)) (min (μ/8) (Mmin*Cycle63.Arithmetic.amplifierFloor/4)))]
  have hb := ht.trans (min_le_left _ _)
  have hd := ht.trans (min_le_right _ _)
  have he := hd.trans (min_le_left _ _)
  have hf := hd.trans (min_le_right _ _)
  refine ⟨hm,?_,?_,?_,?_⟩ <;> linarith

variable (rayM : Ideal O) [NeZero rayM]
local instance meshFiniteQuotient : Finite (O⧸rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ)(hH : RayOrthogonality.globalUnits rayM≤H)

/-- The actual annular amplifier pool is disjoint from every original
stored slot, uniformly before sources and supported cell widths move. -/
theorem eventual_actual_amplifier_slot_coprime (Sbad : Finset (Ideal O))
    (hbad : fixedBadPrimes⊆Sbad)
    (Mmin mesh bslot : ℝ)(hmin : 0<Mmin)
    (hmesh : mesh<Mmin*Cycle63.Arithmetic.amplifierFloor/2) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧
    ∀{α : Type*}[Fintype α][DecidableEq α],
    ∀(s : Input α)(η₀ : Character)(θ : α→RayQuotient.Characters rayM H)
      (w σ v : α→ℝ)(W : ℝ→ℂ),
      Matches rayM H hH s η₀ θ w σ v W bslot Z → (∀j,w j≤mesh) →
    ∀M beta : ℝ,Mmin≤M → Cycle63.Optimization.firstCellTop≤beta → beta≤Cycle63.Optimization.slotTop →
    ∀Q∈primePool rayM H Sbad (1/2) 1 (Z^(M*Cycle63.Arithmetic.amp beta)),
      ∀j I,I∈s.slots j→IsCoprime Q I := by
  let ell:=Mmin*Cycle63.Arithmetic.amplifierFloor/2
  filter_upwards [eventually_scale_gap (max 1 bslot) mesh ell hmesh,
    Cycle63.Physical.actual_amplifier_prime_width rayM H Sbad Mmin hmin] with Z hg hp
  refine ⟨hp.1,?_⟩
  intro α _ _ s η₀ θ w σ v W hm hw M beta hM hb₁ hb₂ Q hQ
  have hd := primePool_data rayM H Sbad hbad (1/2) 1 (Z^(M*Cycle63.Arithmetic.amp beta)) Q hQ
  have hn := (hp.2 M beta hM hb₁ hb₂ Q hQ).1
  have ha := (Cycle63.Arithmetic.amp_bounds ⟨hb₁,hb₂⟩).1
  have hm0 : 0≤M := (hmin.trans_le hM).le
  have hprod := mul_le_mul_of_nonneg_left ha hm0
  have hell : ell≤3*(M*Cycle63.Arithmetic.amp beta)/4 := by
    dsimp [ell]
    nlinarith [mul_le_mul_of_nonneg_right hM Cycle63.Arithmetic.amplifierFloor_pos.le,
      mul_nonneg hm0 (Cycle63.Arithmetic.amp_pos ⟨hb₁,hb₂⟩).le]
  have hnorm : 0<(Q.absNorm:ℝ) := CenteredMomentFirstScale.norm_pos Q hd.1.ne_zero
  have hQN : Z^ell≤(Q.absNorm:ℝ) :=
    (Real.le_logb_iff_rpow_le hp.1 hnorm).mp (hell.trans hn)
  exact actual_full_slot_coprime rayM H hH s η₀ θ w σ v W bslot Z mesh ell hp.1.le hm hw Q hd.1 hQN hg.2

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_analytic_mesh_admission
#print axioms OAI.SevenEighths.Cycle63InitialMass.eventual_actual_amplifier_slot_coprime
