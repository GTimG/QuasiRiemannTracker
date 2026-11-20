/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A finite outer conductor mesh for P.1. The true norm radius stays in the
sum; detector, earlier source and scalar certificate may use the same
slightly larger mesh point, with a single stated power loss. -/
import Candidate.C092.transport.FixedWitnessLabel
import Candidate.C092.transport.LowActualRadiusBank

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily ConcreteTraceCRT
open HeckeInverseAmplification ProbeHighRowFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorEnergyInitialState
open QRH.Cycle092.LowActual QRH.Cycle092.Source QRH.SourceCertificate
namespace QRH.Cycle092.MediumReplace.Source
local notation "O" => HeckeFamily.O

theorem conductor_bank (lo hi δ : ℝ) (hl : lo ≤ hi) (hd : 0 < δ) :
    ∃ bank : Finset ℝ, (∀ d ∈ bank, lo+2*δ ≤ d ∧ d ≤ hi+3*δ) ∧
      ∀ V, lo ≤ V → V ≤ hi → ∃ d ∈ bank, V+2*δ ≤ d ∧ d ≤ V+3*δ := by
  obtain ⟨s,hs,hnet⟩ := finite_left_radius_bank hl hd
  refine ⟨s.image (fun r => r+3*δ),?_,?_⟩
  · intro d hh; obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hh
    obtain ⟨hlo,hhi⟩ := hs r hr
    exact ⟨by linarith,by linarith⟩
  · intro V hV hV'
    obtain ⟨r,hr,hrV,hVr⟩ := hnet V hV hV'
    exact ⟨r+3*δ,Finset.mem_image.mpr ⟨r,hr,rfl⟩,by linarith,by linarith⟩

theorem enlarged_price {V d δ : ℝ} (h : V ≤ d) (h' : d ≤ V+δ) :
    d+radialAllowance d ≤ V+radialAllowance V+δ := by
  have hm : max 0 ((H:ℝ)-d) ≤ max 0 ((H:ℝ)-V) := max_le_max_left _ (by linarith)
  unfold radialAllowance; linarith

variable (M : Ideal O) [NeZero M]
local instance c092LocalInst_Candidate_C092_transport_WitnessConductorBank_1e39378c5dc0aa78_001 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hr : Subgroup (O⧸M)ˣ) (hHr : RayOrthogonality.globalUnits M ≤ Hr)

/-- All fixed labels on all actual retained cores share a member of a finite
conductor bank. The bank, the support, and the threshold precede the live
radius and row. In particular d=V is never assumed as a conductor bound. -/
theorem source_core_conductors (η η₀ : Character) (Q : Ideal O) (lo hi δ : ℝ)
    (hlo : 0 ≤ lo) (hlh : lo ≤ hi) (hδ : 0 < δ) :
    ∃ bank : Finset ℝ, (∀ d ∈ bank, lo+2*δ ≤ d ∧ d ≤ hi+3*δ) ∧
    ∃ bΦ : ℝ, 2 ≤ bΦ ∧ ∃ hs : Function.support (radialMajorant:ℝ→ℂ) ⊆ Set.Iic bΦ,
    ∀ᶠ U : ℝ in atTop, ∃ hU : 1<U, ∃ hη : (η.modulus.absNorm:ℝ) ≤ U^δ,
    ∀ V, lo ≤ V → V ≤ hi → ∃ d ∈ bank, V+2*δ ≤ d ∧ d ≤ V+3*δ ∧
      ∀ (u : FreeRow) (hV : 0 ≤ V), rowNorm u ≤ U^V →
      let st := regularState η Q radialMajorant bΦ U V δ hU.le hV hδ.le hs radialMajorant_nonneg hη
      ∀ (F : NaturalRow st.character u.val) j, ((family M Hr hHr st η₀ F j).modulus.absNorm:ℝ) ≤ U^d := by
  obtain ⟨bank,hbk,hselect⟩ := conductor_bank lo hi δ hlh hδ
  obtain ⟨b,hb,hs₀⟩ := radialMajorant_support_bound
  let bΦ := max 2 b
  have hbΦ : 2 ≤ bΦ := le_max_left _ _
  have hφ : 0 ≤ bΦ := (by norm_num : (0:ℝ) ≤ 2).trans hbΦ
  have hs : Function.support (radialMajorant:ℝ→ℂ) ⊆ Set.Iic bΦ :=
    fun x hx => le_trans (show x≤b from hs₀ hx) (le_max_right _ _)
  refine ⟨bank,hbk,bΦ,hbΦ,hs,?_⟩
  have hsrc (d : bank) := family_conductor_eventually M Hr hHr η₀ bΦ (d.val-δ) 0 δ hφ hδ
  have hm := (tendsto_rpow_atTop hδ).eventually (eventually_ge_atTop (η.modulus.absNorm:ℝ))
  filter_upwards [Filter.eventually_all.mpr hsrc,hm,eventually_gt_atTop (1:ℝ)] with U hsrcU hη hU
  refine ⟨hU,hη,?_⟩; intro V hV hV'
  obtain ⟨d,hd,hvd,hdv⟩ := hselect V hV hV'
  refine ⟨d,hd,hvd,hdv,?_⟩
  intro u hV0 hu
  let st := regularState η Q radialMajorant bΦ U V δ hU.le hV0 hδ.le hs radialMajorant_nonneg hη
  have hw : st.width ≤ d-δ := by rw [show st.width = V+δ from regularState_width ..]; linarith
  have hscale : 0 < U^V := Real.rpow_pos_of_pos (zero_lt_one.trans hU) V
  have hprof : st.radial.profile (‖eisEmbedding u.val‖^2/st.radial.scale) ≠ 0 := by
    change radialMajorant (‖eisEmbedding u.val‖^2/U^V) ≠ 0
    rw [radialMajorant_one _ ⟨div_nonneg (sq_nonneg _) hscale.le,(div_le_one hscale).mpr ?_⟩]
    · exact one_ne_zero
    · rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]; exact hu
  change ∀ (F : NaturalRow st.character u.val) j, ((family M Hr hHr st η₀ F j).modulus.absNorm:ℝ) ≤ U^d
  intro F j
  simpa only [add_zero,sub_add_cancel] using (hsrcU ⟨d,hd⟩).2 st hw u.val F hprof j

#print axioms source_core_conductors
#print axioms enlarged_price
end QRH.Cycle092.MediumReplace.Source
