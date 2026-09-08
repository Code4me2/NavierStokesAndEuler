import Euler.TerminalTimePrimitive
import Euler.TransverseVariationalOperator
import Euler.TransverseFrameCoordinates

/-!
# The actual zero-endpoint transverse displacement inverse

We use the derivative of the physical displacement as the Hilbert-space
variable.  Terminal integration supplies the displacement.  Its initial trace
and its moving normal component are bounded linear constraints, hence define a
closed Hilbert subspace.  The kinetic energy is exactly the squared norm on this
space; no norm equivalence or pre-existing differential inverse is assumed.

This constructs the weak transverse inverse in source lines 172--184.  The
coordinate identity `η = F R ξ` and strong coordinate evolution require the
separate frame and regularity arguments; they are not assumed in this file.
-/

noncomputable section

namespace EulerTransverseVariationalInverse

open MeasureTheory Set InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerTerminalTimePrimitive EulerVolterraConvolution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Derivatives of actual zero-endpoint displacements tangent to the moving plane. -/
def transverseDerivatives (T : ℝ) (hT : 0 ≤ T) (m : Icc (0 : ℝ) T → E) :
    Submodule ℝ (TimeLp T E) where
  carrier := {u | initialTrace T hT u = 0 ∧
    ∀ t, ⟪m t, terminalPrimitive T hT u t⟫_ℝ = 0}
  zero_mem' := by
    constructor
    · exact map_zero _
    · intro t
      simp only [map_zero, ContinuousMap.zero_apply, inner_zero_right]
  add_mem' := by
    intro u v hu hv
    constructor
    · simp only [map_add, hu.1, hv.1, add_zero]
    · intro t
      simp only [map_add, ContinuousMap.add_apply, inner_add_right, hu.2 t, hv.2 t,
        add_zero]
  smul_mem' := by
    intro a u hu
    constructor
    · simp only [map_smul, hu.1, smul_zero]
    · intro t
      simp only [map_smul, ContinuousMap.smul_apply, inner_smul_right, hu.2 t,
        mul_zero]

/-- The two endpoint and moving tangency conditions are closed constraints. -/
theorem transverseDerivatives_closed (T : ℝ) (hT : 0 ≤ T) (m : Icc (0 : ℝ) T → E) :
    IsClosed (transverseDerivatives T hT m : Set (TimeLp T E)) := by
  change IsClosed {u : TimeLp T E | initialTrace T hT u = 0 ∧
    ∀ t, ⟪m t, terminalPrimitive T hT u t⟫_ℝ = 0}
  rw [Set.ofPred_and, Set.ofPred_forall]
  apply (isClosed_eq (initialTrace T hT).continuous continuous_const).inter
  apply isClosed_iInter
  intro t
  exact isClosed_eq
    (continuous_const.inner ((ContinuousMap.evalCLM ℝ t).continuous.comp
      (terminalPrimitive T hT).continuous)) continuous_const

/-- Closedness supplies completeness for the actual displacement-derivative space. -/
instance transverseDerivatives_complete [CompleteSpace E] (T : ℝ) (hT : 0 ≤ T)
    (m : Icc (0 : ℝ) T → E) : CompleteSpace (transverseDerivatives T hT m) :=
  (transverseDerivatives_closed T hT m).completeSpace_coe


/-- Every genuine absolutely continuous zero-endpoint transverse path with an
L² derivative belongs to this Hilbert model.  Thus the test space is not an
assumed family of already solved displacements. -/
theorem derivative_mem_of_ac [CompleteSpace E] (T : ℝ) (hT : 0 ≤ T)
    (m : Icc (0 : ℝ) T → E) (u : TimeLp T E) (η : ℝ → E)
    (hη : AbsolutelyContinuousOnInterval η 0 T)
    (hder : ∀ᵐ t ∂timeMeasure T, HasDerivAt η (u t) t)
    (hzero : η 0 = 0) (hterminal : η T = 0)
    (htangent : ∀ t : Icc (0 : ℝ) T, ⟪m t, η t⟫_ℝ = 0) :
    u ∈ transverseDerivatives T hT m := by
  have heq := eq_realPrimitive_of_ac_hasDerivAt_ae T hT u η hη hder hterminal
  constructor
  · change realPrimitive T u 0 = 0
    rw [← heq 0 ⟨le_rfl, hT⟩, hzero]
  · intro t
    change ⟪m t, realPrimitive T u t⟫_ℝ = 0
    rw [← heq t t.property]
    exact htangent t

/-- The actual terminal primitive restricted to the transverse derivative space. -/
def transversePrimitive (T : ℝ) (hT : 0 ≤ T) (m : Icc (0 : ℝ) T → E) :
    transverseDerivatives T hT m →L[ℝ] TimeLp T E :=
  (primitiveTimeLp T hT).comp (transverseDerivatives T hT m).subtypeL

/-- The sharp time Poincaré bound holds on the actual transverse space. -/
theorem transversePrimitive_norm_sq (T : ℝ) (hT : 0 ≤ T)
    (m : Icc (0 : ℝ) T → E) (u : transverseDerivatives T hT m) :
    ‖transversePrimitive T hT m u‖ ^ 2 ≤ T ^ 2 / 2 * ‖u‖ ^ 2 :=
  primitiveTimeLp_norm_sq_le T hT (u : TimeLp T E)

/-- A convenient polynomial operator bound for the terminal primitive. -/
theorem transversePrimitive_norm_le (T : ℝ) (hT : 0 ≤ T)
    (m : Icc (0 : ℝ) T → E) : ‖transversePrimitive T hT m‖ ≤ T := by
  apply ContinuousLinearMap.opNorm_le_bound _ hT
  intro u
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hT (norm_nonneg u))).1
  calc
    ‖transversePrimitive T hT m u‖ ^ 2 ≤ T ^ 2 / 2 * ‖u‖ ^ 2 :=
      transversePrimitive_norm_sq T hT m u
    _ ≤ T ^ 2 * ‖u‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg ‖u‖)
      nlinarith only [sq_nonneg T]
    _ = (T * ‖u‖) ^ 2 := by ring

variable [CompleteSpace E]
variable (T : ℝ) (hT : 0 ≤ T) (m : Icc (0 : ℝ) T → E)
variable (H : C(Icc (0 : ℝ) T, E →L[ℝ] E))
variable (K : ℝ) (hK : 0 ≤ K)
variable (hH : ∀ t x, ⟪H t x, x⟫_ℝ ≤ K * ‖x‖ ^ 2)
variable (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2)

/-- The actual transverse forcing-to-derivative map, constructed from the
primitive and the given time-dependent Hessian. -/
def transverseSolver : TimeLp T E →L[ℝ] transverseDerivatives T hT m :=
  dirichletSolver (transversePrimitive T hT m) (timeMultiplier T hT H)
    (T ^ 2 / 2) K hK (transversePrimitive_norm_sq T hT m)
    (timeMultiplier_quadratic_upper T hT H K hH) hsmall

/-- The continuous displacement is constructed by integrating its solved derivative. -/
def transverseDisplacement : TimeLp T E →L[ℝ] C(Icc (0 : ℝ) T, E) :=
  (terminalPrimitive T hT).comp
    ((transverseDerivatives T hT m).subtypeL.comp
      (transverseSolver T hT m H K hK hH hsmall))





/-- The actual weak transverse displacement equation, tested against every
zero-endpoint displacement in the same moving plane. -/
theorem transverseSolver_weak (f : TimeLp T E) (v : transverseDerivatives T hT m) :
    let u := transverseSolver T hT m H K hK hH hsmall f
    ⟪(u : TimeLp T E), (v : TimeLp T E)⟫_ℝ -
        ⟪timeMultiplier T hT H (transversePrimitive T hT m u),
          transversePrimitive T hT m v⟫_ℝ =
      -⟪f, transversePrimitive T hT m v⟫_ℝ :=
  dirichletSolver_weak (transversePrimitive T hT m) (timeMultiplier T hT H)
    (T ^ 2 / 2) K hK (transversePrimitive_norm_sq T hT m)
    (timeMultiplier_quadratic_upper T hT H K hH) hsmall f v



/-- Zero forcing has zero displacement, the pointwise-in-label support preservation property. -/
@[simp] theorem transverseDisplacement_zero :
    transverseDisplacement T hT m H K hK hH hsmall 0 = 0 := map_zero _





end EulerTransverseVariationalInverse
