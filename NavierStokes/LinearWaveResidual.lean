import NavierStokes.HarmonicCalculus
import NavierStokes.CylindricalResidual
import NavierStokes.TangentProjection

/-!
# Exact linear harmonic residual

Every differential operator uses an actual Fréchet derivative. The coefficient
field supplied to the linearization is arbitrary, so the formula also applies
to a curl-corrected coefficient without replacing it by its tangent principal
part. The angular direction is unscaled.
-/

noncomputable section

namespace NavierStokes.LinearWaveResidual

open HarmonicCalculus Set Filter
open scoped Topology ContDiff BigOperators


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def timeDirection (ε : ℝ) (Vf Vs : E → E) (x : E) : E :=
  Vf x - ε • Vs x

theorem along_timeDirection (ε : ℝ) (Vf Vs : E → E) (f : E → ℂ) (x : E) :
    along (timeDirection ε Vf Vs) f x = along Vf f x - (ε : ℂ) * along Vs f x := by
  simp [along, timeDirection, map_sub, map_smul, Complex.real_smul]

theorem along_mul_real (V : E → E) {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    along V (fun y => f y * g y) x = along V f x * g x + f x * along V g x := by
  simp only [along, fderiv_fun_mul hf hg, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul]
  ring

/-- The real base components, with angular velocity `V=R F`. -/
noncomputable def base (R b F G : E → ℝ) (x : E) : Fin 3 → ℝ :=
  ![b x, R x * F x, G x]

noncomputable def complexBase (R b F G : E → ℝ) (x : E) : ComplexVector :=
  fun i => (base R b F G x i : ℂ)

/-- Cylindrical bilinear advection, including the derivative of the frame. -/
noncomputable def transport (R : E → ℝ) (Vr Vθ Vz : E → E)
    (u v : E → ComplexVector) (x : E) : ComplexVector := fun i =>
  u x 0 * along Vr (fun y => v y i) x +
    (u x 1 / (R x : ℂ)) * (along Vθ (fun y => v y i) x + angularGenerator (v x) i) +
    u x 2 * along Vz (fun y => v y i) x

noncomputable def gradient (R : E → ℝ) (Vr Vθ Vz : E → E)
    (p : E → ℂ) (x : E) : ComplexVector :=
  ![along Vr p x, (R x)⁻¹ • along Vθ p x, along Vz p x]

/-- The genuine differential linearization with viscosity `ε`. -/
noncomputable def linearResidual (ε : ℝ) (R : E → ℝ) (Vr Vθ Vz Vt : E → E)
    (B a : E → ComplexVector) (p : E → ℂ) (x : E) : ComplexVector := fun i =>
  along Vt (fun y => a y i) x + transport R Vr Vθ Vz B a x i +
    transport R Vr Vθ Vz a B x i + gradient R Vr Vθ Vz p x i -
    (ε : ℂ) * cylindricalVectorLaplacian R Vr Vθ Vz a x i

/-- Matrix `K` from (27), with its radial coefficients actually differentiated. -/
noncomputable def shear (R F G : E → ℝ) (Vr : E → E)
    (a : E → ComplexVector) (x : E) : ComplexVector :=
  ![-2 * (F x : ℂ) * a x 1,
    Complex.ofReal (2 * F x + R x * along Vr F x) * a x 0,
    Complex.ofReal (along Vr G x) * a x 0]

/-- The base derivative and radial-flow connection terms outside `K`. -/
noncomputable def baseDerivativeRemainder (R b F G : E → ℝ) (Vr Vz : E → E)
    (a : E → ComplexVector) (x : E) : ComplexVector := fun i =>
  (![a x 0 * Complex.ofReal (along Vr b x), (b x : ℂ) / (R x : ℂ) * a x 1, 0] i) +
    a x 2 * Complex.ofReal (along Vz (fun y => base R b F G y i) x)

noncomputable def materialPhaseDefect (_R b F G : E → ℝ) (Vr Vθ Vz Vt : E → E)
    (Φ : E → ℝ) (x : E) : ℝ :=
  along Vt Φ x + b x * along Vr Φ x + F x * along Vθ Φ x + G x * along Vz Φ x

noncomputable def slowTransport (ε : ℝ) (b G : E → ℝ) (Vs Vr Vz : E → E)
    (a : E → ComplexVector) (x : E) : ComplexVector := fun i =>
  -(ε : ℂ) * along Vs (fun y => a y i) x +
    (b x : ℂ) * along Vr (fun y => a y i) x +
    (G x : ℂ) * along Vz (fun y => a y i) x

noncomputable def strippedPressureGradient (Vr Vz : E → E) (p : E → ℂ)
    (x : E) : ComplexVector := ![along Vr p x, 0, along Vz p x]

/-- The complete viscous braces in (31), after removal of phase-square damping. -/
noncomputable def viscousRemainder (R : E → ℝ) (Vr Vθ Vz : E → E) (κ : ℝ)
    (Φ : E → ℝ) (a : E → ComplexVector) (x : E) : ComplexVector := fun i =>
  along Vr (along Vr (fun y => a y i)) x + (R x)⁻¹ • along Vr (fun y => a y i) x +
    along Vz (along Vz (fun y => a y i)) x +
    ((R x) ^ 2)⁻¹ • angularGenerator (angularGenerator (a x)) i +
    2 * phaseFactor κ *
      (Complex.ofReal (phaseNormal R Vr Vθ Vz Φ x 0) * along Vr (fun y => a y i) x +
        Complex.ofReal (phaseNormal R Vr Vθ Vz Φ x 2) * along Vz (fun y => a y i) x) +
    phaseFactor κ * Complex.ofReal
      (along Vr (fun y => phaseNormal R Vr Vθ Vz Φ y 0) x +
        phaseNormal R Vr Vθ Vz Φ x 0 / R x +
        along Vz (fun y => phaseNormal R Vr Vθ Vz Φ y 2) x) * a x i +
    2 * phaseFactor κ * Complex.ofReal (phaseNormal R Vr Vθ Vz Φ x 1 / R x) *
      angularGenerator (a x) i

noncomputable def principal (ε κ : ℝ) (R F G : E → ℝ) (Vr Vθ Vz Vf : E → E)
    (Φ : E → ℝ) (a : E → ComplexVector) (p : E → ℂ) (x : E) : ComplexVector := fun i =>
  along Vf (fun y => a y i) x + shear R F G Vr a x i +
    Complex.ofReal (ε * κ ^ 2 * ‖phaseNormal R Vr Vθ Vz Φ x‖ ^ 2) * a x i +
    phaseFactor κ * Complex.ofReal (phaseNormal R Vr Vθ Vz Φ x i) * p x

noncomputable def remainder (ε κ : ℝ) (R b F G : E → ℝ) (Vr Vθ Vz Vf Vs : E → E)
    (Φ : E → ℝ) (a : E → ComplexVector) (p : E → ℂ) (x : E) : ComplexVector := fun i =>
  slowTransport ε b G Vs Vr Vz a x i +
    phaseFactor κ * Complex.ofReal
      (materialPhaseDefect R b F G Vr Vθ Vz (timeDirection ε Vf Vs) Φ x) * a x i +
    baseDerivativeRemainder R b F G Vr Vz a x i + strippedPressureGradient Vr Vz p x i -
    (ε : ℂ) * viscousRemainder R Vr Vθ Vz κ Φ a x i

theorem differentiableAt_base {R b F G : E → ℝ} {x : E}
    (hR : DifferentiableAt ℝ R x) (hb : DifferentiableAt ℝ b x)
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) (i : Fin 3) :
    DifferentiableAt ℝ (fun y => base R b F G y i) x := by
  fin_cases i
  · exact hb
  · exact hR.mul hF
  · exact hG

theorem along_complexBase (V : E → E) {R b F G : E → ℝ} {x : E}
    (hR : DifferentiableAt ℝ R x) (hb : DifferentiableAt ℝ b x)
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) (i : Fin 3) :
    along V (fun y => complexBase R b F G y i) x =
      Complex.ofReal (along V (fun y => base R b F G y i) x) :=
  along_ofReal V (differentiableAt_base hR hb hF hG i)

theorem gradient_mode (R : E → ℝ) (Vr Vθ Vz : E → E) (κ : ℝ)
    {Φ : E → ℝ} {p : E → ℂ} {x : E}
    (hΦ : DifferentiableAt ℝ Φ x) (hp : DifferentiableAt ℝ p x)
    (hpθ : along Vθ p x = 0) :
    gradient R Vr Vθ Vz (mode κ Φ p) x = fun i =>
      (strippedPressureGradient Vr Vz p x i +
        phaseFactor κ * Complex.ofReal (phaseNormal R Vr Vθ Vz Φ x i) * p x) * carrier κ Φ x := by
  ext i
  fin_cases i <;>
    simp [gradient, strippedPressureGradient, phaseNormal, along_mode _ κ hΦ hp,
      hpθ, Complex.real_smul, div_eq_mul_inv]
  all_goals ring

/-- The two linear advection terms produce `K` and exactly the displayed
base-derivative and radial-flow connection terms. -/
theorem linearAdvection_mode (R b F G : E → ℝ) (Vr Vθ Vz : E → E) (κ : ℝ)
    {Φ : E → ℝ} {a : E → ComplexVector} {x : E}
    (hR : DifferentiableAt ℝ R x) (hb : DifferentiableAt ℝ b x)
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x)
    (hRx : R x ≠ 0) (hDr : along Vr R x = 1)
    (hBθ : ∀ i, along Vθ (fun y => base R b F G y i) x = 0)
    (hΦ : DifferentiableAt ℝ Φ x)
    (ha : ∀ i, DifferentiableAt ℝ (fun y => a y i) x)
    (haθ : ∀ i, along Vθ (fun y => a y i) x = 0) :
    (fun i => transport R Vr Vθ Vz (complexBase R b F G) (vectorMode κ Φ a) x i +
      transport R Vr Vθ Vz (vectorMode κ Φ a) (complexBase R b F G) x i) = fun i =>
      ((b x : ℂ) * along Vr (fun y => a y i) x +
        (G x : ℂ) * along Vz (fun y => a y i) x + shear R F G Vr a x i +
        baseDerivativeRemainder R b F G Vr Vz a x i +
        phaseFactor κ * Complex.ofReal
          (b x * along Vr Φ x + F x * along Vθ Φ x + G x * along Vz Φ x) * a x i) *
        carrier κ Φ x := by
  have hmode (V : E → E) (i : Fin 3) :
      along V (fun y => vectorMode κ Φ a y i) x =
        (along V (fun y => a y i) x +
          phaseFactor κ * Complex.ofReal (along V Φ x) * a x i) * carrier κ Φ x :=
    along_mode V κ hΦ (ha i)
  have hbase (V : E → E) (i : Fin 3) := along_complexBase V hR hb hF hG i
  have hrad : along Vr (fun y => R y * F y) x = F x + R x * along Vr F x := by
    rw [along_mul_real Vr hR hF, hDr, one_mul]
  have hrC : (R x : ℂ) ≠ 0 := by exact_mod_cast hRx
  ext i
  fin_cases i <;>
    simp only [transport, hmode, hbase, haθ, hBθ, Complex.ofReal_zero,
      zero_add] <;>
    simp [complexBase, base, vectorMode, mode, shear, baseDerivativeRemainder,
      angularGenerator, Complex.ofReal_add, Complex.ofReal_mul, hrad] <;>
    field_simp [hrC] <;> ring

/-- The scalar and frame Laplacian identities assembled into the viscous
braces of (31), with the phase-square term separated. -/
theorem vectorLaplacian_mode_split {U : Set E} (R : E → ℝ)
    {Vr Vθ Vz : E → E} (κ : ℝ) {Φ : E → ℝ} {a : E → ComplexVector} {pθ : ℝ} {x : E}
    (hU : IsOpen U) (hr : ContDiffOn ℝ ∞ Vr U) (hθ : ContDiffOn ℝ ∞ Vθ U)
    (hz : ContDiffOn ℝ ∞ Vz U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun y => a y i) U)
    (haθ : ∀ i, EqOn (along Vθ (fun y => a y i)) (fun _ => 0) U)
    (hΦθ : EqOn (along Vθ Φ) (fun _ => pθ) U) (hx : x ∈ U) :
    cylindricalVectorLaplacian R Vr Vθ Vz (vectorMode κ Φ a) x = fun i =>
      (viscousRemainder R Vr Vθ Vz κ Φ a x i -
        (κ : ℂ) ^ 2 * Complex.ofReal (‖phaseNormal R Vr Vθ Vz Φ x‖ ^ 2) * a x i) *
        carrier κ Φ x := by
  rw [cylindricalVectorLaplacian_vectorMode R κ hU hr hθ hz hΦ ha hx,
    cylindricalVectorLaplacian_angular_independent R Vr Vθ Vz hU haθ hx,
    cylindricalLaplacian_phase R Vr Vθ Vz hU hΦθ hx]
  ext i
  simp [viscousRemainder, phaseCross, haθ i hx, phaseNormal]
  ring

/-- Full identity (31) for the actual amplitude supplied to the linear
operator. The principal and remainder are both explicitly defined above. -/
theorem linearResidual_mode_split {U : Set E} (ε κ : ℝ) (R b F G : E → ℝ)
    {Vr Vθ Vz : E → E} (Vf Vs : E → E) {Φ : E → ℝ} {a : E → ComplexVector}
    {p : E → ℂ} {pθ : ℝ} {x : E}
    (hU : IsOpen U) (hr : ContDiffOn ℝ ∞ Vr U) (hθ : ContDiffOn ℝ ∞ Vθ U)
    (hz : ContDiffOn ℝ ∞ Vz U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun y => a y i) U)
    (hR : DifferentiableAt ℝ R x) (hb : DifferentiableAt ℝ b x)
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x)
    (hRx : R x ≠ 0) (hDr : along Vr R x = 1)
    (hBθ : ∀ i, along Vθ (fun y => base R b F G y i) x = 0)
    (haθ : ∀ i, EqOn (along Vθ (fun y => a y i)) (fun _ => 0) U)
    (hΦθ : EqOn (along Vθ Φ) (fun _ => pθ) U)
    (hp : DifferentiableAt ℝ p x) (hpθ : along Vθ p x = 0) (hx : x ∈ U) :
    linearResidual ε R Vr Vθ Vz (timeDirection ε Vf Vs) (complexBase R b F G)
      (vectorMode κ Φ a) (mode κ Φ p) x = fun i =>
      (principal ε κ R F G Vr Vθ Vz Vf Φ a p x i +
        remainder ε κ R b F G Vr Vθ Vz Vf Vs Φ a p x i) * carrier κ Φ x := by
  have dΦ := (hΦ.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have da i := ((ha i).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hadv := linearAdvection_mode R b F G Vr Vθ Vz κ hR hb hF hG hRx hDr hBθ dΦ da
    (fun i => haθ i hx)
  have hlap := vectorLaplacian_mode_split R κ hU hr hθ hz hΦ ha haθ hΦθ hx
  have hg := gradient_mode R Vr Vθ Vz κ dΦ hp hpθ
  ext i
  have hadvi := congrFun hadv i
  have hlapi := congrFun hlap i
  have hgi := congrFun hg i
  unfold linearResidual
  rw [show along (timeDirection ε Vf Vs) (fun y => vectorMode κ Φ a y i) x =
      (along (timeDirection ε Vf Vs) (fun y => a y i) x +
        phaseFactor κ * Complex.ofReal (along (timeDirection ε Vf Vs) Φ x) * a x i) *
          carrier κ Φ x from along_mode _ κ dΦ (da i)]
  rw [add_assoc _ (transport R Vr Vθ Vz (complexBase R b F G) (vectorMode κ Φ a) x i)
    (transport R Vr Vθ Vz (vectorMode κ Φ a) (complexBase R b F G) x i)]
  rw [hadvi, hlapi, hgi]
  simp only [principal, remainder, slowTransport, materialPhaseDefect, along_timeDirection,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow]
  ring

/-! ## Actual slot phase and projected pressure -/


/-- The material defect used in the residual is the actual backward-time
material derivative already computed in `PhaseCalculus`. -/
theorem materialPhaseDefect_slot (ε p pz x₀ : ℝ) (b F G : PhaseCalculus.Slow → ℝ)
    (q : PhaseCalculus.Slot) (hR : q.1.1 ≠ 0) :
    materialPhaseDefect (fun y : PhaseCalculus.Slot => y.1.1)
      (fun y => b y.1) (fun y => F y.1) (fun y => G y.1)
      (fun _ => PhaseCalculus.eR) (fun _ => PhaseCalculus.eTheta)
      (fun _ => ε • PhaseCalculus.eZ)
      (timeDirection ε (fun _ => PhaseCalculus.eV) (fun _ => PhaseCalculus.eT))
      (PhaseCalculus.phase ε p pz x₀ F G) q =
      PhaseCalculus.backwardMaterialOp ε b F G (PhaseCalculus.phase ε p pz x₀ F G) q := by
  unfold materialPhaseDefect PhaseCalculus.backwardMaterialOp PhaseCalculus.signedMaterialOp
  simp only [along, timeDirection, map_sub, map_smul, smul_eq_mul, PhaseCalculus.baseV]
  field_simp [hR] ; ring

/-- Explicit formula for the phase material defect, including the sign of
the slow-time term. No estimate for this term is assumed. -/
theorem materialPhaseDefect_slot_formula (ε p pz x₀ : ℝ)
    (b F G : PhaseCalculus.Slow → ℝ) (q : PhaseCalculus.Slot)
    (hε : ε ≠ 0) (hR : 0 < q.1.1)
    (hF : DifferentiableAt ℝ F q.1) (hG : DifferentiableAt ℝ G q.1) :
    materialPhaseDefect (fun y : PhaseCalculus.Slot => y.1.1)
      (fun y => b y.1) (fun y => F y.1) (fun y => G y.1)
      (fun _ => PhaseCalculus.eR) (fun _ => PhaseCalculus.eTheta)
      (fun _ => ε • PhaseCalculus.eZ)
      (timeDirection ε (fun _ => PhaseCalculus.eV) (fun _ => PhaseCalculus.eT))
      (PhaseCalculus.phase ε p pz x₀ F G) q =
      b q.1 * x₀ - q.2.2 *
        (b q.1 * (p * PhaseCalculus.slowR F q.1 + pz * PhaseCalculus.slowR G q.1) -
          ε * (p * PhaseCalculus.slowT F q.1 + pz * PhaseCalculus.slowT G q.1) +
          ε * G q.1 * (p * PhaseCalculus.slowZ F q.1 + pz * PhaseCalculus.slowZ G q.1)) := by
  rw [materialPhaseDefect_slot ε p pz x₀ b F G q (ne_of_gt hR)]
  exact PhaseCalculus.backwardMaterialOp_phase ε p pz x₀ b F G q hε hR hF hG

/-- A base coefficient depending only on slow coordinates has precisely
the slow differential along a slot direction. -/
theorem slot_base_derivative (f : PhaseCalculus.Slow → ℝ) (q w : PhaseCalculus.Slot)
    (hf : DifferentiableAt ℝ f q.1) :
    along (fun _ => w) (fun y : PhaseCalculus.Slot => f y.1) q = fderiv ℝ f q.1 w.1 := by
  have hd := (hf.hasFDerivAt.comp q (hasFDerivAt_id (𝕜 := ℝ) q).fst).fderiv
  dsimp only [Function.comp_def] at hd
  unfold along
  rw [hd]
  rfl



/-- Numerator in the pressure from the projected equation. The derivative
of `n` is the actual derivative in the fast direction. -/
noncomputable def projectionNumerator (Vf : E → E) (n : E → EuclideanSpace ℝ (Fin 3))
    (a Ka f : E → ComplexVector) (x : E) : ℂ :=
  normalDot (n x) (Ka x) - normalDot (along Vf n x) (a x) + normalDot (n x) (f x)

noncomputable def projectedPressure (κ : ℝ) (Vf : E → E)
    (n : E → EuclideanSpace ℝ (Fin 3)) (a Ka f : E → ComplexVector) (x : E) : ℂ :=
  (Complex.I / (κ : ℂ)) * projectionNumerator Vf n a Ka f x /
    Complex.ofReal (‖n x‖ ^ 2)

theorem projectedPressure_force (κ : ℝ) (Vf : E → E)
    (n : E → EuclideanSpace ℝ (Fin 3)) (a Ka f : E → ComplexVector) (x : E)
    (hκ : κ ≠ 0) (i : Fin 3) :
    phaseFactor κ * Complex.ofReal (n x i) * projectedPressure κ Vf n a Ka f x =
      -Complex.ofReal (n x i) * projectionNumerator Vf n a Ka f x /
        Complex.ofReal (‖n x‖ ^ 2) := by
  have hk : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ
  have hc : phaseFactor κ * (Complex.I / (κ : ℂ)) = -1 := by
    unfold phaseFactor
    field_simp [hk]
    simp []
  unfold projectedPressure
  calc
    _ = (phaseFactor κ * (Complex.I / (κ : ℂ))) * Complex.ofReal (n x i) *
        projectionNumerator Vf n a Ka f x / Complex.ofReal (‖n x‖ ^ 2) := by ring
    _ = _ := by rw [hc]; ring


theorem contDiffOn_normalDot {U : Set E} {n : E → EuclideanSpace ℝ (Fin 3)}
    {a : E → ComplexVector} (hn : ContDiffOn ℝ ∞ n U)
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun y => a y i) U) :
    ContDiffOn ℝ ∞ (fun y => normalDot (n y) (a y)) U := by
  have hc i : ContDiffOn ℝ ∞ (fun y => Complex.ofReal (n y i)) U :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).contDiff.comp_contDiffOn hn)
  exact (((hc 0).mul (ha 0)).add ((hc 1).mul (ha 1))).add ((hc 2).mul (ha 2))


/-! ## Real-linear transfer of the complex calculation -/

section LinearMaps

variable {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]

theorem along_map (L : F₁ →L[ℝ] F₂) (V : E → E) {f : E → F₁} {x : E}
    (hf : DifferentiableAt ℝ f x) :
    along V (fun y => L (f y)) x = L (along V f x) := by
  have hd := (L.hasFDerivAt.comp x hf.hasFDerivAt).fderiv
  dsimp only [Function.comp_def] at hd
  unfold along
  rw [hd]
  rfl

theorem along_along_map (L : F₁ →L[ℝ] F₂) {U : Set E} {V : E → E}
    {f : E → F₁} {x : E} (hU : IsOpen U) (hV : ContDiffOn ℝ ∞ V U)
    (hf : ContDiffOn ℝ ∞ f U) (hx : x ∈ U) :
    along V (along V (fun y => L (f y))) x = L (along V (along V f) x) := by
  have he : EqOn (along V (fun y => L (f y))) (fun y => L (along V f y)) U := by
    intro y hy
    exact along_map L V ((hf.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
  rw [along_congr hU he hx]
  exact along_map L V
    (((contDiffOn_along hU hV hf).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))

theorem cylindricalLaplacian_map (L : F₁ →L[ℝ] F₂) {U : Set E} (R : E → ℝ)
    {Vr Vθ Vz : E → E} {f : E → F₁} {x : E} (hU : IsOpen U)
    (hr : ContDiffOn ℝ ∞ Vr U) (hθ : ContDiffOn ℝ ∞ Vθ U)
    (hz : ContDiffOn ℝ ∞ Vz U) (hf : ContDiffOn ℝ ∞ f U) (hx : x ∈ U) :
    cylindricalLaplacian R Vr Vθ Vz (fun y => L (f y)) x =
      L (cylindricalLaplacian R Vr Vθ Vz f x) := by
  simp only [cylindricalLaplacian, along_along_map L hU hr hf hx,
    along_along_map L hU hθ hf hx, along_along_map L hU hz hf hx,
    along_map L Vr ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)),
    map_add, map_smul]

end LinearMaps

noncomputable def realLift (a : E → Fin 3 → ℝ) (x : E) : ComplexVector := fun i => (a x i : ℂ)

noncomputable def realAngularGenerator (a : Fin 3 → ℝ) : Fin 3 → ℝ := ![-a 1, a 0, 0]

noncomputable def realTransport (R : E → ℝ) (Vr Vθ Vz : E → E)
    (u v : E → Fin 3 → ℝ) (x : E) : Fin 3 → ℝ := fun i =>
  u x 0 * along Vr (fun y => v y i) x +
    (u x 1 / R x) * (along Vθ (fun y => v y i) x + realAngularGenerator (v x) i) +
    u x 2 * along Vz (fun y => v y i) x

noncomputable def realFrameLaplacian (R : E → ℝ) (Vr Vθ Vz : E → E)
    (a : E → Fin 3 → ℝ) (x : E) : Fin 3 → ℝ := fun i =>
  cylindricalLaplacian R Vr Vθ Vz (fun y => a y i) x + ((R x) ^ 2)⁻¹ *
    (2 * realAngularGenerator (fun j => along Vθ (fun y => a y j) x) i +
      realAngularGenerator (realAngularGenerator (a x)) i)

/-- Real component form of the same differential linearization. -/
noncomputable def realComponentLinearResidual (ε : ℝ) (R : E → ℝ) (Vr Vθ Vz Vt : E → E)
    (B a : E → Fin 3 → ℝ) (p : E → ℝ) (x : E) : Fin 3 → ℝ := fun i =>
  along Vt (fun y => a y i) x + realTransport R Vr Vθ Vz B a x i +
    realTransport R Vr Vθ Vz a B x i +
    (![along Vr p x, (R x)⁻¹ * along Vθ p x, along Vz p x] i) -
    ε * realFrameLaplacian R Vr Vθ Vz a x i

theorem map_ofReal_mul (L : ℂ →L[ℝ] ℝ) (r : ℝ) (z : ℂ) :
    L ((r : ℂ) * z) = r * L z := by
  change L (r • z) = _
  rw [map_smul]
  rfl

theorem map_mul_ofReal (L : ℂ →L[ℝ] ℝ) (r : ℝ) (z : ℂ) :
    L (z * (r : ℂ)) = L z * r := by
  rw [mul_comm, map_ofReal_mul]
  ring

theorem map_div_ofReal (L : ℂ →L[ℝ] ℝ) (r : ℝ) (z : ℂ) :
    L (z / (r : ℂ)) = L z / r := by
  rw [div_eq_mul_inv, ← Complex.ofReal_inv, map_mul_ofReal, div_eq_mul_inv]

theorem map_two_mul (L : ℂ →L[ℝ] ℝ) (z : ℂ) : L (2 * z) = 2 * L z :=
  map_ofReal_mul L 2 z

/-- The complex linearization transfers through any real continuous linear
functional, in particular real and imaginary parts, because its base is real. -/
theorem realMap_linearResidual {U : Set E} (L : ℂ →L[ℝ] ℝ) (ε : ℝ) (R : E → ℝ)
    {Vr Vθ Vz : E → E} (Vt : E → E) {B : E → Fin 3 → ℝ}
    {a : E → ComplexVector} {p : E → ℂ} {x : E}
    (hU : IsOpen U) (hr : ContDiffOn ℝ ∞ Vr U) (hθ : ContDiffOn ℝ ∞ Vθ U)
    (hz : ContDiffOn ℝ ∞ Vz U) (ha : ∀ i, ContDiffOn ℝ ∞ (fun y => a y i) U)
    (hB : ∀ i, DifferentiableAt ℝ (fun y => B y i) x)
    (hp : DifferentiableAt ℝ p x) (hx : x ∈ U) :
    (fun i => L (linearResidual ε R Vr Vθ Vz Vt (realLift B) a p x i)) =
      realComponentLinearResidual ε R Vr Vθ Vz Vt B
        (fun y i => L (a y i)) (fun y => L (p y)) x := by
  have da i := ((ha i).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hD (V : E → E) (i : Fin 3) := along_map L V (da i)
  have hDB (V : E → E) (i : Fin 3) := along_ofReal V (hB i)
  have hLap i := cylindricalLaplacian_map L R hU hr hθ hz (ha i) hx
  ext i
  fin_cases i <;>
    simp [linearResidual, realComponentLinearResidual, transport, realTransport, realLift,
      gradient, cylindricalVectorLaplacian, realFrameLaplacian, angularGenerator,
      realAngularGenerator, hD, hDB, hLap, along_map L _ hp,
      ← Complex.ofReal_div, map_ofReal_mul, map_mul_ofReal, map_add,
      map_sub, map_neg, Complex.real_smul] <;>
    simp only [← Complex.ofReal_neg, ← Complex.ofReal_add, ← Complex.ofReal_pow,
      ← Complex.ofReal_inv, map_ofReal_mul, map_mul_ofReal, map_div_ofReal, map_two_mul,
      true_or] <;> ring

/-! ## The actual Cartesian and cylindrical linearizations -/

open ProblemStatement

noncomputable def bilinearAdvection (u v : Space → Space) (q : Space) : Space :=
  u q 0 • CylindricalResidual.dCoord 0 v q +
    (u q 1 / q 0) • (CylindricalResidual.dCoord 1 v q + CylindricalResidual.connection (v q)) +
    u q 2 • CylindricalResidual.dCoord 2 v q

noncomputable def cylindricalLinearResidual (ε : ℝ) (B a : VelocityField) (p : PressureField)
    (t : ℝ) (q : Space) : Space :=
  temporalDerivative a t q + bilinearAdvection (fun y => B (t, y)) (fun y => a (t, y)) q +
    bilinearAdvection (fun y => a (t, y)) (fun y => B (t, y)) q +
    CylindricalResidual.scalarGradient (fun y => p (t, y)) q -
    ε • CylindricalResidual.vectorLaplacian (fun y => a (t, y)) q

/-- Linearization in the original Cartesian derivative definitions. -/
noncomputable def cartesianLinearResidual (ε : ℝ) (B a : VelocityField) (p : PressureField)
    (t : ℝ) (x : Space) : Space :=
  temporalDerivative a t x + spatialDerivative a t x (B (t, x)) +
    spatialDerivative B t x (a (t, x)) + pressureGradient p t x -
    ε • spatialLaplacian a t x

theorem cartesianBilinearAdvection_components {u v : Space → Space} {q : Space}
    (hv : DifferentiableAt ℝ v (CylindricalResidual.chart q)) (hr : q 0 ≠ 0) :
    fderiv ℝ v (CylindricalResidual.chart q) (u (CylindricalResidual.chart q)) =
      CylindricalResidual.frame (q 1)
        (bilinearAdvection (CylindricalResidual.components u) (CylindricalResidual.components v) q) := by
  have he := CylindricalResidual.cartesianDerivative_components hv hr
    (CylindricalResidual.components u q)
  have hu : CylindricalResidual.frame (q 1) (CylindricalResidual.components u q) =
      u (CylindricalResidual.chart q) := CylindricalResidual.frame_inverse' _ _
  rw [hu] at he
  have he' := congrArg (CylindricalResidual.frame (q 1)) he
  simp only [CylindricalResidual.frame_inverse'] at he'
  exact he'


noncomputable def spaceDirection (i : Fin 3) (_ : SpaceTime) : SpaceTime :=
  (0, coordinateVector i)

noncomputable def physicalTimeDirection (_ : SpaceTime) : SpaceTime := (1, 0)

noncomputable def coordinateRadius (x : SpaceTime) : ℝ := x.2 0

section Slices

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem along_space_slice {f : SpaceTime → W} {t : ℝ} {q : Space}
    (hf : DifferentiableAt ℝ f (t, q)) (i : Fin 3) :
    along (spaceDirection i) f (t, q) = CylindricalResidual.dCoord i (fun y => f (t, y)) q := by
  have hd := (hf.hasFDerivAt.comp q (hasFDerivAt_prodMk_right t q)).fderiv
  dsimp only [Function.comp_def] at hd
  unfold along CylindricalResidual.dCoord spaceDirection
  rw [hd]
  rfl

theorem along_time_slice {f : SpaceTime → W} {t : ℝ} {q : Space}
    (hf : DifferentiableAt ℝ f (t, q)) :
    along physicalTimeDirection f (t, q) = fderiv ℝ (fun s => f (s, q)) t 1 := by
  have hd := (hf.hasFDerivAt.comp t (hasFDerivAt_prodMk_left (𝕜 := ℝ) t q)).fderiv
  dsimp only [Function.comp_def] at hd
  unfold along physicalTimeDirection
  rw [hd]
  rfl

theorem along_space_space_slice {U : Set SpaceTime} {f : SpaceTime → W} {t : ℝ} {q : Space}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hx : (t, q) ∈ U) (i : Fin 3) :
    along (spaceDirection i) (along (spaceDirection i) f) (t, q) =
      CylindricalResidual.dCoord i (CylindricalResidual.dCoord i (fun y => f (t, y))) q := by
  have hd := contDiffOn_along hU (show ContDiffOn ℝ ∞ (spaceDirection i) U from contDiffOn_const) hf
  rw [along_space_slice ((hd.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))]
  apply CylindricalResidual.dCoord_congr
  have hn : {y : Space | (t, y) ∈ U} ∈ 𝓝 q :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hU.mem_nhds hx)
  filter_upwards [hn] with y hy
  exact along_space_slice ((hf.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)) i

theorem laplacian_space_slice {U : Set SpaceTime} {f : SpaceTime → W} {t : ℝ} {q : Space}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hx : (t, q) ∈ U) :
    cylindricalLaplacian coordinateRadius (spaceDirection 0) (spaceDirection 1) (spaceDirection 2)
      f (t, q) = CylindricalResidual.scalarLaplacian (fun y => f (t, y)) q := by
  unfold cylindricalLaplacian CylindricalResidual.scalarLaplacian coordinateRadius
  rw [along_space_space_slice hU hf hx 0, along_space_space_slice hU hf hx 1,
    along_space_space_slice hU hf hx 2,
    along_space_slice ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)) 0]

end Slices


end NavierStokes.LinearWaveResidual
