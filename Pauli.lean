import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral

/-! A compactly supported family with identical position and momentum distributions.
The Fourier variable below is angular frequency. Integrals use Lebesgue measure. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate BigOperators

namespace Pauli
def cis (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * Complex.I)
@[simp] theorem norm_cis (x : ℝ) : ‖cis x‖ = 1 := Complex.abs_exp_ofReal_mul_I x
@[simp] theorem cis_zero : cis 0 = 1 := by simp [cis]
@[simp] theorem abs_cis (x : ℝ) : Complex.abs (cis x) = 1 := norm_cis x
theorem cis_add (x y : ℝ) : cis (x+y) = cis x * cis y := by
  simp [cis, add_mul, Complex.exp_add]
theorem conj_cis (x : ℝ) : conj (cis x) = cis (-x) := by
  simp [cis, ← Complex.exp_conj]
theorem cis_cont : Continuous cis := by unfold cis; fun_prop

def digit (x : ℝ) : ℝ := if x ≤ 1/3 then 0 else if x ≤ 2/3 then 1 else 2
def shift (x : ℝ) : ℝ := 3*x - digit x
def mark (x : ℝ) : ℝ := if digit x = 1 then 1 else 0
theorem digit_meas : Measurable digit := by
  unfold digit
  apply Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const
  exact Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const measurable_const
theorem shift_meas : Measurable shift :=
  (measurable_const.mul measurable_id).sub digit_meas
theorem mark_meas : Measurable mark :=
  Measurable.ite (measurableSet_eq_fun digit_meas measurable_const) measurable_const measurable_const

def term (a : ℕ → ℝ) (j : ℕ) (x : ℝ) := a j * mark (shift^[j] x)
def phase (n : ℕ) (a : ℕ → ℝ) (x : ℝ) := ∑ j ∈ Finset.range n, term a j x
def tail (a : ℕ → ℝ) (j : ℕ) := a (j+1)
theorem phase_succ (n : ℕ) (a : ℕ → ℝ) (x : ℝ) :
    phase (n+1) a x = a 0 * mark x + phase n (tail a) (shift x) := by
  simp [phase, Finset.sum_range_succ', term, Function.iterate_succ_apply, tail, add_comm]
theorem phase_meas (n : ℕ) (a : ℕ → ℝ) : Measurable (phase n a) := by
  apply Finset.measurable_sum
  intro j _
  exact measurable_const.mul (mark_meas.comp (shift_meas.iterate j))

def moment (h : ℝ → ℝ) (t : ℝ) : ℂ := ∫ x in (0:ℝ)..1, cis (h x + t*x)
def partialMoment (n : ℕ) (a : ℕ → ℝ) (t : ℝ) := moment (phase n a) t
def factor (s u : ℝ) := (1 + cis (s+u) + cis (2*u))/3

private theorem cell (F G : ℝ → ℂ) (c : ℂ) (r : ℝ)
    (h : ∀ x ∈ Ioc (r/3) ((r+1)/3), F x = c * G (3*x-r)) :
    (intervalIntegral F (r/3) ((r+1)/3) volume) = c * (∫ y in (0:ℝ)..1, G y) / 3 := by
  calc
    _ = intervalIntegral (fun x => c * G (3*x-r)) (r/3) ((r+1)/3) volume := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with x hx
      exact h x ((uIoc_of_le (by linarith : r/3 ≤ (r+1)/3)) ▸ hx)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_sub G (by norm_num)]
      rw [show 3*(r/3)-r = 0 by ring, show 3*((r+1)/3)-r = 1 by ring]
      simp [Complex.real_smul, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

theorem partial_succ (n : ℕ) (a : ℕ → ℝ) (t : ℝ) :
    partialMoment (n+1) a t = factor (a 0) (t/3) * partialMoment n (tail a) (t/3) := by
  let F := fun x : ℝ => cis (phase (n+1) a x + t*x)
  let G := fun x : ℝ => cis (phase n (tail a) x + (t/3)*x)
  have hint (p q : ℝ) : IntervalIntegrable F volume p q := by
    apply (intervalIntegrable_const (c := (1:ℝ))).mono_fun
    · exact (cis_cont.measurable.comp ((phase_meas ..).add (measurable_const.mul measurable_id))).aestronglyMeasurable
    · filter_upwards [] with x; simp [F]
  have onCell (r : ℝ) (hr : r = 0 ∨ r = 1 ∨ r = 2) :
      (intervalIntegral F (r/3) ((r+1)/3) volume) =
        cis ((if r = 1 then a 0 else 0) + t/3*r) * (∫ y in (0:ℝ)..1, G y) / 3 := by
    apply cell F G _ r
    intro x hx
    have hd : digit x = r := by
      rcases hx with ⟨hl,hh⟩
      rcases hr with rfl | rfl | rfl <;> unfold digit <;> split_ifs <;> linarith
    dsimp only [F,G]
    rw [← cis_add, phase_succ]
    simp only [shift, mark, hd]
    split_ifs <;> ring_nf
  have h0 := onCell 0 (Or.inl rfl)
  have h1 := onCell 1 (Or.inr (Or.inl rfl))
  have h2 := onCell 2 (Or.inr (Or.inr rfl))
  norm_num at h0 h1 h2
  change (∫ x in (0:ℝ)..1, F x) = factor _ _ * ∫ x in (0:ℝ)..1, G x
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 (2/3)) (hint (2/3) 1),
      ← intervalIntegral.integral_add_adjacent_intervals (hint 0 (1/3)) (hint (1/3) (2/3))]
  unfold factor
  rw [h0,h1,h2]
  ring_nf


theorem factor_le (s u : ℝ) : ‖factor s u‖ ≤ 1 := by
  have h := norm_add_le (1 + cis (s+u)) (cis (2*u))
  have h' := norm_add_le (1:ℂ) (cis (s+u))
  change ‖(1 + cis (s+u) + cis (2*u)) / (3:ℂ)‖ ≤ 1
  rw [norm_div]
  norm_num at h h' ⊢
  linarith

theorem factor_neg (s u : ℝ) : ‖factor (-s) u‖ = ‖factor s u‖ := by
  have h : factor (-s) u = cis (2*u) * conj (factor s u) := by
    unfold factor
    simp only [map_div₀, map_add, map_one, map_ofNat, conj_cis, mul_div_assoc']
    congr 1
    rw [mul_add, mul_add, mul_one, ← cis_add, ← cis_add]
    rw [show 2*u + -(s+u) = -s+u by ring, add_neg_cancel, cis_zero]
    ring
  rw [h,norm_mul,norm_cis,one_mul]
  exact Complex.abs_conj _

theorem partial_mod (n : ℕ) (a b : ℕ → ℝ) (t : ℝ)
    (h : ∀ j, b j = a j ∨ b j = -a j) :
    ‖partialMoment n b t‖ = ‖partialMoment n a t‖ := by
  induction n generalizing a b t with
  | zero => simp [partialMoment,moment,phase]
  | succ n ih =>
    rw [partial_succ,partial_succ,norm_mul,norm_mul,ih (tail a) (tail b) (t/3) (fun j => h (j+1))]
    rcases h 0 with e | e
    · rw [e]
    · rw [e,factor_neg]

def infinitePhase (a : ℕ → ℝ) (x : ℝ) := ∑' j, term a j x
theorem summable_terms {a : ℕ → ℝ} (ha : Summable a) (x : ℝ) :
    Summable (fun j => term a j x) := by
  apply Summable.of_norm_bounded _ ha.norm
  intro j
  simp only [term,mark]
  split_ifs <;> simp

theorem phase_lim {a : ℕ → ℝ} (ha : Summable a) (x : ℝ) :
    Tendsto (fun n => phase n a x) atTop (𝓝 (infinitePhase a x)) :=
  (summable_terms ha x).hasSum.tendsto_sum_nat

theorem infinite_meas {a : ℕ → ℝ} (ha : Summable a) : Measurable (infinitePhase a) :=
  measurable_of_tendsto_metrizable (fun n => phase_meas n a) (tendsto_pi_nhds.mpr (phase_lim ha))

theorem moment_lim {a : ℕ → ℝ} (ha : Summable a) (t : ℝ) :
    Tendsto (fun n => partialMoment n a t) atTop (𝓝 (moment (infinitePhase a) t)) := by
  simp only [partialMoment,moment,intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]
  apply tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ))
  · intro n
    exact (cis_cont.measurable.comp ((phase_meas n a).add (measurable_const.mul measurable_id))).aestronglyMeasurable
  · exact (intervalIntegrable_const (c := (1:ℝ)) (a := (0:ℝ)) (b := 1) (μ := volume)).1
  · intro n
    filter_upwards [] with x
    simp
  · filter_upwards [] with x
    exact cis_cont.continuousAt.tendsto.comp ((phase_lim ha x).add tendsto_const_nhds)

theorem infinite_mod {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b)
    (h : ∀ j, b j = a j ∨ b j = -a j) (t : ℝ) :
    ‖moment (infinitePhase b) t‖ = ‖moment (infinitePhase a) t‖ := by
  apply tendsto_nhds_unique (moment_lim hb t).norm
  exact (moment_lim ha t).norm.congr (fun n => (partial_mod n a b t h).symm)

theorem partial_bound (n : ℕ) (a : ℕ → ℝ) (t : ℝ) : ‖partialMoment n a t‖ ≤ 1 := by
  simpa [partialMoment,moment] using
    (intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1) (C := 1)
       (f := fun x => cis (phase n a x + t*x)) (fun x _ => (norm_cis _).le))

theorem partial_gap (k n : ℕ) (h : k < n) (a : ℕ → ℝ) :
    ‖partialMoment n a 0‖ ≤ ‖factor (a k) 0‖ := by
  induction k generalizing n a with
  | zero =>
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [partial_succ,zero_div,norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (partial_bound ..)
  | succ k ih =>
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [partial_succ,zero_div,norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (factor_le ..)).trans (ih m (by omega) (tail a))

theorem infinite_gap {a : ℕ → ℝ} (ha : Summable a) (k : ℕ) :
    ‖moment (infinitePhase a) 0‖ ≤ ‖factor (a k) 0‖ := by
  apply le_of_tendsto (moment_lim ha 0).norm
  filter_upwards [eventually_gt_atTop k] with n hn using partial_gap k n hn a

theorem factor_strict {s : ℝ} (h : 0 < s) (hp : s ≤ Real.pi) : ‖factor s 0‖ < 1 := by
  have hc : Real.cos s < 1 := by simpa using Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) le_rfl hp h
  have hs := Real.sin_sq_add_cos_sq s
  have hn := Complex.sq_abs (2 + cis s)
  have hre : (cis s).re = Real.cos s := by simp [cis,Complex.exp_re]
  have him : (cis s).im = Real.sin s := by simp [cis,Complex.exp_im]
  rw [Complex.normSq_apply] at hn
  simp [hre,him] at hn
  have hz : Complex.abs (2+cis s) < 3 := by nlinarith
  have he : factor s 0 = (2+cis s)/3 := by simp [factor]; ring
  rw [he, norm_div]
  change Complex.abs (2+cis s) / Complex.abs (3:ℂ) < 1
  norm_num
  linarith


def amp (s : ℕ → Bool) (j : ℕ) : ℝ :=
  if s j then (1/2:ℝ)^(j+1) else -((1/2:ℝ)^(j+1))

theorem amp_sum (s : ℕ → Bool) : Summable (amp s) := by
  apply Summable.of_norm_bounded _ summable_geometric_two
  intro j
  have h : 0 ≤ (1/2:ℝ)^j := by positivity
  have hm : 0 ≤ (1/2:ℝ)^(j+1) := by positivity
  have hb : (1/2:ℝ)^(j+1) ≤ (1/2:ℝ)^j := by
    rw [pow_succ]
    linarith
  unfold amp
  split_ifs <;> simpa only [Real.norm_eq_abs, abs_neg, abs_of_nonneg hm] using hb

def box : Set ℝ := Ioc 0 1
def wave (s : ℕ → Bool) : ℝ → ℂ := box.indicator (fun x => cis (infinitePhase (amp s) x))
/-- Angular-frequency Fourier transform on the real line. -/
def fourier (f : ℝ → ℂ) (t : ℝ) := ∫ x : ℝ, f x * cis (-t*x)

theorem wave_mod (s : ℕ → Bool) (x : ℝ) :
    ‖wave s x‖ = box.indicator (fun _ => (1:ℝ)) x := by
  by_cases h : x ∈ box <;> simp [wave,h]

theorem wave_L2 (s : ℕ → Bool) : Memℒp (wave s) 2 volume := by
  rw [wave, box, memℒp_indicator_iff_restrict measurableSet_Ioc]
  exact Memℒp.of_bound ((cis_cont.measurable.comp (infinite_meas (amp_sum s))).aestronglyMeasurable)
    1 (Eventually.of_forall fun x => (norm_cis _).le)

theorem wave_normalized (s : ℕ → Bool) : (∫ x : ℝ, ‖wave s x‖ ^ 2) = 1 := by
  simp_rw [wave_mod]
  have h : (fun x => (box.indicator (fun _ => (1:ℝ)) x)^2) = box.indicator (fun _ => (1:ℝ)) := by
    funext x; by_cases hx : x ∈ box <;> simp [hx]
  rw [h, box, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  simp

theorem wave_FT (s : ℕ → Bool) (t : ℝ) : fourier (wave s) t = moment (infinitePhase (amp s)) (-t) := by
  unfold fourier wave moment
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases h : x ∈ box
  · simpa [box] using (show box.indicator (fun x => cis (infinitePhase (amp s) x)) x * cis (-t*x) =
        box.indicator (fun x => cis (infinitePhase (amp s) x + -t*x)) x by simp [h,cis_add])
  · simp_all [box]

theorem wave_FT_mod (s u : ℕ → Bool) (t : ℝ) : ‖fourier (wave s) t‖ = ‖fourier (wave u) t‖ := by
  simp only [wave_FT]
  apply infinite_mod (amp_sum u) (amp_sum s)
  intro j
  cases hs : s j <;> cases hu : u j <;> simp [amp,hs,hu]

theorem wave_separate {s u : ℕ → Bool} (hsu : s ≠ u) (c : ℂ) (hc : ‖c‖ = 1) :
    ¬ (wave s =ᵐ[volume] fun x => c * wave u x) := by
  intro he
  let a := amp s
  let b := amp u
  let v := fun j => a j - b j
  have hv : Summable v := (amp_sum s).sub (amp_sum u)
  have hsub (x : ℝ) : infinitePhase v x = infinitePhase a x - infinitePhase b x := by
    unfold infinitePhase
    rw [← tsum_sub (summable_terms (amp_sum s) x) (summable_terms (amp_sum u) x)]
    congr 1
    funext j
    simp [term,v,a,b,sub_mul]
  have hav : moment (infinitePhase v) 0 = c := by
    unfold moment
    calc
      _ = ∫ x in (0:ℝ)..1, c := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [he] with x hx hmem
        rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hmem
        change x ∈ box at hmem
        simp [wave,hmem] at hx
        simp only [zero_mul,add_zero,hsub,sub_eq_add_neg,cis_add]
        change cis (infinitePhase (amp s) x) * cis (-infinitePhase (amp u) x) = c
        rw [hx,mul_assoc,← cis_add,add_neg_cancel,cis_zero,mul_one]
      _ = c := by simp
  obtain ⟨k,hk⟩ : ∃ k, s k ≠ u k := Function.ne_iff.mp hsu
  let m := (1/2:ℝ)^(k+1)
  have hm : 0 < m := by dsimp [m]; positivity
  have hm1 : m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hpi : 2*m ≤ Real.pi := by linarith [Real.two_le_pi]
  have hsign : v k = 2*m ∨ v k = -(2*m) := by
    cases hs : s k <;> cases hu : u k <;> simp_all [v,a,b,amp,m] <;> ring_nf <;> tauto
  have hlt : ‖factor (v k) 0‖ < 1 := by
    rcases hsign with h | h
    · rw [h]; exact factor_strict (by positivity) hpi
    · rw [h,factor_neg]; exact factor_strict (by positivity) hpi
  have hab := infinite_gap hv k
  rw [hav,hc] at hab
  linarith

/-- Explicit continuum-indexed compact-support Pauli counterexample.
Distinct indices denote distinct physical rays, even up to almost-everywhere equality. -/
theorem shkarin_counterexample :
    ∃ F : (ℕ → Bool) → ℝ → ℂ,
      (∀ s, Memℒp (F s) 2 volume ∧ (∫ x : ℝ, ‖F s x‖^2) = 1) ∧
      (∀ s x, ‖F s x‖ = (Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) x) ∧
      (∀ s u t, ‖fourier (F s) t‖ = ‖fourier (F u) t‖) ∧
      (∀ s u, s ≠ u → ∀ c : ℂ, ‖c‖ = 1 → ¬ (F s =ᵐ[volume] fun x => c * F u x)) :=
  ⟨wave, fun s => ⟨wave_L2 s,wave_normalized s⟩,wave_mod,wave_FT_mod,
    fun _ _ h c hc => wave_separate h c hc⟩

/-- No sequence of real-line wave functions can enumerate these states modulo global phase. -/
theorem no_countable_enumeration (g : ℕ → ℝ → ℂ) :
    ∃ s : ℕ → Bool, ∀ n (c : ℂ), ‖c‖ = 1 →
      ¬ (wave s =ᵐ[volume] fun x => c * g n x) := by
  classical
  let Represents (n : ℕ) (s : ℕ → Bool) :=
    ∃ c : ℂ, ‖c‖ = 1 ∧ (wave s =ᵐ[volume] fun x => c * g n x)
  let pick (n : ℕ) : ℕ → Bool :=
    if h : ∃ s, Represents n s then h.choose else fun _ => false
  let diagonal (n : ℕ) := !(pick n n)
  refine ⟨diagonal, ?_⟩
  intro n c hc he
  have h : ∃ s, Represents n s := ⟨diagonal,c,hc,he⟩
  have hp : Represents n (pick n) := by
    simpa only [pick, dif_pos h] using h.choose_spec
  obtain ⟨d,hd,hde⟩ := hp
  have hne : diagonal ≠ pick n := by
    intro hEq
    have hn := congrFun hEq n
    change Bool.not (pick n n) = pick n n at hn
    cases heq : pick n n <;> simp [heq] at hn
  apply wave_separate hne (c * d⁻¹) (by simp [norm_mul,norm_inv,hc,hd])
  have hd0 : d ≠ 0 := by
    intro hdZero
    simp [hdZero] at hd
  filter_upwards [he,hde] with x hx hy
  calc
    wave diagonal x = c * g n x := hx
    _ = (c * d⁻¹) * wave (pick n) x := by
      rw [hy, mul_assoc c, ← mul_assoc d⁻¹, inv_mul_cancel₀ hd0, one_mul]

end Pauli

#print axioms Pauli.shkarin_counterexample
#print axioms Pauli.no_countable_enumeration
