import Mathlib

set_option maxHeartbeats 200000


open Classical BigOperators Topology Filter Nat Finset Metric Real ENNReal NNReal

def CondConvergesTo [AddCommMonoid α] [UniformSpace α] (f : ℕ → α) (a : α) : Prop :=
  Tendsto (fun s => ∑ i in range s, f i) atTop (𝓝 a)

def HasCondSum [AddCommMonoid α] [UniformSpace α] (f : ℕ → α) : Prop :=
  ∃ a, CondConvergesTo f a

noncomputable def get_sum [AddCommMonoid α] [UniformSpace α] {f : ℕ → α} (hs : HasCondSum f) : α := Classical.choose hs

theorem sum_of_nonneg_is_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hs : HasCondSum f) : 0 ≤ get_sum hs := by
  lift f to ℕ → ℝ≥0 using fun i => hf i
  let a := get_sum hs
  let ha := Classical.choose_spec hs
  rw [CondConvergesTo] at ha
  have hb : Tendsto (fun s => ↑(∑ i in range s, f i)) atTop (𝓝 a) := by
    have kek : (fun s => ↑(∑ i in range s, f i)) = (fun s => ∑ i in range s, (↑(f i) : ℝ)) := by
      apply funext
      intro x
      exact NNReal.coe_sum
    have hc := ha
    rw [← kek] at hc
    exact hc
  have hc := NNReal.tendsto_coe'.1 hb
  let ⟨hp,_hq⟩ := hc
  exact hp

def AbsolutelyConverges [Norm β] (f : ℕ → β) : Prop := HasCondSum (fun i => ‖f i‖)

theorem HasCondSum.of_summable [AddCommMonoid α] [UniformSpace α] (f : ℕ → α) (hf : Summable f) : HasCondSum f := by
  rw [HasCondSum]
  constructor
  rw [CondConvergesTo]
  exact HasSum.tendsto_sum_nat  hf.hasSum

theorem Summable.of_pos_of_conv (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (hs : HasCondSum f)
    : Summable f := by
  apply HasSum.summable
  rw [HasSum]
  lift f to ℕ → ℝ≥0 using fun i => hf i
  have hk : (fun s => ∑ b in s, (fun i => (↑(f i) : ℝ)) b) = (fun s => ↑(∑ b in s, f b)) := by
    apply funext
    intro x
    simp
    exact NNReal.coe_sum.symm
  rw [hk]
  swap
  · intro f
    intro _hf
    intro hs
    exact get_sum hs
  rw [NNReal.tendsto_coe']
  constructor
  swap
  · exact sum_of_nonneg_is_nonneg hf hs
  rw [← HasSum]
  apply NNReal.hasSum_iff_tendsto_nat.2
  let a := get_sum hs
  let ha := Classical.choose_spec hs
  rw [CondConvergesTo] at ha
  have hb : Tendsto (fun s => ↑(∑ i in range s, f i)) atTop (𝓝 a) := by
    have kek : (fun s => ↑(∑ i in range s, f i)) = (fun s => ∑ i in range s, (↑(f i) : ℝ)) := by
      apply funext
      intro x
      exact NNReal.coe_sum
    have hc := ha
    rw [← kek] at hc
    exact hc
  have hc := NNReal.tendsto_coe'.1 hb
  let ⟨hp,hq⟩ := hc
  have ht : (fun a => ∑ i in range a, f i) = (fun n => ∑ i in range n, f i) := by simp
  rw [ht] at hq
  exact hq

theorem Summable.of_abs_conv [SeminormedAddCommGroup β] [CompleteSpace β] (f : ℕ → β) (hf: AbsolutelyConverges f) : Summable f := by
  apply Summable.of_norm
  rw [AbsolutelyConverges] at hf
  apply Summable.of_pos_of_conv
  · intro n
    exact norm_nonneg (f n)
  exact hf

theorem AbsolutelyConverges.of_nonneg (f : ℕ → ℝ) (hfpos : ∀ n, 0 ≤ f n)
    (hfsum : HasCondSum f) :
  AbsolutelyConverges f := by
  have hg : f = (fun i => ‖f i‖) := by
    apply funext
    intro x
    rw [norm_eq_abs]
    rw [abs_eq_self.2]
    exact hfpos x
  rw [AbsolutelyConverges, ← hg]
  exact hfsum

theorem HasCondSum.of_const_mul (f : ℕ → ℝ) (C : ℝ) (hf : HasCondSum f) :
    HasCondSum (fun i => C * f i) := by
  rw [HasCondSum]
  let ⟨a, ha⟩ := hf
  constructor
  rw [CondConvergesTo]
  have hk : (fun s => ∑ i in range s, C * f i) = (fun s => C * ∑ i in range s, f i) := by
    apply funext
    intro x
    symm
    exact mul_sum (range x) (fun i => f i) C
  rw [hk]
  apply Filter.Tendsto.const_mul
  exact ha

theorem AbsolutelyConverges.of_nonpos (f : ℕ → ℝ) (hfneg : ∀ n, f n ≤ 0)
    (hfsum : HasCondSum f) :
  AbsolutelyConverges f := by
  rw [AbsolutelyConverges]
  have hk : (fun i => ‖f i‖) = (fun i => -1 * f i) := by
    apply funext
    intro x
    rw [← neg_eq_neg_one_mul]
    rw [norm_eq_abs]
    rw [abs_eq_neg_self.2]
    exact hfneg x
  rw [hk]
  apply HasCondSum.of_const_mul
  exact hfsum

theorem Summable.of_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hs : HasCondSum f) : Summable f := by
  apply Summable.of_abs_conv
  apply AbsolutelyConverges.of_nonneg
  exact hf
  exact hs

theorem cconv_of_nonneg_of_le
    {f : ℕ → ℝ} {g : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (hfg : ∀ n, f n ≤ g n) (hs : HasCondSum g)
    : HasCondSum f := by
  have hg : ∀ n, 0 ≤ g n := by
    intro n
    calc
      0 ≤ f n := hf n
      f n ≤ g n := hfg n
  have hfs : Summable g := Summable.of_nonneg hg hs
  apply HasCondSum.of_summable
  apply Summable.of_norm_bounded
  exact hfs
  intro i
  rw [norm_eq_abs, (abs_eq_self.2 (hf i))]
  exact hfg i


theorem not_cconv_of_nonneg_of_le {f : ℕ → ℝ} {g : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (hfg : ∀ n, f n ≤ g n) (nhs : ¬ HasCondSum f)
    : ¬ HasCondSum g := by
  by_contra nh
  exact nhs (cconv_of_nonneg_of_le hf hfg nh)


theorem epsilon_def [NormedAddCommGroup α] {f : ℕ → α} {b : α} :
    CondConvergesTo f b ↔ ∀ (ε : ℝ), 0 < ε → ∃ N, ∀ n, N ≤ n → ‖(fun s => (∑ i in range s, f i)) n - b‖ < ε := by
  let g := fun s => ∑ i in range s, f i
  have hg : g = (fun s => ∑ i in range s, f i) := by exact rfl
  rw [← hg]
  exact NormedAddCommGroup.tendsto_atTop

theorem cauchy_criterion [NormedAddCommGroup α] [CompleteSpace α] {f : ℕ → α} :
    HasCondSum f ↔ CauchySeq (fun s => (∑ i in range s, f i)) := by
  simp_rw [HasCondSum]
  constructor
  · intro ⟨a, ha⟩
    have hb := epsilon_def.1 ha
    apply Metric.cauchySeq_iff'.2
    intro ε
    intro hε
    have hb := hb (ε / 2)
    have hε : 0 < ε / 2 := by exact half_pos hε
    have hb := hb hε
    let ⟨N, hN⟩ := hb
    constructor
    swap
    exact N
    intro n
    have hN1 := hN N
    have hN2 := hN n
    intro hnN
    have hN1 := hN1 (Nat.le_refl N)
    have hN2 := hN2 hnN
    calc
      Dist.dist (∑ i in range n, f i) (∑ i in range N, f i) <= Dist.dist (∑ i in range n, f i) a + Dist.dist a (∑ i in range N, f i) := by
        exact dist_triangle (∑ i in range n, f i) a (∑ i in range N, f i)
      Dist.dist (∑ i in range n, f i) a + Dist.dist a (∑ i in range N, f i) = Dist.dist (∑ i in range n, f i) a + Dist.dist (∑ i in range N, f i) a := by
        simp
        exact _root_.dist_comm a (∑ i in range N, f i)
      Dist.dist (∑ i in range n, f i) a + Dist.dist (∑ i in range N, f i) a = Dist.dist (∑ i in range n, f i) a + ‖(fun s => ∑ i in range s, f i) N - a‖ := by
        simp
        exact dist_eq_norm (∑ i in range N, f i) a
      Dist.dist (∑ i in range n, f i) a + ‖(fun s => ∑ i in range s, f i) N - a‖ = ‖(fun s => ∑ i in range s, f i) n - a‖ + ‖(fun s => ∑ i in range s, f i) N - a‖ := by
        simp
        exact dist_eq_norm (∑ i in range n, f i) a
      ‖(fun s => ∑ i in range s, f i) n - a‖ + ‖(fun s => ∑ i in range s, f i) N - a‖ < ‖(fun s => ∑ i in range s, f i) n - a‖ + ε / 2 := by
        simp
        exact hN1
      ‖(fun s => ∑ i in range s, f i) n - a‖ + ε / 2 < ε / 2 + ε / 2 := by
        apply add_lt_add_right
        exact hN2
      ε / 2 + ε / 2 = ε := by
        simp
  · intro hc
    have hd := CompleteSpace.complete hc
    exact hd

theorem nth_term_test [NormedAddCommGroup α] [CompleteSpace α] {f : ℕ → α} (hs : HasCondSum f) : Tendsto f atTop (𝓝 0) := by
  have hc := cauchy_criterion.1 hs
  have hd := Metric.cauchySeq_iff.1 hc
  apply Metric.tendsto_atTop.2
  intro ε
  intro hε
  have hd := hd ε hε
  let ⟨N, hN⟩ := hd
  constructor
  swap
  exact N + 1
  intro n
  intro hn
  have hn2 : n + 1 ≥ N := by
    apply le_step
    exact Nat.le_of_lt hn
  have hn1 : n ≥ N := by exact Nat.le_of_lt hn
  have hN := hN (n + 1) hn2 n hn1
  rw [dist_eq_norm] at hN
  rw [Finset.sum_range_succ_sub_sum] at hN
  rw [dist_eq_norm]
  simp
  exact hN

theorem condconv_unique [AddCommMonoid α] [UniformSpace α] [T2Space α] {f : ℕ → α} (hf : CondConvergesTo f a) (hg : CondConvergesTo f b) : a = b :=
   tendsto_nhds_unique hf hg

theorem tendsto_shift [NormedAddCommGroup α] (f : ℕ → α) (x : α) (k : ℕ) : Tendsto f atTop (𝓝 x) ↔ Tendsto (fun i => f (i + k)) atTop (𝓝 x) := by
  constructor
  · intro hf
    apply NormedAddCommGroup.tendsto_atTop.2
    intro ε
    intro hε
    have hg := NormedAddCommGroup.tendsto_atTop.1 hf ε hε
    have ⟨N, hN⟩ := hg
    constructor
    swap
    exact N
    intro n
    intro hn
    exact hN (n + k) (_root_.le_add_right hn)
  · intro hf
    apply NormedAddCommGroup.tendsto_atTop.2
    intro ε
    intro hε
    have hg := NormedAddCommGroup.tendsto_atTop.1 hf ε hε
    have ⟨N, hN⟩ := hg
    constructor
    swap
    exact N + k
    intro n
    intro hn
    have kek := hN (n - k) (le_sub_of_add_le hn)
    have hk : n = (n - k + k) := by
      refine (Nat.sub_add_cancel ?_).symm
      exact le_of_add_le_right hn
    rw [hk]
    exact kek
