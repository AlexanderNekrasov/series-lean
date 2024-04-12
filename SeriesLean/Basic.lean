import Mathlib

set_option maxHeartbeats 1000000


open Classical BigOperators Topology Filter Nat Finset Metric Real ENNReal NNReal

def CondConvergesTo [AddCommMonoid α] [UniformSpace α] (f : ℕ → α) (a : α) : Prop :=
  Tendsto (fun s => ∑ i in range s, f i) atTop (𝓝 a)

def HasCondSum [AddCommMonoid α] [UniformSpace α] (f : ℕ → α) : Prop :=
  ∃ a, CondConvergesTo f a

noncomputable def get_sum [AddCommMonoid α] [UniformSpace α] {f : ℕ → α} (hs : HasCondSum f) : α := Classical.choose hs
theorem get_sum_spec [AddCommMonoid α] [UniformSpace α] {f : ℕ → α} (hs : HasCondSum f) : CondConvergesTo f (get_sum hs) := Classical.choose_spec hs

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

theorem HasCondSum.of_summable [AddCommMonoid α] [UniformSpace α] {f : ℕ → α} (hf : Summable f) : HasCondSum f := by
  rw [HasCondSum]
  constructor
  rw [CondConvergesTo]
  exact HasSum.tendsto_sum_nat  hf.hasSum

theorem Summable.of_pos_of_conv {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hs : HasCondSum f)
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

theorem Summable.of_abs_conv [SeminormedAddCommGroup β] [CompleteSpace β] {f : ℕ → β} (hf: AbsolutelyConverges f) : Summable f := by
  apply Summable.of_norm
  rw [AbsolutelyConverges] at hf
  apply Summable.of_pos_of_conv
  · intro n
    exact norm_nonneg (f n)
  exact hf

theorem tsum_eq_get_sum' [SeminormedAddCommGroup β] [CompleteSpace β] [T2Space β] {f : ℕ → β} (hf : Summable f) : tsum f = get_sum (HasCondSum.of_summable hf) := by
  have hc : HasSum f (tsum f) := by
    exact Summable.hasSum hf
  rw [HasSum] at hc
  have hd : CondConvergesTo f (get_sum (HasCondSum.of_summable hf)) := by
    exact get_sum_spec (HasCondSum.of_summable hf)
  rw [CondConvergesTo] at hd
  have hd' := Tendsto.comp hc tendsto_finset_range
  have he : (fun s => ∑ b in s, f b) ∘ range = (fun s => ∑ i in range s, f i) := by
    exact rfl
  rw [he] at hd'
  exact tendsto_nhds_unique hd' hd

theorem tsum_eq_get_sum [SeminormedAddCommGroup β] [CompleteSpace β] [T2Space β] {f : ℕ → β} (hf : HasCondSum f) (hf2 : AbsolutelyConverges f) : tsum f = get_sum hf := by
  exact tsum_eq_get_sum' (Summable.of_abs_conv hf2)

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

theorem second_comparison_test {a : ℕ → ℝ} {b : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n) (hab : ∃ m, 0 < m ∧ ∃ M, 0 < M ∧ ∀ n, m ≤ a n / b n ∧ a n / b n ≤ M) :
    HasCondSum a ↔ HasCondSum b := by
  have ⟨m, h1⟩ := hab
  have hm := h1.1
  have ⟨M, h2⟩ := h1.2
  have hM := h2.1
  have hmM := h2.2
  constructor
  · intro hca
    have hba : HasCondSum (fun i => m * b i) := by
      apply cconv_of_nonneg_of_le
      · intro n
        refine (mul_nonneg_iff_of_pos_left hm).mpr ?hf.a
        exact LT.lt.le (hb n)
      swap
      exact hca
      · intro n
        have hk3 := (hmM n).1
        exact (_root_.le_div_iff (hb n)).mp hk3
    have hk := HasCondSum.of_const_mul (fun i => m * b i) (1 / m) hba
    simp at hk
    have hk2 : (fun i => m⁻¹ * (m * b i)) = b := by
      apply funext
      intro x
      rw [← mul_assoc]
      refine (mul_eq_right₀ ?h.hb).mpr ?h.a
      exact _root_.ne_of_gt (hb x)
      refine (inv_mul_eq_one₀ ?h.a.ha).mpr rfl
      exact _root_.ne_of_gt hm
    rw [← hk2]
    exact hk
  · intro hcb
    have hba : HasCondSum (fun i => M⁻¹ * a i) := by
      apply cconv_of_nonneg_of_le
      · intro n
        refine (mul_nonneg_iff_of_pos_right (ha n)).mpr ?foo
        refine inv_nonneg.mpr ?foo.a
        exact LT.lt.le hM
      swap
      exact hcb
      intro n
      have hk3 := (hmM n).2
      refine (inv_mul_le_iff' hM).mpr ?hfg.a
      exact (_root_.div_le_iff' (hb n)).mp hk3
    have hk := HasCondSum.of_const_mul (fun i => M⁻¹ * a i) M hba
    have hk2 : (fun i => M * (fun i => M⁻¹ * a i) i) = a := by
      apply funext
      intro x
      simp
      rw [← mul_assoc]
      refine mul_left_eq_self₀.mpr ?boo
      left
      refine mul_inv_cancel ?foo.h.h
      exact _root_.ne_of_gt hM
    rw [← hk2]
    exact hk

theorem equally_convergent_of_limit {a : ℕ → ℝ} {b : ℕ → ℝ} {c : ℝ} (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n) (hc : 0 < c) (hab : Tendsto (fun i => a i / (b i)) atTop (𝓝 c)) :
    HasCondSum a ↔ HasCondSum b := by
  apply second_comparison_test
  exact ha
  exact hb
  have mm_0 := Metric.tendsto_atTop.1 hab (c / 2) (half_pos hc)
  let ⟨n_0, hn_0⟩ := mm_0
  have hkek : (image (fun i => a i / b i) (range (n_0 + 1))).Nonempty := by
    apply Finset.image_nonempty.2
    apply Finset.nonempty_range_iff.2
    exact succ_ne_zero n_0
  let m_1 := Finset.min' (Finset.image (fun i => (a i) / (b i)) (Finset.range (n_0 + 1))) hkek
  let m := min (c / 2) m_1
  let M_1 := Finset.max' (Finset.image (fun i => (a i) / (b i)) (Finset.range (n_0 + 1))) hkek
  let M := max (3 * c / 2) M_1
  constructor
  swap
  exact m
  constructor
  · apply lt_min
    exact half_pos hc
    have kek : m_1 = Finset.min' (Finset.image (fun i => (a i) / (b i)) (Finset.range (n_0 + 1))) hkek := by
      exact rfl
    rw [kek]
    apply (Finset.lt_min'_iff (Finset.image (fun i => (a i) / (b i)) (Finset.range (n_0 + 1))) hkek).2
    intro y
    intro hy
    have hy2 := Finset.mem_image.1 hy
    have ⟨q, hq⟩ := hy2
    rw [← hq.2]
    exact div_pos (ha q) (hb q)
  constructor
  swap
  exact M
  constructor
  · have kek : M = max (3 * c / 2) M_1 := by exact rfl
    rw [kek]
    apply lt_max_of_lt_left
    apply half_pos
    refine Real.mul_pos ?hab.h.right.h.left.h.h.a hc
    exact three_pos
  intro n
  cases (Classical.em (n ≤ n_0)) with
  | inl hp =>
      constructor
      have hkek1 : m = min (c / 2) m_1 := rfl
      rw [hkek1]
      apply min_le_of_right_le
      have hkek2 : m_1 = Finset.min' (Finset.image (fun i => a i / b i) (Finset.range (n_0 + 1))) hkek := rfl
      rw [hkek2]
      apply Finset.min'_le
      apply Finset.mem_image.2
      constructor
      swap
      exact n
      constructor
      exact mem_range_succ_iff.mpr hp
      rfl
      apply le_max_of_le_right
      have hkek3 : M_1 = Finset.max' (Finset.image (fun i => (a i) / (b i)) (Finset.range (n_0 + 1))) hkek := rfl
      rw [hkek3]
      apply Finset.le_max'
      apply Finset.mem_image.2
      constructor
      swap
      exact n
      constructor
      exact mem_range_succ_iff.mpr hp
      rfl
  | inr hq =>
      have hk := hn_0 n (Nat.le_of_not_ge hq)
      rw [Real.dist_eq] at hk
      constructor
      have hl : c / 2 < a n / b n := by
        have hkk := sub_lt_of_abs_sub_lt_left hk
        rw [sub_self_div_two] at hkk
        exact hkk
      have hg : m ≤ c / 2 := by exact min_le_left (c / 2) m_1
      exact LT.lt.le (LE.le.trans_lt hg hl)
      have hl : a n / b n < 3 * c / 2 := by
        have hkk := sub_lt_of_abs_sub_lt_right hk
        have hll := add_lt_add_of_le_of_lt (Eq.le (refl (c / 2))) hkk
        simp at hll
        have hg : c / 2 + c = 3 * c / 2 := by
          refine EuclideanDomain.eq_div_of_mul_eq_right ?haa ?h
          exact two_ne_zero
          rw [mul_add]
          ring
        rw [← hg]
        exact hll
      have hg : 3 * c / 2 ≤ M := by exact le_max_left (3 * c / 2) M_1
      apply LT.lt.le (LT.lt.trans_le hl hg)

theorem CondConvergesTo.shift [AddCommGroup α] [UniformSpace α] [ContinuousAdd α] {f: ℕ → α} {c: α} (k: ℕ) : CondConvergesTo f c ↔ CondConvergesTo (fun i => f (i + k)) (c - ∑ i in range k, f i) := by
  have kek  : (fun s => (∑ i in range (s + k), f i) + (-∑ i in range k, f i)) = (fun s => ∑ i in range s, f (i + k)) := by
    apply funext
    intro n
    refine add_neg_eq_iff_eq_add.mpr ?h.a
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Nat.succ_add, succ_eq_add_one, succ_eq_add_one, Finset.sum_range_succ, Finset.sum_range_succ]
        rw [ih]
        rw [add_assoc, add_assoc]
        rw [add_comm (∑ i in range k, f i)]
  rw [CondConvergesTo, CondConvergesTo]
  constructor
  intro hf
  have hg := (@Filter.tendsto_add_atTop_iff_nat _ (fun s => ∑ i in range s, f i) (𝓝 c) k).2 hf
  rw [← kek, sub_eq_add_neg]
  apply Filter.Tendsto.add_const
  exact hg
  intro hf
  rw [← kek] at hf
  have hq := Filter.Tendsto.add_const (∑ i in range k, f i) hf
  simp at hq
  exact (@Filter.tendsto_add_atTop_iff_nat _ (fun s => ∑ i in range s, f i) (𝓝 c) k).1 hq

theorem HasCondSum.shift [AddCommGroup α] [UniformSpace α] [ContinuousAdd α] {f : ℕ → α} (k : ℕ) : HasCondSum f ↔ HasCondSum (fun i => f (i + k)) := by
  rw [HasCondSum, HasCondSum]
  constructor
  intro hf
  have ⟨q, hq⟩ := hf
  constructor
  exact (CondConvergesTo.shift k).1 hq
  intro hf
  have ⟨q, hq⟩ := hf
  constructor
  have kek : q = q + ∑ i in range k, f i - ∑ i in range k, f i := by
    simp
  rw [kek] at hq
  exact (CondConvergesTo.shift k).2 hq

theorem third_comparison_test_conv' {a : ℕ → ℝ} {b : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n) (hab : ∀ n, (a (n + 1)) / (a n) ≤ (b (n + 1)) / (b n))
    : HasCondSum b → HasCondSum a := by
  intro bconv
  have h : ∀ n, (a n) / (a 0) ≤ (b n) / (b 0) := by
    intro n
    induction n with
    | zero =>
      rw [Nat.zero_eq]
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_cancel, mul_inv_cancel]
      exact _root_.ne_of_gt (hb 0)
      exact _root_.ne_of_gt (ha 0)
    | succ n ih =>
      have ht1 : 0 ≤ a (n + 1) / a n := by
        apply div_nonneg_iff.2
        left
        use (LT.lt.le $ ha (n + 1)), (LT.lt.le $ ha n)
      have ht2 : 0 ≤ b n / b 0 := by
        apply div_nonneg_iff.2
        left
        use (LT.lt.le $ hb n), (LT.lt.le $ hb 0)
      have kek := mul_le_mul_of_le_of_le (hab n) ih ht1 ht2
      rw [succ_eq_add_one]
      rw [mul_comm_div, mul_comm_div, div_right_comm, div_right_comm (b n), div_eq_mul_inv (a n), div_eq_mul_inv (b n), mul_inv_cancel, mul_inv_cancel, mul_div_assoc', mul_one, mul_div_assoc', mul_one] at kek
      assumption
      exact _root_.ne_of_gt (hb n)
      exact _root_.ne_of_gt (ha n)
  have h' : ∀ n, a n ≤ (a 0) / (b 0) * b n := by
    intro n
    rw [div_mul_comm]
    exact (_root_.div_le_iff (ha 0)).mp (h n)
  apply cconv_of_nonneg_of_le
  exact fun n => LT.lt.le (ha n)
  exact h'
  exact HasCondSum.of_const_mul (fun i => b i) (a 0 / b 0) bconv

theorem third_comparison_test_conv {a : ℕ → ℝ} {b : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n) (hab : ∃ N : ℕ, ∀ n, N ≤ n → (a (n + 1)) / (a n) ≤ (b (n + 1)) / (b n))
    : HasCondSum b → HasCondSum a := by
  intro bconv
  let ⟨N, hab'⟩ := hab
  have bconv' : HasCondSum (fun n => b (n + N)):= (HasCondSum.shift N).1 bconv
  apply (HasCondSum.shift N).2
  have ha' : ∀ n, 0 < a (n + N) := by
    intro n
    simp_all only
  have hb' : ∀ n, 0 < b (n + N) := by
    intro n
    simp_all only
  have hab'' : ∀ (n : ℕ), a (n + 1 + N) / a (n + N) ≤ b (n + 1 + N) / b (n + N) := by
    intro n
    have hk : n + 1 + N = n + N + 1 := by
      ring
    rw [hk]
    simp_all only [forall_const, le_add_iff_nonneg_left, _root_.zero_le]
  exact third_comparison_test_conv' ha' hb' hab'' bconv'

theorem third_comparison_test_not_conv {a : ℕ → ℝ} {b : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n) (hab : ∃ N : ℕ, ∀ n, N ≤ n → (a (n + 1)) / (a n) ≤ (b (n + 1)) / (b n))
    : ¬ HasCondSum a → ¬ HasCondSum b := by
  intro nconva
  intro bconv
  exact nconva $ third_comparison_test_conv ha hb hab bconv

theorem HasCondSum.of_sum_range_le {f : ℕ → ℝ} {c : ℝ} (hf : ∀ (n : ℕ), 0 ≤ f n) (h : ∀ (n : ℕ), (Finset.sum (Finset.range n) fun i => f i) ≤ c) : HasCondSum f := by
  apply HasCondSum.of_summable
  exact summable_of_sum_range_le hf h

theorem sum_le_get_sum {f : ℕ → ℝ} (hf1 : ∀ n, 0 ≤ f n) (hf2 : HasCondSum f) (n : ℕ)
    : ∑ i in range n, f i ≤ get_sum hf2 := by
  rw [← tsum_eq_get_sum]
  apply sum_le_tsum
  exact fun i _ => hf1 i
  exact Summable.of_nonneg hf1 hf2
  exact AbsolutelyConverges.of_nonneg f hf1 hf2

theorem cauchy_condensation_test {a : ℕ → ℝ} (ha1 : ∀ n, 0 ≤ a n) (ha2 : Antitone a) :
    HasCondSum a ↔ HasCondSum (fun n => 2 ^ n * a (2 ^ n)) := by
  constructor
  · intro conva
    apply HasCondSum.of_sum_range_le
    · intro n
      simp_all only [gt_iff_lt, zero_lt_two, pow_pos, mul_nonneg_iff_of_pos_left]
    swap
    exact a 1 + 2 * get_sum conva
    intro n
    have hk : ∀ n, (∑ i in range n, 2 ^ i * a (2 ^ (i + 1))) ≤ ∑ i in range (2 ^ n + 1), a i := by
      intro n
      induction n with
      | zero =>
        rw [zero_eq, sum_range_zero, Nat.pow_zero]
        apply sum_nonneg
        exact fun i _ => ha1 i
      | succ n ih =>
        have ht : (k : ℕ) → (k ≤ 2 ^ n) →  (∑ i in range n, 2 ^ i * a (2 ^ (i + 1))) + k * a (2 ^ (n + 1)) ≤ ∑ i in range (2 ^ n + 1 + k), a i := by
          intro k
          induction k with
          | zero =>
            intro _
            rw [zero_eq, Nat.cast_zero, zero_mul, add_zero, add_zero]
            assumption
          | succ k ik =>
            rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, add_succ, add_succ, sum_range_succ, add_zero, succ_eq_add_one, succ_eq_add_one]

            intro hk
            have hk' : k <= 2 ^ n := by exact Nat.le_of_lt hk
            have hl : a (2 ^ (n + 1)) ≤ a (2 ^ n + 1 + k) := by
              have hy : 2 ^ n + 1 + k ≤ 2 ^ (n + 1) := by
                refine (Nat.le_sub_iff_add_le' ?h).mp ?_
                rw [pow_add, pow_one, mul_two]
                refine Nat.add_le_add_iff_left.mpr ?h.a
                exact Nat.one_le_two_pow
                rw [pow_add, pow_one, mul_two, sub_add_eq, add_tsub_cancel_right]
                exact le_sub_one_of_lt hk
              exact ha2 hy
            exact _root_.add_le_add (ik hk') hl
        have ht' := ht (2 ^ n) (le_refl _)
        rw [sum_range_succ, succ_eq_add_one]
        have hk : 2 ^ n + 1 + 2 ^ n = 2 ^ (n + 1) + 1 := by ring
        rw [Nat.cast_pow, Nat.cast_two, hk] at ht'
        exact ht'
    have hq : ∀ n, ∑ i in range (2 ^ n + 1), a i ≤ get_sum conva := fun n => sum_le_get_sum ha1 conva (2 ^ n + 1)
    have ht : (∑ i in range n, 2 ^ i * a (2 ^ i)) + 2 ^ n * a (2 ^ n) = a 1 + 2 * ∑ i in range n, 2 ^ i * a (2 ^ (i + 1)) := by
      induction n with
      | zero =>
        rw [sum_range_zero, sum_range_zero, mul_zero, add_zero, zero_eq, Nat.pow_zero, _root_.pow_zero 2, one_mul, zero_add]
      | succ n ih =>
        rw [sum_range_succ, sum_range_succ, ih, succ_eq_add_one, mul_add, add_assoc]
        apply Mathlib.Tactic.LinearCombination.c_add_pf
        apply Mathlib.Tactic.LinearCombination.c_add_pf
        rw [add_comm, pow_add, pow_one, mul_assoc]
    have ht' : (∑ i in range n, 2 ^ i * a (2 ^ i)) ≤ a 1 + 2 * ∑ i in range n, 2 ^ i * a (2 ^ (i + 1)) := by
      rw [← ht]
      refine (le_add_iff_nonneg_right (∑ i in range n, 2 ^ i * a (2 ^ i))).mpr ?_
      apply mul_nonneg
      apply pow_nonneg
      exact zero_le_two
      exact ha1 (2 ^ n)
    calc
      ∑ i in range n, 2 ^ i * a (2 ^ i) <= a 1 + 2 * ∑ i in range n, 2 ^ i * a (2 ^ (i + 1)) := by
        exact ht'
      _ <= a 1 + 2 * ∑ i in range (2 ^ n + 1), a i := by
        apply add_le_add_left
        refine (mul_le_mul_iff_of_pos_left ?bc.a0).mpr (hk n)
        exact two_pos
      _ <= a 1 + 2 * get_sum conva := by
        apply add_le_add_left
        refine (mul_le_mul_iff_of_pos_left ?bc.a0).mpr (hq n)
  · intro conva
    apply HasCondSum.of_sum_range_le
    exact ha1
    swap
    exact a 0 + a 1 + get_sum conva
    have mon : Monotone (fun n => ∑ i in range n, a i) := by
      apply monotone_nat_of_le_succ
      intro n
      rw [← succ_eq_add_one, sum_range_succ, ← add_zero (∑ i in range n, a i), add_assoc, zero_add]
      apply add_le_add_left
      exact ha1 n
    intro n
    suffices h : ∑ i in range (2 ^ n + 1), a i ≤ a 0 + a 1 + get_sum conva from by
      have kek : ∀ n, n ≤ 2 ^ n + 1 := by
        intro n
        induction n with
        | zero =>
          exact Nat.zero_le (2 ^ zero + 1)
        | succ n ih =>
          rw [succ_eq_add_one, pow_add, pow_one, mul_two]
          refine Nat.add_le_add_right ?succ.h 1
          have kk : 2 ^ n + 1 ≤ 2 ^ n + 2 ^ n := by
            refine Nat.add_le_add_left ?h (2 ^ n)
            exact Nat.one_le_two_pow
          exact Nat.le_trans ih kk
      exact ge_trans h (mon (kek n))
    have hk : ∑ i in range (2 ^ n + 1), a i ≤ a 0 + a 1 + ∑ i in range n, 2 ^ i * a (2 ^ i) := by
      induction n with
      | zero =>
        rw [Nat.zero_eq, Nat.pow_zero, ← succ_eq_add_one, sum_range_succ, sum_range_zero, add_zero, sum_range_one]
      | succ n ih =>
        rw [succ_eq_add_one, pow_add, sum_range_succ _ n, pow_one, mul_two, add_assoc, add_comm (2 ^n) 1, ← add_assoc]
        have hg : (k: ℕ) → k ≤ 2 ^n → ∑ i in range (2 ^ n + 1 + k), a i ≤ a 0 + a 1 + ∑ x in range n, 2 ^ x * a (2 ^ x) + k * a (2 ^ n) := by
          intro k
          induction k with
          | zero =>
            intro _
            rw [zero_eq, add_zero, Nat.cast_zero, zero_mul, add_zero]
            exact ih
          | succ k ih =>
            intro hk
            rw [add_succ, sum_range_succ, Nat.cast_succ, add_mul, ← add_assoc, one_mul]
            have hk' : k ≤ 2 ^ n := by exact Nat.le_of_lt hk
            have ih := ih hk'
            have hw : a (2 ^ n + 1 + k) ≤ a (2 ^ n) := by
              apply ha2
              rw [add_assoc]
              exact Nat.le_add_right (2 ^ n) (1 + k)
            exact _root_.add_le_add ih hw
        have kek := hg (2 ^ n) (le_refl (2^n))
        rw [Nat.cast_pow] at kek
        have kek2 : (@Nat.cast ℝ natCast (2 : ℕ)) = (2 : ℝ) := by
          exact rfl
        rw [kek2] at kek
        rw [← add_assoc]
        exact kek
    calc
      ∑ i in range (2 ^ n + 1), a i ≤ a 0 + a 1 + ∑ i in range n, 2 ^ i * a (2 ^ i) := by
        assumption
      _ ≤ a 0 + a 1 + get_sum conva := by
        apply add_le_add_left
        have kek : ∀ (n : ℕ), 0 ≤ 2 ^ n * a (2 ^ n) := by
          intro n
          apply mul_nonneg
          refine pow_nonneg ?ha.H n
          exact ha1 (2 ^ n)

        exact sum_le_get_sum kek conva n

theorem Real.hasCondSum_zeta_iff {k : ℝ} : HasCondSum (fun n => 1 / ((@Nat.cast ℝ natCast n) ^ k)) ↔ (1 < k) := by
  let g := fun n => if n == 0 then 1 else 1 / (@Nat.cast ℝ natCast n) ^ k
  have hg : g = fun n => if n == 0 then 1 else 1 / (@Nat.cast ℝ natCast n) ^ k := rfl
  have hkek : (fun i => 1 / @Nat.cast ℝ natCast (i + 1) ^ k) = (fun i => g (i + 1)) := by
    apply funext
    intro n
    rw [hg]
    simp
  have ha : ∀ (n : ℕ), 0 ≤ g n := by
    intro n
    rw [hg]
    simp
    refine ite_nonneg ?ha ?hb
    exact instStrictOrderedCommRingReal.proof_3
    refine inv_nonneg_of_nonneg ?hb.a
    refine rpow_nonneg ?hb.a.hx k
    exact cast_nonneg n
  have hb : 0<k → Antitone g:= by
    intro hk
    apply antitone_nat_of_succ_le
    intro n
    rw [hg]
    simp
    cases (Classical.em (n = 0)) with
    | inl hn =>
      rw [if_pos hn, hn, cast_zero, zero_add, Real.one_rpow, inv_one]
    | inr hn =>
      rw [if_neg hn]
      refine inv_le_inv_of_le ?hf.inr.ha ?hf.inr.h
      refine rpow_pos_of_pos ?hf.inr.ha.hx k
      refine cast_pos.mpr ?hf.inr.ha.hx.a
      exact zero_lt_of_ne_zero hn
      refine (Real.rpow_le_rpow_iff ?hf.inr.h.hx ?hf.inr.h.hy hk).mpr ?hf.inr.h.a
      exact cast_nonneg n
      refine Left.add_nonneg ?hf.inr.h.hy.ha ?hf.inr.h.hy.hb
      exact cast_nonneg n
      exact instStrictOrderedCommRingReal.proof_3
      refine le_add_of_le_of_nonneg ?hf.inr.h.a.hbc ?hf.inr.h.a.ha
      exact instDistribLatticeReal.proof_1 ↑n
      exact instStrictOrderedCommRingReal.proof_3
  have hw : (fun n => 2 ^ n * (((2 : ℝ) ^ n) ^ k)⁻¹) = (fun n => (2 ^ (1 - k)) ^ n) := by
    apply funext
    intro n
    rw [← Real.rpow_neg, ← Real.rpow_one (2 ^ n), ← Real.rpow_mul, ← Real.rpow_add,
        ← Real.rpow_mul_natCast, one_mul, mul_comm, Real.rpow_mul, Real.rpow_nat_cast,
        Mathlib.Tactic.RingNF.add_neg]
    repeat {exact zero_le_two}
    refine pow_pos ?h.hx.H n
    exact zero_lt_two
    refine pow_nonneg ?_ n
    exact zero_le_two
    refine pow_nonneg ?_ n
    exact zero_le_two
  constructor
  · intro hp
    cases (Classical.em (k ≤ 0)) with
    | inl hk =>
      exfalso
      have hf := nth_term_test hp
      have ⟨N, hN⟩ := Metric.tendsto_atTop.1 hf 1 zero_lt_one
      have hr := hN (N + 1) (Nat.le_add_right N 1)
      rw [dist_0_eq_abs, abs_eq_self.2] at hr
      have ht : 0 < @Nat.cast ℝ natCast (N + 1) ^ k := by
        refine rpow_pos_of_pos ?hx k
        refine cast_pos.mpr ?hx.a
        exact zero_lt_succ N
      have hr2 := (one_div_lt zero_lt_one ht).2 hr
      rw [div_one] at hr2
      have ht : ¬(1 < @Nat.cast ℝ natCast (N + 1) ^ k) := by
        apply not_lt.2
        refine Real.rpow_le_one_of_one_le_of_nonpos ?hx2 hk
        refine one_le_cast.mpr ?hx2.a
        exact Nat.le_add_left 1 N
      exact ht hr2
      refine one_div_nonneg.mpr ?mp.inl.a
      refine rpow_nonneg ?mp.inl.a.hx k
      exact cast_nonneg (N + 1)
    | inr hk =>
      have hk := not_le.1 hk
      have hp' := (HasCondSum.shift 1).1 hp
      rw [hkek] at hp'
      have hp' := (HasCondSum.shift 1).2 hp'
      have hq := (cauchy_condensation_test ha (hb hk)).1 hp'
      rw [hg] at hq
      simp at hq
      rw [hw] at hq
      have ha := nth_term_test hq
      by_contra h
      rw [not_lt] at h
      cases (Classical.em (k=1)) with
      | inl hk =>
        rw [hk, sub_self, Real.rpow_zero] at ha
        have hf : (fun n =>  (1 : ℝ) ^ n) = (fun n => 1) := by
          apply funext
          intro n
          exact one_pow n
        rw [hf] at ha
        have hg : Tendsto (fun (_ : ℕ) => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
        have ht := tendsto_nhds_unique ha hg
        exact zero_ne_one ht
      | inr hk =>
        have h2 : 0 < (((2 : ℝ) ^ (1 - k)))⁻¹ := by
          apply inv_pos_of_pos
          apply rpow_pos_of_pos
          exact zero_lt_two
        have h3 : ((2 : ℝ) ^ (1 - k))⁻¹ < 1 := by
          apply inv_lt_one
          apply Real.one_lt_rpow
          exact ContDiffBump.instInhabitedContDiffBump.proof_3
          refine sub_pos.mpr ?_
          exact lt_of_le_of_ne h hk
        have h4 := Tendsto.comp (Tendsto.comp  (tendsto_rpow_atBot_of_base_lt_one ((2 : ℝ) ^ (1 - k))⁻¹ h2 h3) Filter.tendsto_neg_atTop_atBot) tendsto_nat_cast_atTop_atTop
        have h5 : ((Real.rpow (2 ^ (1 - k))⁻¹ ∘ Neg.neg) ∘ Nat.cast) = (fun n => (2 ^ (1 - k)) ^ n) := by
          apply funext
          intro n
          simp
          rw [← Real.rpow_neg, ← Real.rpow_mul, ← Real.rpow_nat_cast, ← Real.rpow_mul]
          refine congrArg (HPow.hPow 2) ?_
          exact neg_mul_neg (1 - k) ↑n
          exact zero_le_two
          exact zero_le_two
          exact zero_le_two
        rw [h5] at h4
        exact not_tendsto_atTop_of_tendsto_nhds ha h4
  · intro hk
    apply (HasCondSum.shift 1).2
    rw [hkek]
    apply (HasCondSum.shift 1).1
    apply (cauchy_condensation_test ha ?_).2
    rw [hg]
    simp
    rw [hw]
    apply HasCondSum.of_summable
    apply NormedRing.summable_geometric_of_norm_lt_one
    rw [norm_eq_abs, abs_eq_self.2]
    apply Real.rpow_lt_one_of_one_lt_of_neg
    exact one_lt_two
    simp
    exact hk
    apply Real.rpow_nonneg
    exact zero_le_two
    refine hb ?_
    refine LT.lt.trans ?_ hk
    exact Real.zero_lt_one
