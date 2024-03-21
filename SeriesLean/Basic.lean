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
