import SeriesLean.Basic

open Classical BigOperators Topology Filter Nat Finset Metric Real ENNReal NNReal


noncomputable section

theorem lemma1 : Tendsto (fun (x : ℝ) => (x ^ (-4/3  : ℝ))) (𝓝 1) (𝓝 1) := by
  have hk : 1 = (fun (x : ℝ) => (x ^ (-4/3  : ℝ))) 1 := by
    simp
  nth_rw 2 [hk]
  refine' ContinuousAt.tendsto ?_
  apply ContinuousAt.rpow
  apply Continuous.continuousAt
  exact continuous_id'
  exact continuousAt_const
  left
  exact one_ne_zero

theorem lemma2 : Tendsto (fun (x : ℝ) => 1 - 2 / x) atTop (𝓝 1) := by
  apply NormedAddCommGroup.tendsto_atTop.2
  intro ε
  intro hε
  simp
  constructor
  swap
  exact 4/ε
  intro n
  intro hn
  have hn2 : 2/ε < 4/ε := by
    refine div_lt_div_of_lt hε ?_
    refine sub_pos.mp ?_
    ring_nf
    exact two_pos
  have hn3 : 2/ε < n := by
    exact gt_of_ge_of_gt hn hn2
  have hn4 : 0 < 2/ε := div_pos two_pos hε
  have nn : 0 < n := lt_trans hn4 hn3
  have hk : n = |n| := by
    exact (abs_of_pos nn).symm
  rw [← hk]

  refine (div_lt_one hε).mp ?h.a
  rw [div_right_comm]
  exact (div_lt_one nn).mpr hn3


theorem lemma3 : Tendsto (fun (x : ℝ) => x + 4 / 3) atTop atTop := by
  refine  Monotone.tendsto_atTop_atTop ?_ ?_
  rw [Monotone]
  intro a
  intro b
  intro hab
  simp
  exact hab
  intro b
  constructor
  swap
  exact b - 4/3
  simp

theorem lemma4 : Tendsto (fun (n : ℕ) => ((n + 1) ^ 3 : ℝ)) atTop atTop := by
  refine  Monotone.tendsto_atTop_atTop ?_ ?_
  rw [Monotone]
  intro a
  intro b
  intro hab
  refine pow_le_pow_left ?refine_1.ha ?refine_1.hab 3
  refine Left.add_nonneg ?refine_1.ha.ha ?refine_1.ha.hb
  exact cast_nonneg a
  exact zero_le_one
  simp
  exact hab
  intro b
  constructor
  swap
  exact Nat.ceil |b|
  refine @LE.le.trans _ _ b (Nat.ceil |b| + 1) _ ?_ ?_
  refine @LE.le.trans _ _ b (Nat.ceil |b|) _ ?_ ?_
  refine @LE.le.trans _ _ b |b| (Nat.ceil |b|) ?_ ?_
  exact le_abs_self b
  exact le_ceil |b|
  simp
  refine _root_.le_self_pow ?refine_2.h.refine_2.ha ?refine_2.h.refine_2.h
  simp
  simp

theorem lemma5 : Tendsto (fun (x : ℝ) => ((1-2/x)^((-4/3) : ℝ))) atTop (𝓝 1) := Tendsto.comp lemma1 lemma2

theorem lemma6 : Tendsto (fun (n : ℕ) => ((n + 1) ^ 3 + 4/3 : ℝ)) atTop atTop := Tendsto.comp lemma3 lemma4

theorem lemma7 : Tendsto (fun (n : ℕ) => ((1 - 2/((n+1)^3+4/3))^(((n+1)^3+4/3) : ℝ) : ℝ)) atTop (𝓝 (Real.exp (-2))) := by
  have hk : (fun (n : ℕ) => ((1 - 2/((n+1)^3+4/3))^(((n+1)^3+4/3) : ℝ) : ℝ)) = (fun (n : ℕ) => ((1 + (- 2)/((n+1)^3+4/3))^(((n+1)^3+4/3) : ℝ) : ℝ)) := by
    apply funext
    intro n
    refine' congrFun (congrArg HPow.hPow ?_) _
    ring
  rw [hk]
  exact Tendsto.comp (tendsto_one_plus_div_rpow_exp (-2 : ℝ)) lemma6


theorem lemma8 : Tendsto (fun (n : ℕ) => ((1 - 2/((n+1)^3+4/3))^((-4 : ℝ) /3) : ℝ)) atTop (𝓝 1) := Tendsto.comp lemma5 lemma6

theorem lemma9 : Tendsto (fun (n : ℕ) => ((1 - 2/((n+1)^3+4/3))^((n+1)^3) : ℝ)) atTop (𝓝 (Real.exp (-2))) := by
  have hk : (fun (n : ℕ) => ((1 - 2/((n + 1)^3+4/3))^((n+1)^3) : ℝ)) =
    (fun (x : ℕ) => ((fun (n : ℕ) => ((1 - 2/((n + 1)^3+4/3))^(((n+1)^3+4/3) : ℝ) : ℝ)) x * (fun (n : ℕ) => ((1 - 2/((n+1)^3+4/3))^((-4 : ℝ) / 3) : ℝ)) x)) := by
    apply funext
    intro n
    simp
    have hk : (0 : ℝ) < (1 - 2 / ((↑n+1) ^ 3 + 4 / 3)) := by
      simp
      refine (div_lt_one ?hb).mpr ?_
      refine lt_add_of_pos_of_lt ?hb.ha ?hb.hbc
      refine pow_pos ?hb.ha.H 3
      exact cast_add_one_pos n
      refine div_pos ?hb.hbc.ha ?hb.hbc.hb
      exact four_pos
      exact three_pos
      refine sub_lt_iff_lt_add.mp ?_
      refine @lt_of_lt_of_le _ _ _ 1 _ ?_ ?_
      ring_nf
      refine (div_lt_one ?refine_1.hb).mpr ?refine_1.a
      exact three_pos
      refine lt_of_sub_pos ?refine_1.a.a
      ring_nf
      exact Real.zero_lt_one
      refine one_le_pow_of_one_le ?refine_2.H 3
      simp
    have hh := (Real.rpow_add hk ((n + 1) ^ 3 + 4 / 3) (-4 / 3))
    have hs : (((@Nat.cast ℝ Real.natCast n) + 1) ^ 3 + 4 / 3 + (-4 : ℝ) / 3) = (n+1)^3 := by
      ring
    rw [hs] at hh
    rw [← hh]
    have hkk : (↑n + 1) ^ 3 = (0 : ℝ) + @Nat.cast ℝ Real.natCast ((n + 1) ^ 3) := by
      simp
    rw [hkk]
    have hq : (1 - 2 / (0 + @Nat.cast ℝ Real.natCast ((n + 1) ^ 3) + 4 / 3)) ≠ 0 := by
      rw [hkk] at hk
      exact _root_.ne_of_gt hk
    rw [Real.rpow_add_nat hq 0 ((n + 1) ^ 3)]
    rw [Real.rpow_zero]
    rw [one_mul]
  rw [hk]
  have hh := Filter.Tendsto.mul lemma7 lemma8
  simp
  rw [mul_one] at hh
  exact hh

theorem lemma10 : Tendsto (fun (n : ℕ) => ((1 - 2/(n^3+4/3))^(n^3) : ℝ)) atTop (𝓝 (Real.exp (-2))) := by
  apply (@Filter.tendsto_add_atTop_iff_nat _ (fun (n : ℕ) => ((1 - 2/(n^3+4/3))^(n^3) : ℝ)) _ 1).1
  have hk : (fun i => (1 - 2 / (@Nat.cast ℝ Real.natCast (i + 1) ^ 3 + 4 / 3)) ^ (i + 1) ^ 3) = (fun (n : ℕ) => ((1 - 2/((n+1)^3+4/3))^((n+1)^3) : ℝ)) := by
    apply funext
    intro n
    have hg : @Nat.cast ℝ Real.natCast (n + 1) = @Nat.cast ℝ Real.natCast n + 1 := by
      exact cast_succ n
    rw [hg]
  rw [hk]
  exact lemma9

theorem lemma11 : Tendsto (fun (n : ℕ) => (((3 * n ^ 3 - 2) / (3 * n ^ 3 + 4)) ^ (n ^ 3) : ℝ)) atTop (𝓝 (Real.exp (-2))) := by
  have hf : (fun (n : ℕ) => (((3 * n ^ 3 - 2) / (3 * n ^ 3 + 4)) ^ (n ^ 3) : ℝ)) = (fun (n : ℕ) => ((1 - 2/(n^3+4/3))^(n^3) : ℝ)) := by
    apply funext
    intro n
    refine' congrFun (congrArg HPow.hPow ?_) (n ^ 3)
    have hc2 : (3 * (@Nat.cast ℝ Real.natCast n) ^ 3 + 4) ≠ 0 := by
      have hc3 : (3 * (@Nat.cast ℝ Real.natCast n) ^ 3 + 4) > 0 := by
        refine lt_add_of_le_of_pos ?hbc ?ha
        apply mul_nonneg
        exact zero_le_three
        simp
        simp
      exact ne_of_gt hc3
    apply (mul_left_inj' hc2).1
    rw [div_mul_cancel (3 * @Nat.cast ℝ Real.natCast n ^ 3 - 2) hc2, sub_mul 1]
    have hd : (@Nat.cast ℝ Real.natCast n ^ 3 + 4 / 3) = 1/3 * (3 * (@Nat.cast ℝ Real.natCast n) ^ 3 + 4) := by
      ring
    rw [hd, div_mul, mul_div_cancel]
    simp
    ring
    exact hc2
  rw [hf]
  exact lemma10



theorem example1 : ¬ HasCondSum (fun n => ((((3 * n ^ 3 - 2) / (3 * n ^ 3 + 4)) ^ (n ^ 3)) : ℝ)) := by
  intro hf
  have hg := nth_term_test hf
  have ht := tendsto_nhds_unique hg lemma11
  have ht2 := LT.lt.ne (exp_pos (-2))
  exact ht2 ht

end

noncomputable section

theorem first_wonderful_limit : Tendsto (fun x => (sin x) / x) (𝓝[≠] 0) (𝓝 1) := by
  have hg := hasDerivAt_iff_tendsto_slope_zero.1 (Real.hasDerivAt_sin 0)
  rw [Real.cos_zero] at hg
  have kek : (fun x => sin x / x) = (fun t => t⁻¹ • (sin (0 + t) - sin 0)) := by
    apply funext
    intro x
    rw [Real.sin_zero, zero_add, sub_zero, @IsROrC.real_smul_eq_coe_mul ℝ, IsROrC.ofReal_real_eq_id, id_eq]
    ring
  rw [kek]
  exact hg


theorem example2 : ¬ HasCondSum (fun n => sin (1 / n)) := by
  intro hf
  have hf2 := (HasCondSum.shift 1).1 hf
  have kek : (fun i => sin (1 / @Nat.cast ℝ Real.natCast (i + 1))) = (fun i => sin (1 / (@Nat.cast ℝ Real.natCast i + 1))) := by
    apply funext
    intro x
    apply congrArg
    refine Mathlib.Tactic.LinearCombination.c_div_pf ?h.h.p 1
    exact cast_succ x
  rw [kek] at hf2
  have ha : ∀ n : ℕ, 0 < sin (1 / (n + 1)) := by
    intro n
    apply Real.sin_pos_of_pos_of_le_one
    exact one_div_pos_of_nat
    have kek : 0 < (@Nat.cast ℝ Real.natCast n + 1) := by
      exact cast_add_one_pos n
    apply (div_le_one kek).2
    refine sub_le_iff_le_add.mp ?hx.a
    rw [sub_self]
    exact cast_nonneg n
  have hb : ∀ n : ℕ, 0 < (1 : ℝ) / (n + 1) := by
    exact fun n => one_div_pos_of_nat
  have hc : Tendsto (fun i : ℕ => sin (1 / (i + 1)) / ((1 : ℝ) / (i + 1))) atTop (𝓝 1) := by
    have hd : Tendsto (fun i => 1 / (@Nat.cast ℝ Real.natCast i + 1)) atTop (𝓝[≠] 0) := by
      apply tendsto_nhdsWithin_iff.2
      constructor
      exact tendsto_one_div_add_atTop_nhds_0_nat
      apply Filter.eventually_atTop.2
      constructor
      swap
      exact 0
      intro b
      intro _
      apply (Set.mem_compl_iff {0} (1 / (@Nat.cast ℝ natCast b + 1))).2
      have gg : (1 / (@Nat.cast ℝ natCast b + 1)) ≠ 0 := by
        exact LT.lt.ne' (hb b)
      assumption
    exact Tendsto.comp first_wonderful_limit hd
  have hd : (0 : ℝ) < 1 := by exact Real.zero_lt_one
  have hf3 := (@equally_convergent_of_limit (fun i => sin (1 / (i + 1))) (fun i => (1 : ℝ) / (i + 1)) 1 ha hb hd hc).1 hf2
  have kek : (fun i => 1 / (@Nat.cast ℝ Real.natCast i + 1)) = fun i => 1 / @Nat.cast ℝ Real.natCast (i + 1) := by
    apply funext
    intro n
    refine Mathlib.Tactic.LinearCombination.c_div_pf ?h.p 1
    symm
    exact cast_succ n
  rw [kek] at hf3
  have hf4 := (@HasCondSum.shift ℝ _ _ _ (fun i => 1 / @Nat.cast ℝ Real.natCast i) 1).2 hf3
  have kek2 : ∀ (n : ℕ), 0 ≤ 1 / @Nat.cast ℝ Real.natCast n := by
    intro n
    refine one_div_nonneg.mpr ?inr.a
    exact cast_nonneg n
  have hf5 := Summable.of_pos_of_conv kek2 hf4
  exact Real.not_summable_one_div_nat_cast hf5

end
