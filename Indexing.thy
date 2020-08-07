theory Indexing
  imports Complex_Main
begin

section \<open>Indexing\<close>

subsection \<open>Sqrt Floor and Ceiling\<close>

definition lg :: "real \<Rightarrow> real" where
  "lg \<equiv> log 2"

definition sqrt_ceiling :: "nat \<Rightarrow> nat" ("sqrt\<up> _" [1000]) where 
  "sqrt\<up> u = 2^(nat \<lceil>lg u / 2\<rceil>)"

definition sqrt_floor :: "nat \<Rightarrow> nat" ("sqrt\<down> _" [1000]) where
  "sqrt\<down> u = 2^(nat \<lfloor>lg u / 2\<rfloor>)"

lemma odd_ceiling_div2_add1:
  fixes k :: nat
  assumes "odd k"
  shows "nat \<lceil>k / 2\<rceil> = k div 2 + 1"
proof -
  have 0: "k / 2 = k div 2 + 1/2"
    using odd_two_times_div_two_succ[OF assms] by simp
  have "k / 2 \<noteq> of_int \<lfloor>k / 2\<rfloor>"
    by (simp add: 0)
  thus ?thesis
    unfolding ceiling_altdef by (auto, linarith)
qed

lemma sqrt_floor_div2:
  "sqrt\<down> (2^k) = 2^(k div 2)"
proof -
  have "(2::nat)^nat \<lfloor>log 2 (2 ^ k) / 2\<rfloor> = 2^nat \<lfloor>k / 2\<rfloor>"
    by simp
  also have "... = 2^(k div 2)"
    by (metis floor_divide_of_nat_eq nat_int of_nat_numeral)
  finally show ?thesis
    unfolding sqrt_floor_def lg_def by simp
qed

lemma sqrt_ceiling_div2:
  "even k \<Longrightarrow> sqrt\<up> (2^k) = 2^(k div 2)"
  unfolding sqrt_ceiling_def lg_def by auto

lemma sqrt_ceiling_div2_add1:
  "odd k \<Longrightarrow> sqrt\<up> (2^k) = 2^(k div 2 + 1)"
  unfolding sqrt_ceiling_def lg_def using odd_ceiling_div2_add1 by auto

lemma sqrt_ceiling_mul_floor:
  assumes "u = 2^k"
  shows "u = sqrt\<up> u * sqrt\<down> u"
proof -
  have 0: "sqrt\<up> u * sqrt\<down> u = 2^(nat \<lceil>k / 2\<rceil>) * 2^(nat \<lfloor>k / 2\<rfloor>)"
    using assms unfolding lg_def sqrt_ceiling_def sqrt_floor_def by simp
  show ?thesis
  proof (cases "even k")
    case True
    hence "(2::nat)^(nat \<lceil>k / 2\<rceil>) * 2^(nat \<lfloor>k / 2\<rfloor>) = 2^(k div 2 + k div 2)"
      by (auto simp: power_add)
    thus ?thesis
      using 0 True assms by auto
  next
    case False
    hence "(2::nat)^(nat \<lceil>k / 2\<rceil>) * 2^(nat \<lfloor>k / 2\<rfloor>) = 2^(k div 2 + 1) * 2^(k div 2)"
      using odd_ceiling_div2_add1 by (metis floor_divide_of_nat_eq nat_int of_nat_numeral)
    also have "... = 2^(k div 2 + 1 + k div 2)"
      by (auto simp: power_add)
    finally show ?thesis
      using 0 assms False by (metis False add.commute left_add_twice odd_two_times_div_two_succ)
  qed
qed

subsection "Index, High and Low"

definition high :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "high i u = i div (sqrt\<down> u)"

definition low :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "low i u = i mod (sqrt\<down> u)"

definition index :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "index i j u = i * sqrt\<down> u + j"

lemma index_high_low:
  "index (high i u) (low i u) u = i"
  unfolding index_def high_def low_def by simp

lemma index_eq_high_low:
  assumes "l < sqrt\<down> u" "i = index h l u"
  shows "h = high i u" "l = low i u"
  using assms unfolding index_def high_def low_def by auto

lemma high_mono:
  "i \<le> j \<Longrightarrow> high i u \<le> high j u"
  unfolding high_def using div_le_mono by blast

lemma high_lt_sqrt_ceiling:
  "i < sqrt\<down> u \<Longrightarrow> high i u < sqrt\<up> u"
  unfolding high_def by (simp add: sqrt_ceiling_def)

lemma low_lt_sqrt_floor:
  "low i u < sqrt\<down> u"
  unfolding low_def sqrt_floor_def by simp

lemma high_lt_k:
  "i < k * sqrt\<down> u \<Longrightarrow> high i u < k"
  using less_mult_imp_div_less unfolding high_def by blast

lemma high_geq_index_h0:
  "index h 0 u \<le> i \<Longrightarrow> h \<le> high i u"
  unfolding index_def high_def sqrt_floor_def using nat_le_iff_add by auto

lemma index_lt_u:
  assumes "u = 2^k" "i < sqrt\<up> u" "j < sqrt\<down> u"
  shows "index i j u < u"
proof -
  have 0: "sqrt\<down> u = 2^(k div 2)"
    by (simp add: assms(1) sqrt_floor_div2)
  show ?thesis
  proof (cases "even k")
    case True
    have "index i j u \<le> (sqrt\<up> u - 1) * sqrt\<down> u + j"
      using assms(2) index_def by auto
    also have "... \<le> (sqrt\<up> u - 1) * sqrt\<down> u + (sqrt\<down> u - 1)"
      using assms(3) by linarith
    also have "... = (2^(k div 2) - 1) * 2^(k div 2) + (2^(k div 2) - 1)"
      using 0 True assms(1) sqrt_ceiling_div2 by simp
    also have "... = 2^(k div 2 + k div 2) - 1"
      by (simp add: add.commute mult_eq_if power_add)
    also have "... = u - 1"
      using True assms(1) by (metis even_two_times_div_two mult_2)
    finally have "index i j u \<le> u - 1" .
    thus ?thesis
      using assms(1) by (simp add: Nat.le_diff_conv2)
  next
    case False
    have "index i j u \<le> (sqrt\<up> u - 1) * sqrt\<down> u + j"
      using assms(2) index_def by auto
    also have "... \<le> (sqrt\<up> u - 1) * sqrt\<down> u + (sqrt\<down> u - 1)"
      using assms(3) by linarith
    also have "... = (2^(k div 2 + 1) - 1) * 2^(k div 2) + (2^(k div 2) - 1)"
      using 0 False assms(1) sqrt_ceiling_div2_add1 by simp
    also have "... = 2^(k div 2 + 1) * 2^(k div 2) - 1"
      by (simp add: add.commute mult_eq_if)
    also have "... = u - 1"
      using False assms(1) 0 sqrt_ceiling_div2_add1 sqrt_ceiling_mul_floor by force
    finally have "index i j u \<le> u - 1" .
    thus ?thesis
      using assms(1) by (simp add: Nat.le_diff_conv2)
  qed
qed

end