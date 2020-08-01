theory Van_Emde_Boas
  imports Complex_Main
begin

section \<open>Sqrt Ceiling and Floor\<close>

definition lg :: "real \<Rightarrow> real" where
  "lg \<equiv> log 2"

definition sqrt_ceiling :: "nat \<Rightarrow> nat" ("sqrt\<up> _" [1000]) where 
  "sqrt\<up> u = 2^(nat \<lceil>lg u / 2\<rceil>)"

definition sqrt_floor :: "nat \<Rightarrow> nat" ("sqrt\<down> _" [1000]) where
  "sqrt\<down> u = 2^(nat \<lfloor>lg u / 2\<rfloor>)"

lemma odd_ceiling_div2_add_1:
  assumes "odd (k::nat)"
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

lemma sqrt_ceiling_floor_id:
  assumes "u = 2^k"
  shows "u = sqrt\<up> u * sqrt\<down> u"
proof -
  have *: "sqrt\<up> u * sqrt\<down> u = 2^(nat \<lceil>k / 2\<rceil>) * 2^(nat \<lfloor>k / 2\<rfloor>)"
    using assms unfolding lg_def sqrt_ceiling_def sqrt_floor_def by simp
  show ?thesis
  proof (cases "even k")
    case True
    hence "(2::nat)^(nat \<lceil>k / 2\<rceil>) * 2^(nat \<lfloor>k / 2\<rfloor>) = 2^(k div 2 + k div 2)"
      by (auto simp: power_add)
    also have "... = u"
      using assms True by auto
    finally show ?thesis
      using * by argo
  next
    case False
    hence "(2::nat)^(nat \<lceil>k / 2\<rceil>) * 2^(nat \<lfloor>k / 2\<rfloor>) = 2^(k div 2 + 1) * 2^(k div 2)"
      using odd_ceiling_div2_add_1 by (metis floor_divide_of_nat_eq nat_int of_nat_numeral)
    also have "... = 2^(k div 2 + 1 + k div 2)"
      by (auto simp: power_add)
    also have "... = u"
      using assms False by (metis False add.commute left_add_twice odd_two_times_div_two_succ)
    finally show ?thesis
      using * by argo
  qed
qed

definition high :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "high x u = x div (sqrt\<down> u)"

definition low :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "low x u = x mod (sqrt\<down> u)"

definition index :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "index x y u = x * sqrt\<down> u + y"

lemma index_high_low:
  "index (high x u) (low x u) u = x"
  unfolding index_def high_def low_def by simp


section \<open>Proto van Emde Boas Structure\<close>

datatype pvEB =
  Leaf "bool list"
| Node nat pvEB "pvEB list"

fun universe :: "pvEB \<Rightarrow> nat" where
  "universe (Leaf _) = 2"
| "universe (Node u _ _) = u"

fun list_pvEB :: "pvEB \<Rightarrow> bool list" where
  "list_pvEB (Leaf bs) = bs"
| "list_pvEB (Node _ _ cs) = concat (map list_pvEB cs)"

fun invar :: "pvEB \<Rightarrow> bool" where
  "invar (Leaf bs) \<longleftrightarrow> length bs = 2"
| "invar (Node u s cs) \<longleftrightarrow> invar s \<and> (\<forall>c \<in> set cs. invar c) \<and> (\<exists>k > 1. u = 2^k) \<and> 
    universe s = sqrt\<up> u \<and> length cs = sqrt\<up> u \<and> (\<forall>c \<in> set cs. universe c = sqrt\<down> u) \<and>
    (\<forall>i. (list_pvEB s ! i \<longleftrightarrow> (\<exists>j. list_pvEB (cs!i) ! j)))"

subsection \<open>Auxiliary Lemmas\<close>

lemma universe_2powk:
  "invar pvEB \<Longrightarrow> \<exists>k \<ge> 1. universe pvEB = 2^k"
  by (cases pvEB) auto

lemma low_lt_universe_high:
  assumes "invar pvEB" "pvEB = Node u s cs" "i < universe pvEB"
  shows "low i u < universe (cs!(high i u))"
  unfolding high_def low_def using assms less_mult_imp_div_less sqrt_ceiling_floor_id sqrt_floor_div2 by auto

lemma high_elem_clusters:
  assumes "invar pvEB" "pvEB = Node u s cs" "i < universe pvEB"
  shows "cs!(high i u) \<in> set cs"
  unfolding high_def using assms less_mult_imp_div_less sqrt_ceiling_floor_id by auto

lemma length_list_pvEB_universe:
  "invar pvEB \<Longrightarrow> length (list_pvEB pvEB) = universe pvEB"
proof (induction pvEB)
  case (Node u s cs)
  have 0: "\<forall>c \<in> set cs. length (list_pvEB c) = sqrt\<down> u"
    using Node(2,3) by simp
  have "length (list_pvEB (Node u s cs)) = length (concat (map list_pvEB cs))"
    by simp
  also have "... = sum_list (map (length \<circ> list_pvEB) cs)"
    by (simp add: length_concat)
  also have "... = (\<Sum>_\<leftarrow>cs. sqrt\<down> u)"
    using 0 map_eq_conv[of "length \<circ> list_pvEB" cs] by (metis comp_apply)
  also have "... = length cs * sqrt\<down> u"
    by (simp add: sum_list_triv)
  finally show ?case
    using Node.prems sqrt_ceiling_floor_id by auto
qed simp

(* slice *)
(* slice (list_pvEB pvEB) (i * sqrt\<down> u) ((i + 1) * sqrt\<down> u) = list_pvEB (cs ! i) *)

lemma concat_i_div_mod:
  assumes "\<forall>xs \<in> set xss. length xs = k" "0 < k" "n = length xss" "i < n * k"
  shows "concat xss ! i = (xss!(i div k)) ! (i mod k)"
  using assms by (induction xss arbitrary: i n) (auto simp: nth_append div_if mod_geq)

lemma list_pvEB_i_high_low:
  assumes "invar pvEB" "pvEB = Node u s cs" "i < universe pvEB"
  shows "list_pvEB pvEB ! i = list_pvEB (cs!(high i u)) ! (low i u)"
proof -
  have 0: "\<forall>c \<in> set (map list_pvEB cs). length c = sqrt\<down> u"
    using assms(1,2) length_list_pvEB_universe by auto
  have 1: "0 < sqrt\<down> u"
    by (simp add: sqrt_floor_def)
  have 2: "sqrt\<up> u = length (map list_pvEB cs)"
    using assms(1,2) by simp
  have "universe pvEB = sqrt\<up> u * sqrt\<down> u"
    using assms(1,2) sqrt_ceiling_floor_id by auto
  hence "concat (map list_pvEB cs) ! i = ((map list_pvEB cs)!(i div (sqrt\<down> u))) ! (i mod (sqrt\<down> u))"
    using concat_i_div_mod[OF 0 1 2] assms(3) by simp
  thus ?thesis
    unfolding high_def low_def
    using \<open>universe pvEB = sqrt\<up> u * sqrt\<down> u\<close> assms less_mult_imp_div_less by simp
qed

subsection \<open>Membership\<close>

function (sequential) member :: "pvEB \<Rightarrow> nat \<Rightarrow> bool" where
  "member (Leaf bs) i = bs!i"
| "member (Node u _ cs) i = member (cs!(high i u)) (low i u)"
  by pat_completeness auto
termination member
  sorry

lemma member_list_pvEB:
  assumes "invar pvEB" "i < universe pvEB"
  shows "member pvEB i \<longleftrightarrow> list_pvEB pvEB ! i"
  using assms
proof (induction pvEB arbitrary: i)
  case (Node u s cs)
  have 0: "cs!(high i u) \<in> set cs" "invar (cs!(high i u))"
    using Node.prems(1,2) high_elem_clusters by auto
  hence 1: "low i u < universe (cs!(high i u))"
    using low_lt_universe_high Node.prems(1,2) by blast
  have "member (Node u s cs) i = list_pvEB (cs!(high i u)) ! (low i u)"
    using Node(2)[OF 0 1] by simp
  also have "... = list_pvEB (Node u s cs) ! i"
    using Node.prems(1,2) list_pvEB_i_high_low by blast
  finally show ?case .
qed simp

subsection \<open>Insert\<close>

subsection \<open>Minimum and Maximum\<close>

subsection \<open>Predecessor and Successor\<close>

subsection \<open>Delete\<close>

subsection \<open>Build\<close>

end