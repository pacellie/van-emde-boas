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
    (\<forall>i < sqrt\<up> u. (list_pvEB s ! i \<longleftrightarrow> (\<exists>j < sqrt\<down> u. list_pvEB (cs!i) ! j)))"

subsection \<open>Auxiliary Lemmas\<close>

lemma universe_2powk:
  "invar pvEB \<Longrightarrow> \<exists>k \<ge> 1. universe pvEB = 2^k"
  by (cases pvEB) auto

lemma low_lt_universe_high:
  assumes "invar pvEB" "i < universe pvEB" "pvEB = Node u s cs"
  shows "low i u < universe (cs!(high i u))"
  unfolding high_def low_def using assms less_mult_imp_div_less sqrt_ceiling_floor_id sqrt_floor_div2 by auto

lemma high_lt_universe_summary:
  assumes "invar pvEB" "i < universe pvEB" "pvEB = Node u s cs"
  shows "high i u < universe s"
  unfolding high_def using assms less_mult_imp_div_less sqrt_ceiling_floor_id by auto

lemma high_elem_clusters:
  assumes "invar pvEB" "i < universe pvEB" "pvEB = Node u s cs"
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

lemma AUX: (* TODO *)
  assumes "\<forall>xs \<in> set xss. length xs = k" "0 < k" "n = length xss" "i < n * k"
  shows "(concat xss)[i := x] = concat (xss[i div k := (xss!(i div k))[i mod k := x]])"
  using assms
proof (induction xss arbitrary: i n)
  case (Cons xs xss)
  then show ?case
  proof (cases "i < k")
    case True
    then show ?thesis
      using Cons apply (auto)
      by (simp add: list_update_append1)
  next
    case False
    thm Cons
    have "(concat xss)[i - k := x] = concat (xss[(i - k) div k := (xss ! ((i - k) div k))[(i - k) mod k := x]])"
      using Cons.IH[of "n-k" "i-k"]
      by (metis False One_nat_def assms(2) insert_iff less_diff_conv2 linorder_not_less list.set(2) list.size(4) local.Cons(1) local.Cons(2) local.Cons(4) local.Cons(5) mult.left_neutral nat_distrib(1))
    then show ?thesis
      apply (auto split: nat.split)
      using Euclidean_Division.div_eq_0_iff False assms(2) apply blast
      by (simp add: Cons.prems(1) False assms(2) div_geq list_update_append mod_geq)
  qed
qed simp

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

function (domintros, sequential) member :: "pvEB \<Rightarrow> nat \<Rightarrow> bool" where
  "member (Leaf bs) i = bs!i"
| "member (Node u _ cs) i = member (cs!(high i u)) (low i u)"
  by pat_completeness auto

lemma member_termination:
  assumes "invar pvEB" "i < universe pvEB"
  shows "member_dom (pvEB, i)"
  using assms
proof (induction pvEB arbitrary: i)
  case (Leaf bs)
  thus ?case 
    by (simp add: member.domintros(1))
next
  case (Node u s cs)
  have 0: "cs!(high i u) \<in> set cs" "invar (cs!(high i u))"
    using Node.prems(1,2) high_elem_clusters by auto
  hence 1: "low i u < universe (cs!(high i u))"
    using low_lt_universe_high Node.prems(1,2) by blast
  have "member_dom (cs!(high i u), low i u)"
    using Node.IH(2)[OF 0 1] by blast
  thus ?case
    by (simp add: member.domintros(2))
qed

lemma member_list_pvEB_nth:
  assumes "invar pvEB" "i < universe pvEB"
  shows "member pvEB i \<longleftrightarrow> list_pvEB pvEB ! i"
  using assms
proof (induction pvEB arbitrary: i)
  case (Leaf bs)
  thus ?case
    by (simp add: member.domintros(1) member.psimps(1))
next
  case (Node u s cs)
  have 0: "cs!(high i u) \<in> set cs" "invar (cs!(high i u))"
    using Node.prems(1,2) high_elem_clusters by auto
  hence 1: "low i u < universe (cs!(high i u))"
    using low_lt_universe_high Node.prems(1,2) by blast
  have "member (Node u s cs) i = list_pvEB (cs!(high i u)) ! (low i u)"
    using Node(2)[OF 0 1] Node.prems member.psimps(2) member_termination by blast
  also have "... = list_pvEB (Node u s cs) ! i"
    using Node.prems(1,2) list_pvEB_i_high_low by blast
  finally show ?case .
qed

subsection \<open>Insert\<close>

function (sequential) insert :: "pvEB \<Rightarrow> nat \<Rightarrow> pvEB" where
  "insert (Leaf bs) i = Leaf (bs[i := True])"
| "insert (Node u s cs) i = (
    let h = high i u in
    let l = low i u in
    Node u (insert s h) (cs[h := insert (cs!h) l]))"
  by pat_completeness auto
termination insert
  sorry (* TODO *)

lemma insert_universe:
  "invar pvEB \<Longrightarrow> universe (insert pvEB i) = universe pvEB"
  by (induction pvEB arbitrary: i) (auto simp: Let_def)

lemma insert_update: (* TODO *)
  assumes "invar pvEB" "i < universe pvEB"
  shows "list_pvEB (insert pvEB i) = (list_pvEB pvEB)[i := True]"
  using assms
proof (induction pvEB arbitrary: i)
  case (Leaf bs)
  thus ?case
    by simp
next
  case (Node u s cs)
  define h where "h = high i u"
  define l where "l = low i u"
  note defs = h_def l_def
  have IH: "list_pvEB (insert (cs!h) l) = (list_pvEB (cs!h))[l := True]"
    using high_elem_clusters[OF Node.prems] low_lt_universe_high[OF Node.prems] Node.prems Node.IH(2) defs by simp
  have 0: "\<forall>c \<in> set (map list_pvEB cs). length c = sqrt\<down> u"
    using Node.prems(1) length_list_pvEB_universe by auto
  have 1: "0 < sqrt\<down> u"
    by (simp add: sqrt_floor_def)
  have 2: "sqrt\<up> u = length (map list_pvEB cs)"
    using Node.prems(1) by auto

  have "list_pvEB (insert (Node u s cs) i) = concat (map list_pvEB (cs[h := insert (cs!h) l]))"
    using defs by (auto simp: Let_def)
  also have "... = concat ((map list_pvEB cs)[h := list_pvEB (insert (cs!h) l)])"
    by (simp add: map_update)
  also have "... = concat ((map list_pvEB cs)[h := (list_pvEB (cs!h))[l := True]])"
    using IH by argo
  also have "... = (concat (map list_pvEB cs))[i := True]"
    using AUX[OF 0 1 2] Node.prems(1,2) defs high_def low_def high_lt_universe_summary sqrt_ceiling_floor_id by auto
  also have "... = (list_pvEB (Node u s cs))[i := True]"
    by simp
  finally show ?case .
qed

lemma insert_invar:
  assumes "invar pvEB" "i < universe pvEB"
  shows "invar (insert pvEB i)"
  using assms
proof (induction pvEB arbitrary: i)
  case (Leaf bs)
  thus ?case
    by simp
next
  case (Node u s cs)
  define h where "h = high i u"
  define l where "l = low i u"
  note defs = h_def l_def
  have "invar (insert s h)"
    using Node.prems Node.IH(1) high_lt_universe_summary defs by auto
  moreover have "invar (insert (cs!h) l)"
    using high_elem_clusters[OF Node.prems] low_lt_universe_high[OF Node.prems] Node.prems Node.IH(2) defs by simp
  ultimately show ?case (* TODO *)
    using defs Node.prems(1) apply (auto simp: Let_def insert_universe)
    using set_update_subset_insert apply fastforce
      apply (metis in_set_conv_nth insert_universe length_list_update nth_list_update_eq nth_list_update_neq)
     apply (metis Node.prems(1) Node.prems(2) high_elem_clusters high_lt_universe_summary insert_update length_list_pvEB_universe low_lt_universe_high nth_list_update)
    by (metis Node.prems(1) Node.prems(2) high_lt_universe_summary insert_update length_list_pvEB_universe nth_list_update)
qed

subsection \<open>Minimum and Maximum\<close>

subsection \<open>Predecessor and Successor\<close>

subsection \<open>Delete\<close>

subsection \<open>Build\<close>

end