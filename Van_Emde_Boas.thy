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

lemma odd_ceiling_div2_add1:
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

lemma even_sqrt_ceiling_div2:
  "even k \<Longrightarrow> sqrt\<up> (2^k) = 2^(k div 2)"
  unfolding sqrt_ceiling_def lg_def by auto

lemma odd_sqrt_ceiling_div2_add1:
  "odd k \<Longrightarrow> sqrt\<up> (2^k) = 2^(k div 2 + 1)"
  unfolding sqrt_ceiling_def lg_def using odd_ceiling_div2_add1 by auto

lemma sqrt_ceiling_floor_id:
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

definition high :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "high x u = x div (sqrt\<down> u)"

definition low :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "low x u = x mod (sqrt\<down> u)"

definition index :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "index x y u = x * sqrt\<down> u + y"

lemma index_high_low:
  "index (high x u) (low x u) u = x"
  unfolding index_def high_def low_def by simp

lemma index_is_high_low:
  assumes "l < sqrt\<down> u" "i = index h l u"
  shows "h = high i u" "l = low i u"
  using assms unfolding index_def high_def low_def by auto

lemma index_lt_u:
  assumes "u = 2^k" "x < sqrt\<up> u" "y < sqrt\<down> u"
  shows "index x y u < u"
proof -
  have 0: "sqrt\<down> u = 2^(k div 2)"
    by (simp add: assms(1) sqrt_floor_div2)
  show ?thesis
  proof (cases "even k")
    case True
    have "index x y u \<le> (sqrt\<up> u - 1) * sqrt\<down> u + y"
      using assms(2) index_def by auto
    also have "... \<le> (sqrt\<up> u - 1) * sqrt\<down> u + (sqrt\<down> u - 1)"
      using assms(3) by linarith
    also have "... = (2^(k div 2) - 1) * 2^(k div 2) + (2^(k div 2) - 1)"
      using 0 True assms(1) even_sqrt_ceiling_div2 by simp
    also have "... = 2^(k div 2 + k div 2) - 1"
      by (simp add: add.commute mult_eq_if power_add)
    also have "... = u - 1"
      using True assms(1) by (metis even_two_times_div_two mult_2)
    finally have "index x y u \<le> u - 1" .
    thus ?thesis
      using assms(1) by (simp add: Nat.le_diff_conv2)
  next
    case False
    have "index x y u \<le> (sqrt\<up> u - 1) * sqrt\<down> u + y"
      using assms(2) index_def by auto
    also have "... \<le> (sqrt\<up> u - 1) * sqrt\<down> u + (sqrt\<down> u - 1)"
      using assms(3) by linarith
    also have "... = (2^(k div 2 + 1) - 1) * 2^(k div 2) + (2^(k div 2) - 1)"
      using 0 False assms(1) odd_sqrt_ceiling_div2_add1 by simp
    also have "... = 2^(k div 2 + 1) * 2^(k div 2) - 1"
      by (simp add: add.commute mult_eq_if)
    also have "... = u - 1"
      using False assms(1) 0 odd_sqrt_ceiling_div2_add1 sqrt_ceiling_floor_id by force
    finally have "index x y u \<le> u - 1" .
    thus ?thesis
      using assms(1) by (simp add: Nat.le_diff_conv2)
  qed
qed


section \<open>Proto van Emde Boas Tree\<close>

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

lemma clusters_universe_div2:
  assumes "invar pvEB" "pvEB = Node (2^k) s cs"
  shows "\<forall>c \<in> set cs. universe c = 2^(k div 2)"
  using assms sqrt_floor_div2 by (auto)

lemma low_lt_universe_high_clusters:
  assumes "invar pvEB" "i < universe pvEB" "pvEB = Node u s cs"
  shows "low i u < universe (cs!(high i u))"
  using high_def low_def assms less_mult_imp_div_less sqrt_ceiling_floor_id sqrt_floor_div2 by auto

lemma high_lt_universe_summary:
  assumes "invar pvEB" "i < universe pvEB" "pvEB = Node u s cs"
  shows "high i u < universe s"
  using high_def assms less_mult_imp_div_less sqrt_ceiling_floor_id by auto

lemma high_in_clusters:
  assumes "invar pvEB" "i < universe pvEB" "pvEB = Node u s cs"
  shows "cs!(high i u) \<in> set cs"
  using high_def assms less_mult_imp_div_less sqrt_ceiling_floor_id by auto

lemma length_list_pvEB_universe:
  "invar pvEB \<Longrightarrow> length (list_pvEB pvEB) = universe pvEB"
proof (induction pvEB)
  case (Node u s cs)
  have 0: "\<forall>c \<in> set cs. length (list_pvEB c) = sqrt\<down> u"
    using Node(2,3) by simp
  have "length (list_pvEB (Node u s cs)) = sum_list (map (length \<circ> list_pvEB) cs)"
    by (simp add: length_concat)
  also have "... = (\<Sum>_\<leftarrow>cs. sqrt\<down> u)"
    using 0 map_eq_conv[of "length \<circ> list_pvEB" cs] by (metis comp_apply)
  also have "... = length cs * sqrt\<down> u"
    by (simp add: sum_list_triv)
  finally show ?case
    using Node.prems sqrt_ceiling_floor_id by auto
qed simp

lemma concat_nth_div_mod:
  assumes "\<forall>xs \<in> set xss. length xs = k" "0 < k" "n = length xss" "i < n * k"
  shows "concat xss ! i = (xss!(i div k)) ! (i mod k)"
  using assms 
  by (induction xss arbitrary: i n) 
     (auto simp: nth_append div_geq mod_geq)

lemma concat_update_div_mod:
  assumes "\<forall>xs \<in> set xss. length xs = k" "0 < k" "n = length xss" "i < n * k"
  shows "(concat xss)[i := x] = concat (xss[i div k := (xss!(i div k))[i mod k := x]])"
  using assms 
  by (induction xss arbitrary: i n) 
     (auto simp: list_update_append div_geq mod_geq)

lemma list_pvEB_nth_clusters_high_low:
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
    using concat_nth_div_mod[OF 0 1 2] assms(3) by simp
  thus ?thesis
    unfolding high_def low_def
    using \<open>universe pvEB = sqrt\<up> u * sqrt\<down> u\<close> assms less_mult_imp_div_less by simp
qed

subsection \<open>Membership \<O>(lg lg u)\<close>

function (domintros, sequential) member :: "pvEB \<Rightarrow> nat \<Rightarrow> bool" where
  "member (Leaf bs) i = bs!i"
| "member (Node u _ cs) i = member (cs!(high i u)) (low i u)"
  by pat_completeness auto

declare member.domintros[simp] member.psimps[simp]

lemma member_termination:
  assumes "invar pvEB" "i < universe pvEB"
  shows "member_dom (pvEB, i)"
  using assms
proof (induction pvEB arbitrary: i)
  case (Node u s cs)
  have 0: "cs!(high i u) \<in> set cs" "invar (cs!(high i u))"
    using Node.prems(1,2) high_in_clusters by auto
  hence 1: "low i u < universe (cs!(high i u))"
    using low_lt_universe_high_clusters Node.prems(1,2) by blast
  have "member_dom (cs!(high i u), low i u)"
    using Node.IH(2)[OF 0 1] by blast
  thus ?case
    by simp
qed simp

lemma member_list_pvEB_nth:
  assumes "invar pvEB" "i < universe pvEB"
  shows "member pvEB i \<longleftrightarrow> list_pvEB pvEB ! i"
  using assms
proof (induction pvEB arbitrary: i)
  case (Node u s cs)
  have 0: "cs!(high i u) \<in> set cs" "invar (cs!(high i u))"
    using Node.prems(1,2) high_in_clusters by auto
  hence 1: "low i u < universe (cs!(high i u))"
    using low_lt_universe_high_clusters Node.prems(1,2) by blast
  have "member (Node u s cs) i = list_pvEB (cs!(high i u)) ! (low i u)"
    using Node(2)[OF 0 1] Node.prems member.psimps(2) member_termination by blast
  also have "... = list_pvEB (Node u s cs) ! i"
    using Node.prems(1,2) list_pvEB_nth_clusters_high_low by blast
  finally show ?case .
qed simp

subsection \<open>Insert \<O>(lg u)\<close>

function (domintros, sequential) insert :: "pvEB \<Rightarrow> nat \<Rightarrow> pvEB" where
  "insert (Leaf bs) i = Leaf (bs[i := True])"
| "insert (Node u s cs) i = (
    let h = high i u in
    let l = low i u in
    Node u (insert s h) (cs[h := insert (cs!h) l]))"
  by pat_completeness auto

declare insert.domintros[simp] insert.psimps[simp]

lemma insert_termination:
  assumes "invar pvEB" "i < universe pvEB"
  shows "insert_dom (pvEB, i)"
  using assms
proof (induction pvEB arbitrary: i)
  case (Node u s cs)
  have "insert_dom (s, high i u)"
    using Node.IH(1) Node.prems high_lt_universe_summary by auto
  moreover have "insert_dom (cs!(high i u), low i u)"
    using Node.IH(2) Node.prems by (meson high_in_clusters invar.simps(2) low_lt_universe_high_clusters)
  ultimately show ?case
    by simp
qed simp

lemma insert_universe:
  assumes "invar pvEB" "i < universe pvEB"
  shows "universe (insert pvEB i) = universe pvEB"
  using assms by (induction pvEB arbitrary: i) (auto simp: Let_def insert_termination)

lemma insert_update:
  assumes "invar pvEB" "i < universe pvEB"
  shows "list_pvEB (insert pvEB i) = (list_pvEB pvEB)[i := True]"
  using assms
proof (induction pvEB arbitrary: i)
  case (Node u s cs)
  define h where "h = high i u"
  define l where "l = low i u"
  note defs = h_def l_def

  have IH: "list_pvEB (insert (cs!h) l) = (list_pvEB (cs!h))[l := True]"
    using high_in_clusters[OF Node.prems] low_lt_universe_high_clusters[OF Node.prems] 
          Node.prems Node.IH(2) defs by simp
  have 0: "\<forall>c \<in> set (map list_pvEB cs). length c = sqrt\<down> u"
    using Node.prems(1) length_list_pvEB_universe by auto
  have 1: "0 < sqrt\<down> u" "sqrt\<up> u = length (map list_pvEB cs)" "i < sqrt\<up> u * sqrt\<down> u"
    using Node.prems sqrt_ceiling_floor_id by (auto simp: sqrt_floor_def)

  have "list_pvEB (insert (Node u s cs) i) = concat (map list_pvEB (cs[h := insert (cs!h) l]))"
    using defs Node.prems by (auto simp: insert_termination, meson list_pvEB.simps(2))
  also have "... = concat ((map list_pvEB cs)[h := list_pvEB (insert (cs!h) l)])"
    by (simp add: map_update)
  also have "... = concat ((map list_pvEB cs)[h := (list_pvEB (cs!h))[l := True]])"
    using IH by argo
  also have "... = concat ((map list_pvEB cs)[h := (map list_pvEB cs ! h)[l := True]])"
    using nth_map Node.prems h_def high_lt_universe_summary by auto
  also have "... = (concat (map list_pvEB cs))[i := True]"
    using concat_update_div_mod[OF 0 1] defs high_def low_def by auto
  also have "... = (list_pvEB (Node u s cs))[i := True]"
    by simp
  finally show ?case .
qed simp

lemma insert_invar:
  assumes "invar pvEB" "i < universe pvEB"
  shows "invar (insert pvEB i)"
  using assms
proof (induction pvEB arbitrary: i)
  case (Node u s cs)
  define h where "h = high i u"
  define l where "l = low i u"
  note defs = h_def l_def

  have IHcs: "invar (insert (cs!h) l)" "universe (insert (cs!h) l) = sqrt\<down> u"
    using high_in_clusters[OF Node.prems] low_lt_universe_high_clusters[OF Node.prems] 
          insert_universe Node.prems Node.IH(2) defs by auto
  hence 0: "\<forall>c \<in> set (cs[h := insert (cs!h) l]). invar c \<and> universe c = sqrt\<down> u"
    using Node.prems(1) set_update_subset_insert by fastforce
  have IHs: "invar (insert s h)"
    using Node.prems Node.IH(1) high_lt_universe_summary defs by auto
  have 1: "universe (insert s h) = sqrt\<up> u"
    using Node.prems defs high_lt_universe_summary insert_universe by auto
  have 2: "length (cs[h := insert (cs!h) l]) = sqrt\<up> u"
    using Node.prems(1) by simp

  have 3: "h < universe (insert s h)"
    using Node.prems defs 1 high_lt_universe_summary by auto
  have 4: "l < universe (insert (cs ! h) l)"
    using IHcs(2) defs low_def sqrt_floor_def by auto
  have "list_pvEB (insert s h) ! h"
    using insert_update[OF IHs] defs 1 3 Node.prems(1) insert_update length_list_pvEB_universe by auto
  moreover have "list_pvEB ((cs[h := insert (cs!h) l])!h) ! l"
    using 1 2 3 4 insert_update IHcs(2) Node.prems(1) length_list_pvEB_universe by auto
  moreover have "\<forall>i \<noteq> h. (list_pvEB (insert s h) ! i \<longleftrightarrow> (\<exists>j. list_pvEB ((cs[h := insert (cs!h) l])!i) ! j))"
    using 1 3 Node.prems(1) insert_update by auto
  ultimately have "\<forall>i. (list_pvEB (insert s h) ! i \<longleftrightarrow> (\<exists>j. list_pvEB ((cs[h := insert (cs!h) l])!i) ! j))"
    by fast

  hence "invar (Node u (insert s h) (cs[h := insert (cs!h) l]))"
    using 0 IHs 1 2 Node.prems(1) by auto
  thus ?case
    using defs by (metis Node.prems insert.psimps(2) insert_termination)
qed simp

subsection \<open>Minimum and Maximum\<close>

function (sequential) minimum :: "pvEB \<Rightarrow> nat option" where
  "minimum (Leaf bs) = (
    if bs!0 then Some 0
    else if bs!1 then Some 1
    else None
  )"
| "minimum (Node u s cs) = (
    case minimum s of
      Some h \<Rightarrow> (
        case minimum (cs!h) of
          Some l \<Rightarrow> Some (index h l u)
        | None \<Rightarrow> None
      )
    | None \<Rightarrow> None
  )"
  by pat_completeness auto
termination minimum sorry (* TODO *)

lemma minimum_universe:
  assumes "invar pvEB" "Some i = minimum pvEB"
  shows "i < universe pvEB"
  using assms index_lt_u
  by (induction pvEB arbitrary: i)
     (auto simp: split: if_splits option.splits, metis nth_mem)

lemma minimum_Some_list_pvEB_nth:
  assumes "invar pvEB" "Some i = minimum pvEB"
  shows "list_pvEB pvEB ! i"
  using assms
proof (induction pvEB arbitrary: i)
  case (Node u s cs)
  show ?case
  proof (cases "\<exists>h l. Some h = minimum s \<and> Some l = minimum (cs!h)")
    case True
    then obtain h l where defs: "Some h = minimum s" "Some l = minimum (cs!h)"
      by blast
    have 0: "cs!h \<in> set cs"
      using minimum_universe[OF _ defs(1)] Node.prems(1) by auto
    hence "l < sqrt\<down> u"
      using minimum_universe[OF _ defs(2)] Node.prems(1) by auto
    hence "h = high i u" "l = low i u"
      using index_is_high_low defs Node.prems(2) by (auto split: option.splits)
    hence "list_pvEB (Node u s cs) ! i = list_pvEB (cs!h) ! l"
      using list_pvEB_nth_clusters_high_low Node.prems minimum_universe by blast
    thus ?thesis
      using defs 0 Node.IH(2) Node.prems(1) by simp
  next
    case False
    thus ?thesis
      using Node.prems by (auto split: option.splits)
  qed
qed (auto split: if_splits)

lemma AUX:
  assumes "invar pvEB" "pvEB = Node u s cs" "i < universe pvEB" "j < low i u"
  shows "list_pvEB pvEB ! index (high i u) j u = list_pvEB (cs!(high i u)) ! j"
  using assms
  sorry
  (* by (smt Suc_leI high_in_clusters high_lt_universe_summary index_is_high_low(1) index_is_high_low(2) index_lt_u invar.simps(2) length_list_pvEB_universe list_pvEB_nth_clusters_high_low low_lt_universe_high_clusters of_nat_1 of_nat_add of_nat_le_iff of_nat_less_iff plus_1_eq_Suc universe.simps(2) universe_2powk) *)

lemma B: (* TODO *)
  assumes "invar pvEB" "Some i = minimum pvEB"
  shows "\<forall>j < i. \<not>(list_pvEB pvEB ! j)"
  using assms
proof (induction pvEB arbitrary: i)
  case (Node u s cs)
  show ?case
  proof (cases "\<exists>h l. Some h = minimum s \<and> Some l = minimum (cs!h)")
    case True
    then obtain h l where defs: "Some h = minimum s" "Some l = minimum (cs!h)"
      by blast

    have 0: "cs!h \<in> set cs"
      using minimum_universe[OF _ defs(1)] Node.prems(1) by auto
    hence "l < sqrt\<down> u"
      using minimum_universe[OF _ defs(2)] Node.prems(1) by auto
    hence *: "h = high i u" "l = low i u"
      using index_is_high_low defs Node.prems(2) by (auto split: option.splits)

    have "\<forall>j < h. \<not> list_pvEB s ! j"
      using Node.IH(1) Node.prems(1) defs by simp

    hence "\<forall>i < h. \<forall>j. \<not> list_pvEB (cs!i) ! j"
      using Node.prems(1) by auto

    hence "\<forall>j < index h 0 u. \<not> list_pvEB (Node u s cs) ! j"
      sorry
      (* by (smt Node.prems(1) True \<open>\<forall>j<h. \<not> list_pvEB s ! j\<close> add.right_neutral dual_order.strict_trans high_def index_def index_lt_u invar.simps(2) length_list_pvEB_universe less_mult_imp_div_less linorder_neqE_nat list_pvEB_nth_clusters_high_low minimum_Some_list_pvEB_nth minimum_universe nat_zero_less_power_iff pos2 sqrt_floor_div2 universe.simps(2)) *)
    hence 1: "\<forall>j < index (high i u) 0 u. \<not> list_pvEB (Node u s cs) ! j"
      using * by blast

    (* list_pvEB pvEB ! i = list_pvEB (cs!(high i u)) ! (low i u) *)
    have "\<forall>j < l. \<not> list_pvEB (cs!h) ! j"
      using Node.IH(2)[OF 0 _ defs(2)] 0 Node.prems(1) by simp
    hence "\<forall>j < low i u. \<not> list_pvEB (cs!high i u) ! j"
      using * by blast
    hence "\<forall>j < low i u. \<not> list_pvEB (Node u s cs) ! index (high i u) j u"
      using AUX Node.prems minimum_universe by blast
    hence 2: "\<forall>j \<in> set [index (high i u) 0 u..<index (high i u) (low i u) u]. \<not> list_pvEB (Node u s cs) ! j"
      sorry      
      (* by (smt "*"(2) add.right_neutral add_diff_cancel_left' in_set_conv_nth index_def length_upt less_imp_of_nat_less nth_upt of_nat_add of_nat_less_imp_less) *)

    have "\<forall>j \<in> set [0..<index (high i u) (low i u) u]. \<not> list_pvEB (Node u s cs) ! j"
      using 1 2 by auto

    thus ?thesis
      using index_high_low by simp

  next
    case False
    thus ?thesis
      using Node.prems by (auto split: option.splits)
  qed
qed (auto split: if_splits)

lemma C: (* TODO *)
  assumes "invar pvEB" "None = minimum pvEB"
  shows "\<forall>i < universe pvEB. \<not>(list_pvEB pvEB ! i)"
  sorry

lemma minimum_arg_min:
  assumes "invar pvEB" "Some i = minimum pvEB"
  shows "i = arg_min id (nth (list_pvEB pvEB))"
  using assms minimum_Some_list_pvEB_nth B arg_min_nat_lemma by (metis id_apply le_neq_implies_less)

subsection \<open>Predecessor and Successor\<close>

subsection \<open>Delete\<close>

subsection \<open>Build\<close>

end