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
  "high i u = i div (sqrt\<down> u)"

definition low :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "low i u = i mod (sqrt\<down> u)"

definition index :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "index i j u = i * sqrt\<down> u + j"

lemma index_high_low:
  "index (high i u) (low i u) u = i"
  unfolding index_def high_def low_def by simp

lemma high_mono:
  "i \<le> j \<Longrightarrow> high i u \<le> high j u"
  unfolding high_def using div_le_mono by blast

lemma low_lt_sqrt_floor:
  "low i u < sqrt\<down> u"
  unfolding low_def sqrt_floor_def by simp

lemma high_lt_k_if_sqrt_floor:
  "i < k * sqrt\<down> u \<Longrightarrow> high i u < k"
  using less_mult_imp_div_less unfolding high_def by blast

lemma high_geq_if_index_low0:
  "index i 0 u \<le> j \<Longrightarrow> i \<le> high j u"
  unfolding index_def high_def sqrt_floor_def using nat_le_iff_add by auto

lemma index_is_high_low:
  assumes "l < sqrt\<down> u" "i = index h l u"
  shows "h = high i u" "l = low i u"
  using assms unfolding index_def high_def low_def by auto

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
      using 0 True assms(1) even_sqrt_ceiling_div2 by simp
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
      using 0 False assms(1) odd_sqrt_ceiling_div2_add1 by simp
    also have "... = 2^(k div 2 + 1) * 2^(k div 2) - 1"
      by (simp add: add.commute mult_eq_if)
    also have "... = u - 1"
      using False assms(1) 0 odd_sqrt_ceiling_div2_add1 sqrt_ceiling_floor_id by force
    finally have "index i j u \<le> u - 1" .
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
    (\<forall>i < sqrt\<up> u. (list_pvEB s ! i \<longleftrightarrow> (\<exists>j < sqrt\<down> u. list_pvEB (cs!i) ! j)))"

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

lemma high_low_sqrt_bound:
  assumes "invar pvEB" "i < universe pvEB" "pvEB = Node u s cs"
  shows "high i u < sqrt\<up> u" "low i u < sqrt\<down> u"
    using assms high_lt_universe_summary by (auto simp add: low_def sqrt_floor_def)

lemma high_in_clusters:
  assumes "invar pvEB" "i < universe pvEB" "pvEB = Node u s cs"
  shows "cs!(high i u) \<in> set cs"
  using high_def assms high_low_sqrt_bound(1) by auto

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

lemma concat_nth_offset:
  assumes "\<forall>xs \<in> set xss. length xs = k" "0 < k" "n = length xss" "i < n" "j < k"
  shows "concat xss ! (i * k + j) = (xss!i) ! j"
  using assms
proof (induction xss arbitrary: i n)
  case (Cons xs xss)
  show ?case
  proof (cases "i = 0")
    case True
    thus ?thesis
      using Cons.prems by (auto simp: nth_append)
  next
    case False
    have "concat (xs # xss) ! (i * k + j) = concat xss ! ((i-1) * k + j)"
      using False Cons.prems nth_append_length_plus[of xs "concat xss"] by (simp add: add.assoc mult_eq_if)
    thus ?thesis
      using False Cons by simp
  qed
qed simp

lemma concat_update_div_mod:
  assumes "\<forall>xs \<in> set xss. length xs = k" "0 < k" "n = length xss" "i < n * k"
  shows "(concat xss)[i := x] = concat (xss[i div k := (xss!(i div k))[i mod k := x]])"
  using assms
  by (induction xss arbitrary: i n) 
     (auto simp: list_update_append div_geq mod_geq)

lemma list_pvEB_nth_index:
  assumes "invar pvEB" "i < sqrt\<up> u" "j < sqrt\<down> u" "pvEB = Node u s cs"
  shows "list_pvEB pvEB ! index i j u = list_pvEB (cs!i) ! j"
proof -
  have 0: "\<forall>c \<in> set (map list_pvEB cs). length c = sqrt\<down> u"
    using assms(1,4) length_list_pvEB_universe by auto
  have 1: "0 < sqrt\<down> u"
    by (simp add: sqrt_floor_def)
  have 2: "sqrt\<up> u = length (map list_pvEB cs)"
    using assms(1,4) by simp
  have "list_pvEB pvEB ! index i j u = concat (map list_pvEB cs) ! index i j u"
    by (simp add: assms(4))
  also have "... = ((map list_pvEB cs) ! i) ! j"
    using concat_nth_offset[OF 0 1 2 assms(2) assms(3)] index_def by simp
  finally show ?thesis
    using 2 assms(2) by auto
qed

corollary list_pvEB_nth_high_low:
  assumes "invar pvEB" "i < universe pvEB" "pvEB = Node u s cs" 
  shows "list_pvEB pvEB ! i = list_pvEB (cs!(high i u)) ! (low i u)"
  using list_pvEB_nth_index high_low_sqrt_bound index_high_low assms by metis

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
    using Node.prems(1,2) list_pvEB_nth_high_low by blast
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
  moreover have "\<forall>i < sqrt\<up> u. i \<noteq> h \<longrightarrow> (list_pvEB (insert s h) ! i \<longleftrightarrow> (\<exists>j < sqrt\<down> u. list_pvEB ((cs[h := insert (cs!h) l])!i) ! j))"
    using 1 3 Node.prems(1) insert_update by auto
  ultimately have "\<forall>i < sqrt\<up> u. (list_pvEB (insert s h) ! i \<longleftrightarrow> (\<exists>j < sqrt\<down> u. list_pvEB ((cs[h := insert (cs!h) l])!i) ! j))"
    using IHcs(2) 4 by metis

  hence "invar (Node u (insert s h) (cs[h := insert (cs!h) l]))"
    using 0 IHs 1 2 Node.prems(1) by auto
  thus ?case
    using defs by (metis Node.prems insert.psimps(2) insert_termination)
qed simp

subsection \<open>Minimum and Maximum\<close>

function (domintros, sequential) minimum :: "pvEB \<Rightarrow> nat option" where
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

declare minimum.domintros[simp] minimum.psimps[simp]

lemma minimum_termination_aux:
  assumes "invar pvEB"
  shows "minimum_dom pvEB \<and> (Some m = minimum pvEB \<longrightarrow> m < universe pvEB)"
  using assms
proof (induction pvEB arbitrary: m)
  case (Leaf bs)
  thus ?case 
    by (auto split: if_splits)
next
  case (Node u s cs)
  show ?case
  proof (cases "\<exists>h. Some h = minimum s")
    case True
    then obtain h where h_def: "Some h = minimum s"
      by blast
    hence *: "minimum_dom s" "h < universe s"
      using Node.prems Node.IH(1) by simp_all
    have "\<And>h'. minimum s = Some h' \<Longrightarrow> minimum_dom (cs ! h')"
    proof -
      fix h'
      assume "minimum s = Some h'"
      thus "minimum_dom (cs!h')"
        using h_def Node.prems Node.IH(2) *(2) by simp
    qed
    hence dom: "minimum_dom (Node u s cs)"
      using *(1) by simp
    show ?thesis
    proof cases
      assume "\<exists>l. Some l = minimum (cs!h)"
      hence "(Some m = minimum (Node u s cs) \<longrightarrow> m < universe (Node u s cs))"
        using Node.IH(2) Node.prems True h_def *(2) dom index_lt_u 
        by (auto split: option.splits, metis nth_mem)
      thus ?thesis using True h_def Node
        using dom by blast
    next
      assume "\<not>(\<exists>l. Some l = minimum (cs!h))"
      thus ?thesis
        using dom h_def by (auto split: option.splits)
    qed
  next
    case False
    hence 0: "minimum_dom (Node u s cs)"
      using False Node.IH(1) Node.prems by (auto, metis minimum.domintros(2)) 
    hence "None = minimum (Node u s cs)"
      using False by (auto split: option.splits)
    thus ?thesis
      using 0 by simp
  qed
qed

corollary minimum_termination:
  assumes "invar pvEB"
  shows "minimum_dom pvEB"
  using assms minimum_termination_aux by blast

corollary minimum_universe:
  assumes "invar pvEB" "Some m = minimum pvEB"
  shows "m < universe pvEB"
  using assms minimum_termination_aux by blast

lemma minimum_Some_list_pvEB_nth:
  assumes "invar pvEB" "Some m = minimum pvEB"
  shows "list_pvEB pvEB ! m"
  using assms
proof (induction pvEB arbitrary: m)
  case (Node u s cs)
  have dom: "minimum_dom (Node u s cs)"
    using Node.prems(1) minimum_termination by blast
  show ?case
  proof (cases "\<exists>h l. Some h = minimum s \<and> Some l = minimum (cs!h)")
    case True
    then obtain h l where defs: "Some h = minimum s" "Some l = minimum (cs!h)"
      by blast
    have 0: "cs!h \<in> set cs"
      using minimum_universe[OF _ defs(1)] Node.prems(1) by auto
    hence "l < sqrt\<down> u"
      using minimum_universe[OF _ defs(2)] Node.prems(1) by auto
    hence "h = high m u" "l = low m u"
      using index_is_high_low defs Node.prems(2) dom by (auto split: option.splits)
    hence "list_pvEB (Node u s cs) ! m = list_pvEB (cs!h) ! l"
      using list_pvEB_nth_high_low Node.prems minimum_universe by blast
    thus ?thesis
      using defs 0 Node.IH(2) Node.prems(1) by simp
  next
    case False
    thus ?thesis
      using Node.prems dom by (auto split: option.splits)
  qed
qed (auto split: if_splits)

lemma minimum_Some_not_list_pvEb_nth:
  assumes "invar pvEB" "Some m = minimum pvEB" "i < m"
  shows "\<not> list_pvEB pvEB ! i"
  using assms
proof (induction pvEB arbitrary: m i)
  case (Node u s cs)
  have dom: "minimum_dom (Node u s cs)"
    using Node.prems(1) minimum_termination by blast
  show ?case
  proof (cases "\<exists>h l. Some h = minimum s \<and> Some l = minimum (cs!h)")
    case True
    then obtain h l where defs: "Some h = minimum s" "Some l = minimum (cs!h)"
      by blast

    have 0: "h < sqrt\<up> u"
      using minimum_universe[OF _ defs(1)] Node.prems(1) by auto     
    hence 1: "l < sqrt\<down> u"
      using minimum_universe[OF _ defs(2)] Node.prems(1) by auto
    hence *: "h = high m u" "l = low m u"
      using index_is_high_low defs Node.prems(2) dom by (auto split: option.splits)

    show ?thesis
    proof (cases "i < index h 0 u")
      case True
      have A: "i = index (high i u) (low i u) u"
        using index_high_low by simp
      have B: "high i u < h"
        using True high_lt_k_if_sqrt_floor index_def by auto
      have C: "low i u < sqrt\<down> u"
        by (simp add: low_lt_sqrt_floor)
      have "\<forall>j < h. \<not> list_pvEB s ! j"
        using Node.IH(1) Node.prems(1) defs by simp
      hence "\<forall>i < h. \<forall>j < sqrt\<down> u. \<not> list_pvEB (cs!i) ! j"
        using Node.prems(1) *(1) 0 by simp
      hence "\<forall>i < h. \<forall>j < sqrt\<down> u. \<not> list_pvEB (Node u s cs) ! index i j u"
        using list_pvEB_nth_index 0 Node.prems(1) by auto
      thus ?thesis
        using A B C by metis
    next
      case False
      have "h = high i u"
        using False Node.prems(3) *(1) high_geq_if_index_low0 high_mono by (simp add: dual_order.antisym)
      hence A: "i = index h (low i u) u"
        by (simp add: index_high_low)
      hence B: "low i u < l"
        using * Node.prems(3) by (metis index_def index_high_low nat_add_left_cancel_less)
      have "\<forall>j < l. \<not> list_pvEB (cs!h) ! j"
        using Node.IH(2)[OF _ _ defs(2)] 0 Node.prems(1) by simp
      hence "\<forall>j < l. \<not> list_pvEB (Node u s cs) ! index h j u"
        using 0 1 Node.prems(1) list_pvEB_nth_index by auto
      then show ?thesis
        using A B by auto
    qed
  next
    case False
    thus ?thesis
      using Node.prems dom by (auto split: option.splits)
  qed
qed (auto split: if_splits)

lemma C: (* TODO *)
  assumes "invar pvEB" "i < universe pvEB"
  shows "(None = minimum pvEB) \<longleftrightarrow> (\<not> list_pvEB pvEB ! i)"
  sorry

corollary minimum_arg_min:
  assumes "invar pvEB" "Some m = minimum pvEB"
  shows "m = arg_min id (nth (list_pvEB pvEB))"
  using assms minimum_Some_list_pvEB_nth minimum_Some_not_list_pvEb_nth arg_min_nat_lemma 
  by (metis id_apply le_neq_implies_less)

subsection \<open>Predecessor and Successor\<close>

subsection \<open>Delete\<close>

subsection \<open>Build\<close>

end