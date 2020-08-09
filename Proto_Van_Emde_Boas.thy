theory Proto_Van_Emde_Boas
  imports Indexing
begin

section \<open>Proto van Emde Boas Tree\<close>

text \<open>
  \<^item> Extension 1:
    Introduce satellite data.
  \<^item> Extension 2:
    Do not store universe size u, instead just store k since u = 2^k.
    \<rightarrow> Simplifies Indexing.thy and eliminates lg and root operations.
  \<^item> Extension 3:
    Allow for duplicate keys.
\<close>

datatype pvEB =
  Leaf "bool list"
| Node nat pvEB "pvEB list"

fun uv :: "pvEB \<Rightarrow> nat" where
  "uv (Leaf bs) = length bs"
| "uv (Node u _ _) = u"

fun list_pvEB :: "pvEB \<Rightarrow> bool list" where
  "list_pvEB (Leaf bs) = bs"
| "list_pvEB (Node _ _ cs) = concat (map list_pvEB cs)"

fun invar :: "pvEB \<Rightarrow> bool" where
  "invar (Leaf bs) \<longleftrightarrow> length bs = 2"
| "invar (Node u s cs) \<longleftrightarrow> invar s \<and> (\<forall>c \<in> set cs. invar c \<and> uv c = sqrt\<down> u) \<and>
    (\<exists>k > 1. u = 2^k) \<and> length cs = sqrt\<up> u \<and> uv s = sqrt\<up> u \<and>
    (\<forall>i < sqrt\<up> u. list_pvEB s ! i \<longleftrightarrow> (\<exists>j < sqrt\<down> u. list_pvEB (cs!i) ! j))"

subsection \<open>Auxiliary Lemmas\<close>

lemma nat_less_induct':
  fixes P :: "nat \<Rightarrow> bool"
    and n :: "nat"
  assumes "\<And>n. (\<And>m. m < n \<Longrightarrow> P m) \<Longrightarrow> P n"
  shows "P n"
  using assms less_induct by blast

lemma low_lt_uv_high_clusters:
  assumes "invar pvEB" "i < uv pvEB" "pvEB = Node u s cs"
  shows "low i u < uv (cs!(high i u))"
  using assms high_def less_mult_imp_div_less low_lt_sqrt_floor sqrt_ceiling_mul_floor by auto

lemma high_lt_uv_summary:
  assumes "invar pvEB" "i < uv pvEB" "pvEB = Node u s cs"
  shows "high i u < uv s"
  using high_def assms less_mult_imp_div_less sqrt_ceiling_mul_floor by auto

lemma high_in_clusters:
  assumes "invar pvEB" "i < uv pvEB" "pvEB = Node u s cs"
  shows "cs!(high i u) \<in> set cs"
  using assms high_lt_uv_summary by auto

lemma length_list_pvEB_uv:
  "invar pvEB \<Longrightarrow> length (list_pvEB pvEB) = uv pvEB"
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
    using Node.prems sqrt_ceiling_mul_floor by auto
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
    using assms(1,4) length_list_pvEB_uv by auto
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
  assumes "invar pvEB" "i < uv pvEB" "pvEB = Node u s cs"
  shows "list_pvEB pvEB ! i = list_pvEB (cs!(high i u)) ! (low i u)"
  using list_pvEB_nth_index high_lt_sqrt_ceiling index_high_low assms
  by (metis high_lt_uv_summary invar.simps(2) low_lt_sqrt_floor)

subsection \<open>Build \<O>(u)\<close>

function (domintros) build :: "nat \<Rightarrow> pvEB" where
  "build 2 = Leaf (replicate 2 False)"
| "u \<noteq> 2 \<Longrightarrow> build u = Node u (build (sqrt\<up> u)) (replicate (sqrt\<up> u) (build (sqrt\<down> u)))"
  by blast+

declare build.domintros[simp] build.psimps[simp]

lemma build_termination:
  assumes "u = 2^k" "0 < k"
  shows "build_dom u"
  using assms
proof (induction k arbitrary: u rule: nat_less_induct')
  case (1 k)
  show ?case
  proof (cases "k \<le> 1")
    case True
    hence "u = 2"
      using "1.prems"(1,2) le_neq_implies_less power_one_right by blast
    thus ?thesis
      by simp
  next
    case False
    hence 0: "k div 2 < k" "sqrt\<down> u = 2^(k div 2)" "0 < k div 2"
      using "1.prems" sqrt_floor_div2 by auto
    hence 1: "u \<noteq> 2"
      using "1.prems"(1) False by (metis div_less less_2_cases_iff less_not_refl2 power_gt_expt)
    show ?thesis
    proof cases
      assume "even k"
      hence "build_dom (sqrt\<up> u)"
        using  "0"(1,3) "1.IH" "1.prems"(1) sqrt_ceiling_div2 by blast
      thus ?thesis
        using "1.IH"[OF 0] 1 by simp
    next
      assume "\<not> even k"
      hence 2: "k div 2 + 1 < k" "sqrt\<up> u = 2^(k div 2 + 1)" "0 < k div 2 + 1"
        using "0"(3) "1.prems"(1) sqrt_ceiling_div2_add1 by (presburger, auto)
      show ?thesis
        using "1.IH"[OF 0] 1 "1.IH"[OF 2] by simp
    qed
  qed
qed

lemma build_uv:
  assumes "u = 2^k" "0 < k"
  shows "uv (build u) = u"
  using assms build_termination by (cases "u \<noteq> 2") simp_all

lemma build_invar_empty:
  assumes "u = 2^k" "0 < k"
  shows "invar (build u) \<and> (\<forall>i < u. \<not> list_pvEB (build u) ! i)"
  using assms
proof (induction k arbitrary: u rule: nat_less_induct')
  case (1 k)
  define rep where [simp]: "rep = replicate (sqrt\<up> u) (build sqrt\<down> u)"
  show ?case
  proof (cases "k \<le> 1")
    case True
    hence "u = 2"
      using "1.prems"(1,2) le_neq_implies_less power_one_right by blast
    thus ?thesis
      by simp
  next
    case False
    hence evenk: "k div 2 < k" "sqrt\<down> u = 2^(k div 2)" "0 < k div 2"
      using "1.prems" sqrt_floor_div2 by auto
    hence "u \<noteq> 2"
      using "1.prems"(1) False by (metis div_less less_2_cases_iff less_not_refl2 power_gt_expt)
    have IH: "\<forall>c \<in> set rep. invar c \<and> uv c = sqrt\<down> u" "\<forall>j < sqrt\<down> u. \<not> list_pvEB (build sqrt\<down> u) ! j"
      using "1.IH"[OF evenk] evenk(2,3) build_uv by simp_all

    have "invar (build (sqrt\<up> u)) \<and> (\<forall>i < sqrt\<up> u. \<not> list_pvEB (build (sqrt\<up> u)) ! i) \<and> 
          uv (build (sqrt\<up> u)) = sqrt\<up> u"
    proof (cases "even k")
      case True
      thus ?thesis
        using evenk(1,3) "1.IH" "1.prems"(1) sqrt_ceiling_div2 build_uv by auto
    next
      case False
      hence "k div 2 + 1 < k" "sqrt\<up> u = 2^(k div 2 + 1)" "0 < k div 2 + 1"
        using evenk(3) "1.prems"(1) sqrt_ceiling_div2_add1 by (presburger, auto)
      then show ?thesis
        using "1.IH" build_uv by presburger
    qed
    hence INVAR: "invar (build u)"
      using "1.prems" "1.IH"[OF evenk] IH False \<open>u \<noteq> 2\<close> build_termination by simp

    hence "\<forall>i < u. list_pvEB (build u) ! i = list_pvEB (rep!high i u) ! low i u"
      using \<open>u \<noteq> 2\<close> "1.prems" list_pvEB_nth_high_low build_uv build.psimps(2) build_termination rep_def by metis
    hence "\<forall>i < u. list_pvEB (build u) ! i = list_pvEB (build (sqrt\<down> u)) ! low i u"
      using "1.prems"(1) high_def less_mult_imp_div_less sqrt_ceiling_mul_floor by auto
    thus ?thesis
      using INVAR by (simp add: IH low_lt_sqrt_floor)
  qed
qed

subsection \<open>Membership \<O>(lg lg u)\<close>

function (domintros, sequential) member :: "pvEB \<Rightarrow> nat \<Rightarrow> bool" where
  "member (Leaf bs) i = bs!i"
| "member (Node u _ cs) i = member (cs!(high i u)) (low i u)"
  by pat_completeness auto

declare member.domintros[simp] member.psimps[simp]

lemma member_termination:
  assumes "invar pvEB" "i < uv pvEB"
  shows "member_dom (pvEB, i)"
  using assms
proof (induction pvEB arbitrary: i)
  case (Node u s cs)
  thus ?case
    using high_in_clusters low_lt_sqrt_floor by auto
qed simp

lemma member_list_pvEB_nth:
  assumes "invar pvEB" "i < uv pvEB"
  shows "member pvEB i \<longleftrightarrow> list_pvEB pvEB ! i"
  using assms
proof (induction pvEB arbitrary: i)
  case (Node u s cs)
  have 0: "cs!(high i u) \<in> set cs" "invar (cs!(high i u))"
    using Node.prems(1,2) high_in_clusters by auto
  hence 1: "low i u < uv (cs!(high i u))"
    using low_lt_uv_high_clusters Node.prems(1,2) by blast
  have "member (Node u s cs) i = list_pvEB (cs!(high i u)) ! (low i u)"
    using Node(2)[OF 0 1] Node.prems member.psimps(2) member_termination by blast
  also have "... = list_pvEB (Node u s cs) ! i"
    using Node.prems(1,2) list_pvEB_nth_high_low by blast
  finally show ?case .
qed simp

subsection \<open>Insert \<O>(lg u)\<close>

function (domintros, sequential) insert :: "pvEB \<Rightarrow> nat \<Rightarrow> pvEB" where
  "insert (Leaf bs) i = Leaf (bs[i := True])"
| "insert (Node u s cs) i = Node u (insert s (high i u)) (cs[high i u := insert (cs!high i u) (low i u)])"
  by pat_completeness auto

declare insert.domintros[simp] insert.psimps[simp]

lemma insert_termination:
  assumes "invar pvEB" "i < uv pvEB"
  shows "insert_dom (pvEB, i)"
  using assms
proof (induction pvEB arbitrary: i)
  case (Node u s cs)
  thus ?case
    using high_lt_uv_summary low_lt_sqrt_floor by auto
qed simp

lemma insert_uv:
  assumes "invar pvEB" "i < uv pvEB"
  shows "uv (insert pvEB i) = uv pvEB"
  using assms by (cases pvEB) (auto simp: insert_termination)

lemma insert_update:
  assumes "invar pvEB" "i < uv pvEB"
  shows "list_pvEB (insert pvEB i) = (list_pvEB pvEB)[i := True]"
  using assms
proof (induction pvEB arbitrary: i)
  case (Node u s cs)
  define h where "h = high i u"
  define l where "l = low i u"
  note defs = h_def l_def

  have IH: "list_pvEB (insert (cs!h) l) = (list_pvEB (cs!h))[l := True]"
    using high_in_clusters[OF Node.prems] low_lt_uv_high_clusters[OF Node.prems]
          Node.prems Node.IH(2) defs by simp
  have 0: "\<forall>c \<in> set (map list_pvEB cs). length c = sqrt\<down> u"
    using Node.prems(1) length_list_pvEB_uv by auto
  have 1: "0 < sqrt\<down> u" "sqrt\<up> u = length (map list_pvEB cs)" "i < sqrt\<up> u * sqrt\<down> u"
    using Node.prems sqrt_ceiling_mul_floor by (auto simp: sqrt_floor_def)

  have "list_pvEB (insert (Node u s cs) i) = concat (map list_pvEB (cs[h := insert (cs!h) l]))"
    using defs Node.prems by (auto simp: insert_termination)
  also have "... = concat ((map list_pvEB cs)[h := list_pvEB (insert (cs!h) l)])"
    by (simp add: map_update)
  also have "... = concat ((map list_pvEB cs)[h := (list_pvEB (cs!h))[l := True]])"
    using IH by argo
  also have "... = concat ((map list_pvEB cs)[h := (map list_pvEB cs ! h)[l := True]])"
    using nth_map Node.prems h_def high_lt_uv_summary by auto
  also have "... = (concat (map list_pvEB cs))[i := True]"
    using concat_update_div_mod[OF 0 1] defs high_def low_def by auto
  also have "... = (list_pvEB (Node u s cs))[i := True]"
    by simp
  finally show ?case .
qed simp

lemma insert_invar:
  assumes "invar pvEB" "i < uv pvEB"
  shows "invar (insert pvEB i)"
  using assms
proof (induction pvEB arbitrary: i)
  case (Node u s cs)
  define h where "h = high i u"
  define l where "l = low i u"
  note defs = h_def l_def

  have IHcs: "invar (insert (cs!h) l)" "uv (insert (cs!h) l) = sqrt\<down> u"
    using high_in_clusters[OF Node.prems] low_lt_uv_high_clusters[OF Node.prems]
          insert_uv Node.prems Node.IH(2) defs by auto
  hence 0: "\<forall>c \<in> set (cs[h := insert (cs!h) l]). invar c \<and> uv c = sqrt\<down> u"
    using Node.prems(1) set_update_subset_insert by fastforce
  have IHs: "invar (insert s h)"
    using Node.prems Node.IH(1) high_lt_uv_summary defs by auto
  have 1: "uv (insert s h) = sqrt\<up> u"
    using Node.prems defs high_lt_uv_summary insert_uv by auto
  have 2: "length (cs[h := insert (cs!h) l]) = sqrt\<up> u"
    using Node.prems(1) by simp

  have 3: "h < uv (insert s h)"
    using Node.prems defs 1 high_lt_uv_summary by auto
  have 4: "l < uv (insert (cs ! h) l)"
    using IHcs(2) defs low_def sqrt_floor_def by auto
  have "list_pvEB (insert s h) ! h"
    using insert_update[OF IHs] defs 1 3 Node.prems(1) insert_update length_list_pvEB_uv by auto
  moreover have "list_pvEB ((cs[h := insert (cs!h) l])!h) ! l"
    using 1 2 3 4 insert_update IHcs(2) Node.prems(1) length_list_pvEB_uv by auto
  moreover have "\<forall>i < sqrt\<up> u. i \<noteq> h \<longrightarrow> (list_pvEB (insert s h) ! i \<longleftrightarrow>
                (\<exists>j < sqrt\<down> u. list_pvEB ((cs[h := insert (cs!h) l])!i) ! j))"
    using 1 3 Node.prems(1) insert_update by auto
  ultimately have "\<forall>i < sqrt\<up> u. (list_pvEB (insert s h) ! i \<longleftrightarrow>
                  (\<exists>j < sqrt\<down> u. list_pvEB ((cs[h := insert (cs!h) l])!i) ! j))"
    using IHcs(2) 4 by metis

  hence "invar (Node u (insert s h) (cs[h := insert (cs!h) l]))"
    using 0 IHs 1 2 Node.prems(1) by auto
  thus ?case
    using defs by (metis Node.prems insert.psimps(2) insert_termination)
qed simp

subsection \<open>Minimum and Maximum\<close>

subsubsection \<open>Minimum \<O>(lg u)\<close>

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
        | None \<Rightarrow> None \<comment>\<open>impossible case, requires simultaneous proof of termination, uv, Some_nth, None_empty\<close>
      )
    | None \<Rightarrow> None
  )"
  by pat_completeness auto

declare minimum.domintros[simp] minimum.psimps[simp]

lemma minimum_termination_uv:
  assumes "invar pvEB"
  shows "minimum_dom pvEB \<and> (Some m = minimum pvEB \<longrightarrow> m < uv pvEB)"
  using assms
proof (induction pvEB arbitrary: m)
  case (Node u s cs)
  thus ?case
    by (auto split: option.splits, metis index_lt_u nth_mem)
qed (auto split: if_splits)

corollary minimum_termination:
  assumes "invar pvEB"
  shows "minimum_dom pvEB"
  using assms minimum_termination_uv by blast

corollary minimum_uv:
  assumes "invar pvEB" "Some m = minimum pvEB"
  shows "m < uv pvEB"
  using assms minimum_termination_uv by blast

lemma minimum_Some_nth:
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
      using minimum_uv[OF _ defs(1)] Node.prems(1) by auto
    hence "l < sqrt\<down> u"
      using minimum_uv[OF _ defs(2)] Node.prems(1) by auto
    hence "h = high m u" "l = low m u"
      using index_eq_high_low defs Node.prems(2) dom by (auto split: option.splits)
    hence "list_pvEB (Node u s cs) ! m = list_pvEB (cs!h) ! l"
      using list_pvEB_nth_high_low Node.prems minimum_uv by blast
    thus ?thesis
      using defs 0 Node.IH(2) Node.prems(1) by simp
  next
    case False
    thus ?thesis
      using Node.prems dom by (auto split: option.splits)
  qed
qed (auto split: if_splits)

lemma minimum_Some_not_nth:
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
      using minimum_uv[OF _ defs(1)] Node.prems(1) by auto
    hence 1: "l < sqrt\<down> u"
      using minimum_uv[OF _ defs(2)] Node.prems(1) by auto
    hence *: "h = high m u" "l = low m u"
      using index_eq_high_low defs Node.prems(2) dom by (auto split: option.splits)

    show ?thesis
    proof (cases "i < index h 0 u")
      case True
      have A: "i = index (high i u) (low i u) u"
        using index_high_low by simp
      have B: "high i u < h"
        using True high_lt_k index_def by auto
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
        using False Node.prems(3) *(1) high_geq_index_h0 high_mono by (simp add: dual_order.antisym)
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

corollary minimum_is_arg_min:
  assumes "invar pvEB" "Some m = minimum pvEB"
  shows "is_arg_min id (nth (list_pvEB pvEB)) m"
  unfolding is_arg_min_def using assms minimum_Some_nth minimum_Some_not_nth by (metis id_apply)

lemma minimum_None_empty:
  assumes "invar pvEB"
  shows "(None = minimum pvEB) \<longleftrightarrow> (\<forall>i < uv pvEB. \<not> list_pvEB pvEB ! i)"
proof standard
  assume "None = minimum pvEB"
  thus "\<forall>i < uv pvEB. \<not> list_pvEB pvEB ! i" using assms
  proof (induction pvEB)
    case (Node u s cs)
    have "minimum_dom (Node u s cs)"
      using Node.prems(2) minimum_termination by blast
    thus ?case
      using Node
      apply (auto simp del: list_pvEB.simps split: option.splits)
      subgoal premises prems for k i
      proof -
        have "list_pvEB (Node u s cs) ! i = list_pvEB (cs!high i u) ! low i u"
          using list_pvEB_nth_high_low[OF Node.prems(2)] by (simp add: prems(11-12))
        thus ?thesis
          using low_lt_sqrt_floor prems(2,11,12) Node.prems(2) high_lt_uv_summary prems(13) by auto
      qed
      using minimum_Some_nth minimum_uv by force
  qed (auto simp: less_2_cases_iff split: if_splits)
next
  assume *: "\<forall>i < uv pvEB. \<not> list_pvEB pvEB ! i"
  show "None = minimum pvEB"
  proof (rule ccontr)
    assume "\<not> None = minimum pvEB"
    then obtain m where "Some m = minimum pvEB" "m < uv pvEB" "list_pvEB pvEB ! m"
      using minimum_Some_nth minimum_uv assms not_Some_eq by metis
    thus False
      using * by blast
  qed
qed

subsubsection \<open>Maximum \<O>(lg u)\<close> (* symmetric to Minimum *)

subsection \<open>Predecessor and Successor\<close>

subsubsection \<open>Predecessor \<O>(lg u lg lg u)\<close> (* symmetric to Successor *)

subsubsection \<open>Successor \<O>(lg u lg lg u)\<close>

function (domintros, sequential) successor :: "pvEB \<Rightarrow> nat \<Rightarrow> nat option" where
  "successor (Leaf bs) i = (
    if i = 0 \<and> bs!1 then Some 1
    else None
  )"
| "successor (Node u s cs) i = (
    case successor (cs!high i u) (low i u) of
      Some offset \<Rightarrow> Some (index (high i u) offset u)
    | None \<Rightarrow> (
      case successor s (high i u) of
        Some succ \<Rightarrow> (
          case minimum (cs!succ) of
            Some offset \<Rightarrow> Some (index succ offset u)
          | None \<Rightarrow> None \<comment>\<open>impossible case\<close>
        )
      | None \<Rightarrow> None
    )
  )"
  by pat_completeness auto

declare successor.domintros[simp] successor.psimps[simp]

lemma successor_termination:
  assumes "invar pvEB" "i < uv pvEB"
  shows "successor_dom (pvEB, i)"
  using assms 
proof (induction pvEB arbitrary: i)
  case (Node u s cs)
  thus ?case 
    using high_lt_uv_summary low_lt_sqrt_floor by auto
qed simp

lemma successor_uv:
  assumes "invar pvEB" "Some j = successor pvEB i" "i < uv pvEB"
  shows "j < uv pvEB"
  using assms
proof (induction pvEB arbitrary: i j)
  case (Node u s cs)
  have IHs: "\<And>succ. Some succ = successor s (high i u) \<Longrightarrow> succ < uv s"
    using Node.IH(1) Node.prems(1,3) high_lt_uv_summary by auto
  have 0: "cs!high i u \<in> set cs"
    using Node.prems(1,3) high_in_clusters by blast
  have IHo: "\<And>offset. Some offset = successor (cs!high i u) (low i u) \<Longrightarrow> offset < uv (cs!high i u)"
    using Node.IH(2)[OF 0] Node.prems(1,3) high_in_clusters by (auto simp: low_lt_sqrt_floor)
  show ?case
    using Node.prems IHs IHo high_lt_uv_summary minimum_uv index_lt_u
    by (auto simp: successor_termination split: option.splits, metis nth_mem)
qed (auto split: if_splits)

lemma successor_lt:
  assumes "invar pvEB" "Some j = successor pvEB i" "i < uv pvEB"
  shows "i < j"
  using assms
proof (induction pvEB arbitrary: i j)
  case (Node u s cs)
  show ?case
  proof (cases "\<exists>off. Some off = successor (cs!high i u) (low i u)")
    case True
    then obtain off where *: "Some off = successor (cs!high i u) (low i u)"
      by blast
    have "cs!high i u \<in> set cs" "invar (cs!high i u)"
      using Node.prems(1,3) high_in_clusters by auto
    hence "low i u < off"
      using Node.prems Node.IH(2) * successor_uv low_lt_uv_high_clusters by blast
    hence "i < index (high i u) off u"
      using index_high_low index_low_mono by metis
    thus ?thesis
      using * Node.prems successor_termination by (auto split: option.splits)
  next
    case False
    then obtain succ off where *: "Some succ = successor s (high i u)" "Some off = minimum (cs!succ)"
      using Node.prems successor_termination by (auto split: option.splits)
    hence "high i u < succ"
      using Node.IH(1) Node.prems(1,3) high_lt_uv_summary by auto
    hence "i < index succ off u"
      using index_high_low index_mono low_lt_sqrt_floor by metis
    then show ?thesis
      using False * Node.prems successor_termination by (auto split: option.splits)
  qed
qed (auto split: if_splits)

lemma successor_Some_nth:
  assumes "invar pvEB" "Some j = successor pvEB i" "i < uv pvEB"
  shows "list_pvEB pvEB ! j"
  using assms
proof (induction pvEB arbitrary: i j)
  case (Node u s cs)
  show ?case
  proof (cases "\<exists>off. Some off = successor (cs!high i u) (low i u)")
    case True
    then obtain off where *: "Some off = successor (cs!high i u) (low i u)"
      by blast
    have high: "cs!high i u \<in> set cs" "invar (cs!high i u)"
      using Node.prems(1,3) high_in_clusters by auto
    hence IH: "list_pvEB (cs!high i u) ! off"
      using Node.prems Node.IH(2) * low_lt_uv_high_clusters by blast
    have "off < sqrt\<down> u"
      using successor_uv[OF high(2) *] low_lt_uv_high_clusters[OF Node.prems(1) Node.prems(3)]
            Node.prems(1) high(1) by simp
    moreover have "j = index (high i u) off u"
      using * Node.prems successor_termination by (auto split: option.splits)
    ultimately have "list_pvEB (Node u s cs) ! j = list_pvEB (cs!high i u) ! off"
      using Node.prems index_eq_high_low list_pvEB_nth_high_low successor_uv by metis
    thus ?thesis
      using IH by blast
  next
    case False
    then obtain succ off where *: "Some succ = successor s (high i u)" "Some off = minimum (cs!succ)"
      using Node.prems successor_termination by (auto split: option.splits)
    hence "list_pvEB (cs!succ) ! off"
      using minimum_Some_nth Node.prems(1,3) high_lt_uv_summary successor_uv[OF _ *(1)] by auto
    have "list_pvEB (Node u s cs) ! j = list_pvEB (Node u s cs) ! index succ off u"
      using False * Node.prems successor_termination by (auto split: option.splits)
    also have "... = list_pvEB (cs!succ) ! off"
      using list_pvEB_nth_index successor_uv[OF _ *(1)] minimum_uv[OF _ *(2)] Node.prems(1,3) high_lt_uv_summary by auto
    finally show ?thesis
      using \<open>list_pvEB (cs!succ) ! off\<close> by blast
  qed
qed (auto split: if_splits)

lemma successor_None_partial_empty:
  assumes "invar pvEB" "i < uv pvEB"
  shows "(None = successor pvEB i) \<longleftrightarrow> (\<forall>j < uv pvEB. i < j \<longrightarrow> \<not> list_pvEB pvEB ! j)"
proof standard
  assume None: "None = successor pvEB i"
  show "\<forall>j < uv pvEB. i < j \<longrightarrow> \<not> list_pvEB pvEB ! j"
  proof (standard, standard, standard)
    fix j
    assume "j < uv pvEB" "i < j"
    thus "\<not> list_pvEB pvEB ! j" using assms None
    proof (induction pvEB arbitrary: i j)
      case (Node u s cs)
      show ?case
      proof (cases "\<exists>succ. Some succ = successor s (high i u)")
        case True
        then obtain succ where succ_def: "Some succ = successor s (high i u)"
          by blast
        have 0: "high i u < uv s"
          using Node.prems(3,4) high_lt_uv_summary by blast
        hence "list_pvEB s ! succ"
          using Node.prems(3) succ_def successor_Some_nth by auto
        hence 1: "\<exists>i < sqrt\<down> u. list_pvEB (cs!succ) ! i"
          using Node.prems(3) 0 succ_def successor_uv by fastforce
        have "None = minimum (cs!succ)"
          using succ_def Node.prems successor_termination by (auto split: option.splits)
        hence "\<forall>i < sqrt\<down> u. \<not> list_pvEB (cs!succ) ! i"
          using minimum_None_empty 0 Node.prems(3) succ_def successor_uv by force
        thus ?thesis
          using 1 by blast
      next
        case False
        show ?thesis
        proof cases
          assume "high j u \<le> high i u"
          hence *: "high j u = high i u"
            using Node.prems(2) high_mono by (simp add: dual_order.antisym less_imp_le_nat)
          have "None = successor (cs!high i u) (low i u)"
            using Node.prems successor_termination by (auto split: option.splits)
          moreover have "low i u < low j u"
            using index_high_low index_low_mono * Node.prems(2) by (metis not_less_iff_gr_or_eq)
          moreover have "low j u < uv (cs!high i u)"
            using low_lt_uv_high_clusters Node.prems(1,3) * by metis
          ultimately have "\<not> list_pvEB (cs!high i u) ! low j u"
            using Node.IH(2) Node.prems(3,4) high_in_clusters by auto
          thus ?thesis
            using Node.prems(1,3) list_pvEB_nth_high_low * by presburger
        next
          assume *: "\<not> high j u \<le> high i u"
          have "None = successor s (high i u)"
            using False by (metis not_Some_eq)
          hence "\<forall>j < uv s. \<forall>k < sqrt\<down> u. high i u < j \<longrightarrow> \<not> list_pvEB (cs!j) ! k"
            using Node.IH(1) Node.prems(1,3) by auto
          thus ?thesis using * Node.prems(1,3)
            by (meson high_lt_uv_summary list_pvEB_nth_high_low low_lt_sqrt_floor le_less_linear)
        qed
      qed
    qed (auto simp: less_2_cases_iff split: if_splits)
  qed
next
  assume *: "\<forall>j < uv pvEB. i < j \<longrightarrow> \<not> list_pvEB pvEB ! j"
  show "None = successor pvEB i"
  proof (rule ccontr)
    assume "\<not> None = successor pvEB i"
    then obtain j where "Some j = successor pvEB i"
      by (metis not_None_eq)
    thus False
      using assms * successor_uv successor_lt successor_Some_nth by blast
  qed
qed

lemma successor_None_not_nth:
  assumes "invar pvEB" "Some k = successor pvEB i" "i < uv pvEB" "i < j" "j < k"
  shows "\<not> list_pvEB pvEB ! j"
  using assms
proof (induction pvEB arbitrary: i j k)
  case (Node u s cs)
  show ?case
  proof (cases "\<exists>off. Some off = successor (cs!high i u) (low i u)")
    case True
    then obtain off where *: "Some off = successor (cs!high i u) (low i u)"
      by blast
    have high: "cs!high i u \<in> set cs" "invar (cs!high i u)"
      using Node.prems(1,3) high_in_clusters by auto
    hence IH: "\<forall>j. low i u < j \<and> j < off \<longrightarrow> \<not> list_pvEB (cs!high i u) ! j"
      using Node.prems Node.IH(2) * low_lt_uv_high_clusters by blast
    have "k = index (high i u) off u"
      using * Node.prems(1,2,3) successor_termination by (auto split: option.splits)
    moreover have "off < sqrt\<down> u"
      using successor_uv[OF high(2) *] low_lt_uv_high_clusters[OF Node.prems(1) Node.prems(3)]
            Node.prems(1) high(1) by simp
    ultimately have "high i u = high k u"
      using index_eq_high_low(1) by auto
    hence "high i u = high j u"
      using Node.prems(4,5) high_mono by (metis dual_order.antisym le_eq_less_or_eq)
    moreover have "k < uv (Node u s cs)"
      using successor_uv Node.prems(1,2,3) by blast
    ultimately have "list_pvEB (Node u s cs) ! j = list_pvEB (cs!high i u) ! low j u"
      using list_pvEB_nth_high_low Node.prems(1,5) less_trans by metis
    moreover have "low i u < low j u" "low j u < off"
      using index_high_low index_low_mono Node.prems(4,5) \<open>high i u = high j u\<close> \<open>k = index (high i u) off u\<close>
      by (metis not_less_iff_gr_or_eq less_imp_triv linorder_neqE_nat)+
    ultimately show ?thesis
      using IH by blast
  next
    case False
    then obtain succ off where *: "Some succ = successor s (high i u)" "Some off = minimum (cs!succ)"
      using Node.prems successor_termination by (auto split: option.splits)
    hence "k = index succ off u"
      using False Node.prems(1,2,3) successor_termination by (auto split: option.splits)
    moreover have "off < sqrt\<down> u"
      using minimum_uv[OF _ *(2)] successor_uv[OF _ *(1)] Node.prems(1,3) high_lt_uv_summary by auto
    ultimately have "succ = high k u"
      using index_eq_high_low(1) by blast
    hence "high j u \<le> succ"
      using Node.prems(5) high_mono by auto
    then consider (A) "high i u = high j u" | (B) "high i u < high j u" "high j u < succ" | (C) "high j u = succ"
      using Node.prems(4) high_mono le_eq_less_or_eq by auto
    thus ?thesis
    proof cases
      case A
      have "None = successor (cs!high i u) (low i u)"
        using False by (metis option.exhaust)
      hence empty: "\<forall>j < uv (cs!high i u). low i u < j \<longrightarrow> \<not> list_pvEB (cs!high i u) ! j"
        using successor_None_partial_empty Node.prems(1,3) high_in_clusters by auto
      have "j < uv (Node u s cs)"
        using Node.prems(1-3,5) less_trans successor_uv by blast
      hence "list_pvEB (Node u s cs) ! j = list_pvEB (cs!high i u) ! (low j u)"
        using list_pvEB_nth_high_low Node.prems(1) A by metis
      moreover have "low i u < low j u"
        using A Node.prems(4) index_high_low index_low_mono by (metis not_less_iff_gr_or_eq)
      moreover have "low j u < uv (cs!high i u)"
        using A Node.prems(1) \<open>j < uv (Node u s cs)\<close> low_lt_uv_high_clusters by auto
      ultimately show ?thesis
        using empty by blast
    next
      case B
      hence "\<not> list_pvEB s ! high j u"
        using Node.IH(1)[OF _ *(1)] Node.prems(1,3) high_lt_uv_summary by auto
      moreover have "high j u < sqrt\<up> u"
        using successor_uv[OF _ *(1)] B(2) Node.prems(1) Node.prems(3) high_lt_uv_summary by auto
      ultimately have "\<forall>i < sqrt\<down> u. \<not> list_pvEB (cs!high j u) ! i"
        using Node.prems(1) by simp
      moreover have "low j u < sqrt\<down> u"
        by (simp add: low_lt_sqrt_floor)
      ultimately show ?thesis
        using Node.prems(1) \<open>high j u < sqrt\<up> u\<close> index_high_low list_pvEB_nth_index by metis
    next
      case C
      have "invar (cs!succ)"
        using successor_uv[OF _ *(1)] Node.prems(1,3) high_lt_uv_summary by auto
      hence empty: "\<forall>i < off. \<not> list_pvEB (cs!succ) ! i"
        using minimum_Some_not_nth *(2) by blast
      have "k < uv (Node u s cs)"
        using successor_uv Node.prems(1,2,3) by blast
      hence "list_pvEB (Node u s cs) ! j = list_pvEB (cs!succ) ! low j u"
        using list_pvEB_nth_high_low Node.prems(1,5) less_trans C by blast
      moreover have "low j u < off"
        using C Node.prems(5) \<open>k = index succ off u\<close> index_high_low index_low_mono by (metis less_imp_triv nat_neq_iff)
      ultimately show ?thesis
        using empty by blast
    qed
  qed
qed (auto split: if_splits)

corollary successor_is_arg_min:
  assumes "invar pvEB" "Some j = successor pvEB i" "i < uv pvEB"
  shows "is_arg_min id (\<lambda>j. list_pvEB pvEB ! j \<and> i < j \<and> (\<forall>k. i < k \<and> k < j \<longrightarrow> \<not> list_pvEB pvEB ! k)) j"
  using assms successor_lt successor_Some_nth successor_None_not_nth unfolding is_arg_min_def by (metis id_apply)

subsection \<open>Delete \<O>(sqrt u lg lg u)\<close> (* slow for proto van Emde Boas trees *)

end
