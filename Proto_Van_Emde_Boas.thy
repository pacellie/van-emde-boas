theory Proto_Van_Emde_Boas
  imports Indexing
begin

section \<open>Proto van Emde Boas Tree\<close>

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
    (\<forall>i < sqrt\<up> u. (list_pvEB s ! i \<longleftrightarrow> (\<exists>j < sqrt\<down> u. list_pvEB (cs!i) ! j)))"

subsection \<open>Auxiliary Lemmas\<close>

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

subsection \<open>Build \<O>(u)\<close> (* TODO *)

function (sequential) build :: "nat \<Rightarrow> pvEB" where
  "build u = (
    if u = 2 then
      Leaf (replicate 2 False)
    else
      Node u (build (sqrt\<up> u)) (replicate (sqrt\<up> u) (build (sqrt\<down> u)))
  )"
  by pat_completeness auto
termination sorry

lemma build_simps[simp]:
  "u = 2 \<Longrightarrow> build u = Leaf (replicate 2 False)"
  "u \<noteq> 2 \<Longrightarrow> build u = Node u (build (sqrt\<up> u)) (replicate (sqrt\<up> u) (build (sqrt\<down> u)))"
  by simp_all

lemma build_uv:
  "uv (build u) = u"
  by simp

declare build.simps[simp del]

lemma nat01_induct:
  fixes n
  assumes "P 0" "P 1" "\<And>n. 0 < n \<Longrightarrow> P n \<Longrightarrow> P (Suc n)"
  shows "P n"
  using assms nat_induct_non_zero by (metis gr0I)

lemma build_empty:
  assumes "u = 2^k" "0 < k" "i < u"
  shows "\<not> list_pvEB (build u) ! i"
  sorry

lemma build_invar:
  assumes "u = 2^k" "0 < k"
  shows "invar (build u)"
  sorry

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
  have 0: "cs!(high i u) \<in> set cs" "invar (cs!(high i u))"
    using Node.prems(1,2) high_in_clusters by auto
  hence 1: "low i u < uv (cs!(high i u))"
    using low_lt_uv_high_clusters Node.prems(1,2) by blast
  have "member_dom (cs!(high i u), low i u)"
    using Node.IH(2)[OF 0 1] by blast
  thus ?case
    by simp
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
| "insert (Node u s cs) i = (
    let h = high i u in
    let l = low i u in
    Node u (insert s h) (cs[h := insert (cs!h) l]))"
  by pat_completeness auto

declare insert.domintros[simp] insert.psimps[simp]

lemma insert_termination:
  assumes "invar pvEB" "i < uv pvEB"
  shows "insert_dom (pvEB, i)"
  using assms
proof (induction pvEB arbitrary: i)
  case (Node u s cs)
  have "insert_dom (s, high i u)"
    using Node.IH(1) Node.prems high_lt_uv_summary by auto
  moreover have "insert_dom (cs!(high i u), low i u)"
    using Node.IH(2) Node.prems by (meson high_in_clusters invar.simps(2) low_lt_uv_high_clusters)
  ultimately show ?case
    by simp
qed simp

lemma insert_uv:
  assumes "invar pvEB" "i < uv pvEB"
  shows "uv (insert pvEB i) = uv pvEB"
  using assms by (cases pvEB) (auto simp: insert_termination, meson uv.simps(2))

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
    using defs Node.prems by (auto simp: insert_termination, meson list_pvEB.simps(2))
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
        | None \<Rightarrow> None
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
  show ?case
  proof (cases "\<exists>h. Some h = minimum s")
    case True
    then obtain h where h_def: "Some h = minimum s"
      by blast
    hence *: "minimum_dom s" "h < uv s"
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
      hence "(Some m = minimum (Node u s cs) \<longrightarrow> m < uv (Node u s cs))"
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

subsubsection \<open>Successor \<O>(lg u lg lg u)\<close> (* TODO *)

function (sequential) successor :: "pvEB \<Rightarrow> nat \<Rightarrow> nat option" where
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
          | None \<Rightarrow> None
        )
      | None \<Rightarrow> None
    )
  )"
  by pat_completeness auto
termination sorry (* TODO *)

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
    by (auto split: option.splits, metis nth_mem)
qed (auto split: if_splits)

lemma B:
  assumes "invar pvEB" "Some j = successor pvEB i" "i < uv pvEB"
  shows "i < j"
  sorry

lemma C:
  assumes "invar pvEB" "Some j = successor pvEB i" "i < uv pvEB"
  shows "list_pvEB pvEB ! j"
  sorry

lemma D:
  assumes "invar pvEB" "Some j = successor pvEB i" "i < uv pvEB" "i < k" "k < j"
  shows "\<not> list_pvEB pvEB ! k"
  sorry

corollary successor_is_arg_min:
  assumes "invar pvEB" "Some j = successor pvEB i" "i < uv pvEB"
  shows "is_arg_min id (\<lambda>j. list_pvEB pvEB ! j \<and> i < j \<and> (\<forall>k. i < k \<and> k < j \<longrightarrow> \<not> list_pvEB pvEB ! k)) j"
  using assms B C D unfolding is_arg_min_def by (metis id_apply)

lemma E:
  assumes "invar pvEB" "i < uv pvEB"
  shows "(None = successor pvEB i) \<longleftrightarrow> (\<forall>j < uv pvEB. i < j \<longrightarrow> \<not> list_pvEB pvEB ! j)"
  sorry

subsection \<open>Delete \<O>(sqrt u lg lg u)\<close> (* TODO *)

end
