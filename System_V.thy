(*
  Authors: Asta Halkjær From, Agnes Moesgård Eschen & Jørgen Villadsen, DTU Compute
*)

theory System_V imports Main begin

section \<open>Syntax / Semantics\<close>

datatype form = Falsity (\<open>\<bottom>\<close>) | Pro nat (\<open>\<cdot>\<close>) | Imp form form (infix \<open>\<rightarrow>\<close> 0)

primrec semantics (infix \<open>\<Turnstile>\<close> 0) where
  \<open>(I \<Turnstile> \<bottom>) = False\<close> |
  \<open>(I \<Turnstile> \<cdot> n) = I n\<close> |
  \<open>(I \<Turnstile> (p \<rightarrow> q)) = ((I \<Turnstile> p) \<longrightarrow> (I \<Turnstile> q))\<close>

abbreviation \<open>valid p \<equiv> \<forall>I. (I \<Turnstile> p)\<close>

section \<open>Axiomatic System\<close>

inductive V (\<open>\<then>\<close>) where
  MP: \<open>\<then> p\<close> if \<open>\<then> q\<close> and \<open>\<then> (q \<rightarrow> p)\<close> |
  CC: \<open>\<then> p\<close> if \<open>\<then> ((p \<rightarrow> q) \<rightarrow> p)\<close> |
  Tran: \<open>\<then> ((q \<rightarrow> r) \<rightarrow> ((r \<rightarrow> p) \<rightarrow> (q \<rightarrow> p)))\<close> |
  Simp: \<open>\<then> (p \<rightarrow> (q \<rightarrow> p))\<close> |
  Expl: \<open>\<then> (\<bottom> \<rightarrow> p)\<close>

section \<open>Soundness\<close>

theorem soundness: \<open>valid p\<close> if \<open>\<then> p\<close>
  using that by induct auto

section \<open>Derived Rules\<close>

lemma MPA: \<open>\<then> (p \<rightarrow> ((p \<rightarrow> q) \<rightarrow> q))\<close>
  by (metis Simp Tran CC MP)

lemma Swap: \<open>\<then> ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> (q \<rightarrow> (p \<rightarrow> r)))\<close>
  by (meson MPA Tran MP)

lemma Peirce: \<open>\<then> (((p \<rightarrow> q) \<rightarrow> p) \<rightarrow> p)\<close>
  by (metis Simp Swap Tran CC MP)

lemma Hilbert: \<open>\<then> ((p \<rightarrow> (p \<rightarrow> q)) \<rightarrow> (p \<rightarrow> q))\<close>
  by (meson Peirce Tran MP)

lemma Tran': \<open>\<then> ((r \<rightarrow> p) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> (q \<rightarrow> p)))\<close>
  by (meson Swap Tran MP)

lemma Frege: \<open>\<then> ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)))\<close>
  by (meson Hilbert Tran' MP Swap)

primrec imply :: \<open>form list \<Rightarrow> form \<Rightarrow> form\<close> where
  \<open>imply [] q = q\<close>
| \<open>imply (p # ps) q = (p \<rightarrow> imply ps q)\<close>

lemma imply_head: \<open>\<then> (imply (p # ps) p)\<close>
  by (induct ps) (metis Frege Simp MP imply.simps, metis Frege Simp MP imply.simps(2))

lemma imply_Cons: \<open>\<then> (imply ps q) \<Longrightarrow> \<then> (imply (p # ps) q)\<close>
  by (metis Simp MP imply.simps(2))

lemma imply_mem: \<open>p \<in> set ps \<Longrightarrow> \<then> (imply ps p)\<close>
  using imply_head imply_Cons by (induct ps) auto

lemma imply_MP: \<open>\<then> (imply ps p \<rightarrow> (imply ps (p \<rightarrow> q) \<rightarrow> imply ps q))\<close>
proof (induct ps)
  case Nil
  then show ?case
    by (metis Frege Simp MP imply.simps(1))
next
  case (Cons r ps)
  then have \<open>\<then> ((r \<rightarrow> imply ps p) \<rightarrow> (r \<rightarrow> (imply ps (p \<rightarrow> q) \<rightarrow> imply ps q)))\<close>
    by (meson Frege Simp MP)
  then have \<open>\<then> ((r \<rightarrow> imply ps p) \<rightarrow> ((r \<rightarrow> imply ps (p \<rightarrow> q)) \<rightarrow> (r \<rightarrow> imply ps q)))\<close>
    by (meson Frege Simp MP)
  then show ?case
    by simp
qed

lemma imply_mp': \<open>\<then> (imply ps p) \<Longrightarrow> \<then> (imply ps (p \<rightarrow> q)) \<Longrightarrow> \<then> (imply ps q)\<close>
  using imply_MP MP by meson

lemma add_imply: \<open>\<then> q \<Longrightarrow> \<then> (imply ps q)\<close>
  using imply_Cons by (induct ps) simp_all

lemma imply_append: \<open>imply (ps @ qs) r = imply ps (imply qs r)\<close>
  by (induct ps) simp_all

lemma imply_swap: \<open>\<then> (imply (ps @ qs) r) \<Longrightarrow> \<then> (imply (qs @ ps) r)\<close>
proof (induct qs arbitrary: ps)
  case Cons
  then show ?case
    using imply_Cons imply_head imply_mp' imply.simps(2) imply_append by metis
qed simp

lemma deduct: \<open>\<then> (imply (p # ps) q) \<longleftrightarrow> \<then> (imply ps (p \<rightarrow> q))\<close>
  using imply_append imply_swap imply.simps by metis

theorem imply_weaken: \<open>\<then> (imply ps q) \<Longrightarrow> set ps \<subseteq> set ps' \<Longrightarrow> \<then> (imply ps' q)\<close>
proof (induct ps arbitrary: q)
  case (Cons p ps)
  note \<open>\<then> (imply (p # ps) q)\<close>
  then have \<open>\<then> (imply ps (p \<rightarrow> q))\<close>
    using deduct by blast
  then have \<open>\<then> (imply ps' (p \<rightarrow> q))\<close>
    using Cons by simp
  then show ?case
    using Cons(3) imply_mem imply_mp' by (metis list.set_intros(1) subset_code(1))
qed (simp add: add_imply)

lemma cut: \<open>\<then> (imply ps p) \<Longrightarrow> \<then> (imply (p # ps) q) \<Longrightarrow> \<then> (imply ps q)\<close>
  using deduct imply_mp' by meson

lemma cut': \<open>\<then> (imply (p # ps) r) \<Longrightarrow> \<then> (imply (q # ps) p) \<Longrightarrow> \<then> (imply (q # ps) r)\<close>
  using cut deduct imply_Cons by meson

abbreviation Neg (\<open>\<sim>\<close>) where \<open>\<sim> p \<equiv> (p \<rightarrow> \<bottom>)\<close>

lemma Neg: \<open>\<then> (\<sim> (\<sim> p) \<rightarrow> p)\<close>
  by (meson Expl Peirce Tran' MP)

section \<open>Consistent\<close>

definition consistent :: \<open>form set \<Rightarrow> bool\<close> where
  \<open>consistent S \<equiv> \<nexists>S'. set S' \<subseteq> S \<and> \<then> (imply S' \<bottom>)\<close>

lemma UN_finite_bound:
  assumes \<open>finite A\<close> \<open>A \<subseteq> (\<Union>n. f n)\<close>
  shows \<open>\<exists>m :: nat. A \<subseteq> (\<Union>n \<le> m. f n)\<close>
  using assms
proof (induct rule: finite_induct)
  case (insert x A)
  then obtain m where \<open>A \<subseteq> (\<Union>n \<le> m. f n)\<close>
    by fast
  then have \<open>A \<subseteq> (\<Union>n \<le> (m + k). f n)\<close> for k
    by fastforce
  moreover obtain m' where \<open>x \<in> f m'\<close>
    using insert(4) by blast
  ultimately have \<open>{x} \<union> A \<subseteq> (\<Union>n \<le> m + m'. f n)\<close>
    by auto
  then show ?case
    by blast
qed simp

section \<open>Extension\<close>

primrec extend :: \<open>form set \<Rightarrow> (nat \<Rightarrow> form) \<Rightarrow> nat \<Rightarrow> form set\<close> where
  \<open>extend S f 0 = S\<close>
| \<open>extend S f (Suc n) =
    (if consistent ({f n} \<union> extend S f n)
     then {f n} \<union> extend S f n
     else extend S f n)\<close>

definition Extend :: \<open>form set \<Rightarrow> (nat \<Rightarrow> form) \<Rightarrow> form set\<close> where
  \<open>Extend S f \<equiv> \<Union>n. extend S f n\<close>

lemma Extend_subset: \<open>S \<subseteq> Extend S f\<close>
  unfolding Extend_def by (metis Union_upper extend.simps(1) range_eqI)

lemma extend_bound: \<open>(\<Union>n \<le> m. extend S f n) = extend S f m\<close>
  by (induct m) (simp_all add: atMost_Suc)

lemma consistent_extend: \<open>consistent S \<Longrightarrow> consistent (extend S f n)\<close>
  by (induct n) simp_all

lemma consistent_Extend:
  assumes \<open>consistent S\<close>
  shows \<open>consistent (Extend S f)\<close>
  unfolding Extend_def
proof (rule ccontr)
  assume \<open>\<not> consistent (\<Union>n. extend S f n)\<close>
  then obtain S' where \<open>\<then> (imply S' \<bottom>)\<close> \<open>set S' \<subseteq> (\<Union>n. extend S f n)\<close>
    unfolding consistent_def by blast
  then obtain m where \<open>set S' \<subseteq> (\<Union>n \<le> m. extend S f n)\<close>
    using UN_finite_bound by (metis List.finite_set)
  then have \<open>set S' \<subseteq> extend S f m\<close>
    using extend_bound by blast
  moreover have \<open>consistent (extend S f m)\<close>
    using assms consistent_extend by blast
  ultimately show False
    unfolding consistent_def using \<open>\<then> (imply S' \<bottom>)\<close> by blast
qed

section \<open>Maximal\<close>

definition maximal :: \<open>form set \<Rightarrow> bool\<close> where
  \<open>maximal S \<equiv> \<forall>p. p \<notin> S \<longrightarrow> \<not> consistent ({p} \<union> S)\<close>

lemma maximal_Extend:
  assumes \<open>surj f\<close>
  shows \<open>maximal (Extend S f)\<close>
proof (rule ccontr)
  assume \<open>\<not> maximal (Extend S f)\<close>
  then obtain p where \<open>p \<notin> Extend S f\<close> \<open>consistent ({p} \<union> Extend S f)\<close>
    unfolding maximal_def using assms consistent_Extend by blast
  obtain n where n: \<open>f n = p\<close>
    using \<open>surj f\<close> unfolding surj_def by metis
  then have \<open>p \<notin> extend S f (Suc n)\<close>
    using \<open>p \<notin> Extend S f\<close> unfolding Extend_def by blast
  then have \<open>\<not> consistent ({p} \<union> extend S f n)\<close>
    using n by fastforce
  moreover have \<open>{p} \<union> extend S f n \<subseteq> {p} \<union> Extend S f\<close>
    unfolding Extend_def by blast
  ultimately have \<open>\<not> consistent ({p} \<union> Extend S f)\<close>
    unfolding consistent_def by fastforce
  then show False
    using \<open>consistent ({p} \<union> Extend S f)\<close> by blast
qed

section \<open>Hintikka\<close>

definition hintikka :: \<open>form set \<Rightarrow> bool\<close> where
  \<open>hintikka H \<equiv>
    \<bottom> \<notin> H \<and>
    (\<forall>n. \<cdot> n \<in> H \<longrightarrow> (\<sim> (\<cdot> n)) \<notin> H) \<and>
    (\<forall>p q. (p \<rightarrow> q) \<in> H \<longrightarrow> (\<sim> p) \<in> H \<or> q \<in> H) \<and>
    (\<forall>p q. (\<sim> (p \<rightarrow> q)) \<in> H \<longrightarrow> p \<in> H \<and> \<sim> q \<in> H)\<close>

abbreviation (input) \<open>model H n \<equiv> \<cdot> n \<in> H\<close>

lemma hintikka_model:
  assumes \<open>hintikka H\<close>
  shows \<open>(p \<in> H \<longrightarrow> (model H \<Turnstile> p)) \<and> (\<sim> p \<in> H \<longrightarrow> \<not> (model H \<Turnstile> p))\<close>
  using assms by (induct p) (simp; unfold hintikka_def, blast)+

lemma inconsistent_head:
  assumes \<open>maximal S\<close> \<open>consistent S\<close> \<open>p \<notin> S\<close>
  shows \<open>\<exists>S'. \<then> (imply (p # S') \<bottom>) \<and> set S' \<subseteq> S\<close>
proof -
  obtain S' where S': \<open>\<then> (imply S' \<bottom>)\<close> \<open>set S' \<subseteq> {p} \<union> S\<close> \<open>p \<in> set S'\<close>
    using assms unfolding maximal_def consistent_def by fast
  then obtain S'' where S'': \<open>\<then> (imply (p # S'') \<bottom>)\<close> \<open>set S'' = set S' - {p}\<close>
    using imply_weaken by (metis Diff_single_insert list.set(2) set_removeAll subset_refl)
  then show ?thesis
    using S'(2) by fast
qed

lemma hintikka_Extend:
  assumes \<open>maximal S\<close> \<open>consistent S\<close>
  shows \<open>hintikka S\<close>
  unfolding hintikka_def
proof safe
  assume \<open>\<bottom> \<in> S\<close>
  then show False
    using assms(2) imply_head unfolding consistent_def
    by (metis all_not_in_conv empty_set insert_subset list.simps(15) subsetI)
next
  fix n
  assume \<open>\<cdot> n \<in> S\<close> \<open>(\<sim> (\<cdot> n)) \<in> S\<close>
  moreover have \<open>\<then> (imply [\<cdot> n, \<sim> (\<cdot> n)] \<bottom>)\<close>
    using deduct imply_head by blast
  ultimately show False
    using assms(2) unfolding consistent_def
    by (metis bot.extremum empty_set insert_subset list.set(2))
next
  fix p q
  assume *: \<open>(p \<rightarrow> q) \<in> S\<close> \<open>q \<notin> S\<close>
  then obtain Sq' where Sq': \<open>\<then> (imply (q # Sq') \<bottom>)\<close> \<open>set Sq' \<subseteq> S\<close>
    using assms inconsistent_head by blast
  show \<open>\<sim> p \<in> S\<close>
  proof (rule ccontr)
    assume \<open>\<sim> p \<notin> S\<close>
    then obtain Sp' where Sp': \<open>\<then> (imply (\<sim> p # Sp') \<bottom>)\<close> \<open>set Sp' \<subseteq> S\<close>
      using assms inconsistent_head by blast
    obtain S' where S': \<open>set S' = set Sp' \<union> set Sq'\<close>
      by (meson set_append)
    then have \<open>\<then> (imply (\<sim> p # S') \<bottom>)\<close> \<open>\<then> (imply (q # S') \<bottom>)\<close>
    proof -
      have \<open>set Sp' \<subseteq> set S'\<close>
        using S' by blast
      then show \<open>\<then> (imply (\<sim> p # S') \<bottom>)\<close>
        by (metis Sp'(1) deduct imply_weaken)
      have \<open>set Sq' \<subseteq> set S'\<close>
        using S' by blast
      then show \<open>\<then> (imply (q # S') \<bottom>)\<close>
        by (metis Sq'(1) deduct imply_weaken)
    qed
    then have \<open>\<then> (imply ((p \<rightarrow> q) # S') \<bottom>)\<close>
      using Neg add_imply cut' deduct imply_Cons imply_head imply_mp' by metis
    moreover have \<open>set ((p \<rightarrow> q) # S') \<subseteq> S\<close>
      using *(1) S' Sp'(2) Sq'(2) by auto
    ultimately show False
      using assms unfolding consistent_def by blast
  qed
next
  fix p q
  assume *: \<open>(\<sim> (p \<rightarrow> q)) \<in> S\<close>
  show \<open>p \<in> S\<close>
  proof (rule ccontr)
    assume \<open>p \<notin> S\<close>
    then obtain S' where S': \<open>\<then> (imply (p # S') \<bottom>)\<close> \<open>set S' \<subseteq> S\<close>
      using assms inconsistent_head by blast
    then have \<open>\<then> (imply ((\<sim> (p \<rightarrow> q)) # S') p)\<close>
      using Frege Simp Neg Tran MP add_imply deduct by metis
    then have \<open>\<then> (imply ((\<sim> (p \<rightarrow> q)) # S') \<bottom>)\<close>
      using cut' S'(1) by blast
    moreover have \<open>set ((\<sim> (p \<rightarrow> q)) # S') \<subseteq> S\<close>
      using *(1) S'(2) by fastforce
    ultimately show False
      using assms unfolding consistent_def by blast
  qed
next
  fix p q
  assume *: \<open>(\<sim> (p \<rightarrow> q)) \<in> S\<close>
  show \<open>\<sim> q \<in> S\<close>
  proof (rule ccontr)
    assume \<open>\<sim> q \<notin> S\<close>
    then obtain S' where S': \<open>\<then> (imply (\<sim> q # S') \<bottom>)\<close> \<open>set S' \<subseteq> S\<close>
      using assms inconsistent_head by blast
    then have \<open>\<then> (imply ((\<sim> (p \<rightarrow> q)) # S') (\<sim> q))\<close>
      using Frege Simp Neg Tran MP add_imply deduct by metis
    then have \<open>\<then> (imply ((\<sim> (p \<rightarrow> q)) # S') \<bottom>)\<close>
      using cut' S'(1) by blast
    moreover have \<open>set ((\<sim> (p \<rightarrow> q)) # S') \<subseteq> S\<close>
      using *(1) S'(2) by fastforce
    ultimately show False
      using assms unfolding consistent_def by blast
  qed
qed

section \<open>Countable Formulas\<close>

primrec diag :: \<open>nat \<Rightarrow> (nat \<times> nat)\<close> where
  \<open>diag 0 = (0, 0)\<close>
| \<open>diag (Suc n) =
     (let (x, y) = diag n
      in case y of
          0 \<Rightarrow> (0, Suc x)
        | Suc y \<Rightarrow> (Suc x, y))\<close>

theorem diag_le1: \<open>fst (diag (Suc n)) < Suc n\<close>
  by (induct n) (simp_all add: Let_def split_def split: nat.split)

theorem diag_le2: \<open>snd (diag (Suc (Suc n))) < Suc (Suc n)\<close>
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n')
  then show ?case
  proof (induct n')
    case 0
    then show ?case by simp
  next
    case (Suc _)
    then show ?case
      using diag_le1 by (simp add: Let_def split_def split: nat.split)
  qed
qed

theorem diag_le3: \<open>fst (diag n) = Suc x \<Longrightarrow> snd (diag n) < n\<close>
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n')
  then show ?case
  proof (induct n')
    case 0
    then show ?case by simp
  next
    case (Suc n'')
    then show ?case using diag_le2 by simp
  qed
qed

theorem diag_le4: \<open>fst (diag n) = Suc x \<Longrightarrow> x < n\<close>
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n')
  then have \<open>fst (diag (Suc n')) < Suc n'\<close>
    using diag_le1 by blast
  then show ?case using Suc by simp
qed

function undiag :: \<open>nat \<times> nat \<Rightarrow> nat\<close> where
  \<open>undiag (0, 0) = 0\<close>
| \<open>undiag (0, Suc y) = Suc (undiag (y, 0))\<close>
| \<open>undiag (Suc x, y) = Suc (undiag (x, Suc y))\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (\<lambda>(x, y). ((x + y) * (x + y + 1)) div 2 + x)\<close>) auto

theorem diag_undiag [simp]: \<open>diag (undiag (x, y)) = (x, y)\<close>
  by (induct rule: undiag.induct) simp_all

datatype btree = Leaf nat | Branch btree btree

function diag_btree :: \<open>nat \<Rightarrow> btree\<close> where
  \<open>diag_btree n = (case fst (diag n) of
       0 \<Rightarrow> Leaf (snd (diag n))
     | Suc x \<Rightarrow> Branch (diag_btree x) (diag_btree (snd (diag n))))\<close>
  by auto
termination
  by (relation \<open>measure id\<close>) (auto intro: diag_le3 diag_le4)

primrec undiag_btree :: \<open>btree \<Rightarrow> nat\<close> where
  \<open>undiag_btree (Leaf n) = undiag (0, n)\<close>
| \<open>undiag_btree (Branch t1 t2) = undiag (Suc (undiag_btree t1), undiag_btree t2)\<close>

theorem diag_undiag_btree [simp]: \<open>diag_btree (undiag_btree t) = t\<close>
  by (induct t) simp_all

declare diag_btree.simps [simp del] undiag_btree.simps [simp del]

fun form_of_btree :: \<open>btree \<Rightarrow> form\<close> where
  \<open>form_of_btree (Leaf 0) = Falsity\<close>
| \<open>form_of_btree (Branch (Leaf 0) (Leaf n)) = \<cdot> n\<close>
| \<open>form_of_btree (Branch (Leaf (Suc 0)) (Branch t1 t2)) =
     ((form_of_btree t1) \<rightarrow> (form_of_btree t2))\<close>
| \<open>form_of_btree (Leaf (Suc _)) = undefined\<close>
| \<open>form_of_btree (Branch (Leaf 0) (Branch _ _)) = undefined\<close>
| \<open>form_of_btree (Branch (Leaf (Suc 0)) (Leaf _)) = undefined\<close>
| \<open>form_of_btree (Branch (Leaf (Suc (Suc _))) _) = undefined\<close>
| \<open>form_of_btree (Branch (Branch _ _) _) = undefined\<close>

primrec btree_of_form :: \<open>form \<Rightarrow> btree\<close> where
  \<open>btree_of_form Falsity = Leaf 0\<close>
| \<open>btree_of_form (\<cdot> n) = Branch (Leaf 0) (Leaf n)\<close>
| \<open>btree_of_form (p \<rightarrow> q) = Branch (Leaf (Suc 0))
     (Branch (btree_of_form p) (btree_of_form q))\<close>

definition diag_form :: \<open>nat \<Rightarrow> form\<close> where
  \<open>diag_form n = form_of_btree (diag_btree n)\<close>

definition undiag_form :: \<open>form \<Rightarrow> nat\<close> where
  \<open>undiag_form p = undiag_btree (btree_of_form p)\<close>

theorem diag_undiag_form [simp]: \<open>diag_form (undiag_form p) = p\<close>
  unfolding diag_form_def undiag_form_def by (induct p) simp_all

abbreviation \<open>from_nat \<equiv> diag_form\<close>
abbreviation \<open>to_nat \<equiv> undiag_form\<close>

lemma surj_from_nat: \<open>surj from_nat\<close>
  by (metis diag_undiag_form surj_def)

section \<open>Completeness\<close>

lemma imply_completeness:
  assumes valid: \<open>\<forall>I. list_all (\<lambda>q. (I \<Turnstile> q)) ps \<longrightarrow> (I \<Turnstile> p)\<close>
  shows \<open>\<then> (imply ps p)\<close>
proof (rule ccontr)
  assume \<open>\<not> \<then> (imply ps p)\<close>
  then have *: \<open>\<not> \<then> (imply (\<sim> p # ps) \<bottom>)\<close>
    using Neg add_imply deduct imply_mp' by metis
  let ?S = \<open>set (\<sim> p # ps)\<close>
  let ?H = \<open>Extend ?S from_nat\<close>
  have \<open>consistent ?S\<close>
    unfolding consistent_def using * imply_weaken by blast
  then have \<open>consistent ?H\<close> \<open>maximal ?H\<close>
    using consistent_Extend maximal_Extend surj_from_nat by blast+
  then have \<open>hintikka ?H\<close>
    using hintikka_Extend by blast
  then have \<open>model ?H \<Turnstile> p\<close> if \<open>p \<in> ?S\<close> for p
    using that Extend_subset hintikka_model by blast
  then have \<open>model ?H \<Turnstile> \<sim> p\<close> \<open>list_all (\<lambda>p. (model ?H \<Turnstile> p)) ps\<close>
    unfolding list_all_def by fastforce+
  then have \<open>model ?H \<Turnstile> p\<close>
    using valid by blast
  then show False
    using \<open>model ?H \<Turnstile> \<sim> p\<close> by simp
qed

theorem completeness: \<open>\<then> p\<close> if \<open>valid p\<close>
  using that imply_completeness[where ps=\<open>[]\<close>] by simp

section \<open>Main Result\<close>

theorem main: \<open>valid p \<longleftrightarrow> \<then> p\<close>
proof
  assume \<open>valid p\<close>
  with completeness show \<open>\<then> p\<close> .
next
  assume \<open>\<then> p\<close>
  with soundness show \<open>valid p\<close> .
qed

section \<open>Appendix Isabelle Workshop\<close>

inductive U (\<open>\<turnstile>\<close>) where
  \<open>\<turnstile> p\<close> if \<open>\<turnstile> q\<close> and \<open>\<turnstile> (q \<rightarrow> p)\<close> |
  \<open>\<turnstile> ((q \<rightarrow> r) \<rightarrow> ((r \<rightarrow> (r \<rightarrow> p)) \<rightarrow> (q \<rightarrow> p)))\<close> |
  \<open>\<turnstile> (p \<rightarrow> (q \<rightarrow> p))\<close> |
  \<open>\<turnstile> (\<sim> (\<sim> p) \<rightarrow> p)\<close>

inductive W (\<open>\<tturnstile>\<close>) where
  \<open>\<tturnstile> p\<close> if \<open>\<tturnstile> q\<close> and \<open>\<tturnstile> (q \<rightarrow> p)\<close> |
  \<open>\<tturnstile> ((r \<rightarrow> q) \<rightarrow> ((r \<rightarrow> (q \<rightarrow> p)) \<rightarrow> (r \<rightarrow> p)))\<close> |
  \<open>\<tturnstile> (p \<rightarrow> (r \<rightarrow> p))\<close> |
  \<open>\<tturnstile> (\<sim> (\<sim> p) \<rightarrow> p)\<close>

theorem
  \<open>valid p \<longleftrightarrow> \<turnstile> p\<close>
  \<open>valid p \<longleftrightarrow> \<tturnstile> p\<close>
proof -
  have H: \<open>\<turnstile> ((r \<rightarrow> (r \<rightarrow> p)) \<rightarrow> (r \<rightarrow> p))\<close> for p r
    by (metis U.intros(1-3))
  have T: \<open>\<turnstile> ((r \<rightarrow> q) \<rightarrow> ((q \<rightarrow> p) \<rightarrow> (r \<rightarrow> p)))\<close> for p q r
    by (meson U.intros(1-3))
  have S: \<open>\<turnstile> ((r \<rightarrow> (q \<rightarrow> p)) \<rightarrow> (q \<rightarrow> (r \<rightarrow> p)))\<close> for p q r
    by (meson U.intros(1-3) T)
  have T': \<open>\<turnstile> ((q \<rightarrow> p) \<rightarrow> ((r \<rightarrow> q) \<rightarrow> (r \<rightarrow> p)))\<close> for p q r
    by (meson U.intros(1) S T)
  have F: \<open>\<turnstile> ((r \<rightarrow> (q \<rightarrow> p)) \<rightarrow> ((r \<rightarrow> q) \<rightarrow> (r \<rightarrow> p)))\<close> for p q r
    by (meson T' U.intros(1) S H)
  have F': \<open>\<turnstile> ((r \<rightarrow> q) \<rightarrow> ((r \<rightarrow> (q \<rightarrow> p)) \<rightarrow> (r \<rightarrow> p)))\<close> for p q r
    by (meson U.intros(1) S F)
  have \<open>\<tturnstile> ((r \<rightarrow> (q \<rightarrow> p)) \<rightarrow> ((r \<rightarrow> q) \<rightarrow> (r \<rightarrow> p)))\<close> for p q r
    by (use W.intros(1-3) in metis)
  with W.intros(1,3) have *: \<open>\<tturnstile> ((r \<rightarrow> q) \<rightarrow> ((q \<rightarrow> p) \<rightarrow> (r \<rightarrow> p)))\<close> for p q r
    by metis
  note main
  moreover have \<open>\<tturnstile> p\<close> if \<open>\<then> p\<close>
    using that by induct (use * W.intros in metis)+
  moreover have \<open>\<then> p\<close> if \<open>\<tturnstile> p\<close>
    using that by induct (use MP Frege Simp Neg Swap in metis)+
  ultimately show \<open>valid p \<longleftrightarrow> \<tturnstile> p\<close>
    by fast
  note this
  moreover have \<open>\<turnstile> p\<close> if \<open>\<tturnstile> p\<close>
    using that by induct (use F' U.intros(1,3,4) in metis)+
  moreover have \<open>\<tturnstile> p\<close> if \<open>\<turnstile> p\<close>
    using that by induct (use * W.intros in metis)+
  ultimately show \<open>valid p \<longleftrightarrow> \<turnstile> p\<close>
    by fast
qed

end
