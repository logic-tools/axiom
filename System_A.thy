(* Author: Asta Halkjær From, DTU Compute *)

theory System_A imports "HOL-Library.Countable" begin

section \<open>Syntax\<close>

datatype form
  = Falsity (\<open>\<^bold>\<bottom>\<close>)
  | Pro nat
  | Imp form form (infixr \<open>\<^bold>\<longrightarrow>\<close> 25)
  | Dis form form (infixr \<open>\<^bold>\<or>\<close> 30)
  | Con form form (infixr \<open>\<^bold>\<and>\<close> 35)

abbreviation Truth (\<open>\<^bold>\<top>\<close>) where \<open>\<^bold>\<top> \<equiv> \<^bold>\<bottom> \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>

abbreviation Neg (\<open>\<^bold>\<not> _\<close> [40] 40) where \<open>\<^bold>\<not> p \<equiv> p \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>

section \<open>Semantics\<close>

primrec semantics :: \<open>(nat \<Rightarrow> bool) \<Rightarrow> form \<Rightarrow> bool\<close> (\<open>_ \<Turnstile> _\<close> [50, 50] 50) where
  \<open>(I \<Turnstile> \<^bold>\<bottom>) = False\<close>
| \<open>(I \<Turnstile> Pro n) = I n\<close>
| \<open>(I \<Turnstile> (p \<^bold>\<longrightarrow> q)) = ((I \<Turnstile> p) \<longrightarrow> (I \<Turnstile> q))\<close>
| \<open>(I \<Turnstile> (p \<^bold>\<or> q)) = ((I \<Turnstile> p) \<or> (I \<Turnstile> q))\<close>
| \<open>(I \<Turnstile> (p \<^bold>\<and> q)) = ((I \<Turnstile> p) \<and> (I \<Turnstile> q))\<close>

section \<open>Axiomatics\<close>

inductive Axiomatics :: \<open>form \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [50] 50) where
  MP: \<open>\<turnstile> p \<Longrightarrow> \<turnstile> (p \<^bold>\<longrightarrow> q) \<Longrightarrow> \<turnstile> q\<close>
| Imp1: \<open>\<turnstile> (p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> p)\<close>
| Imp2: \<open>\<turnstile> ((p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> r)\<close>
| DisE: \<open>\<turnstile> ((p \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> (q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> p \<^bold>\<or> q \<^bold>\<longrightarrow> r)\<close>
| DisI1: \<open>\<turnstile> (p \<^bold>\<longrightarrow> p \<^bold>\<or> q)\<close>
| DisI2: \<open>\<turnstile> (q \<^bold>\<longrightarrow> p \<^bold>\<or> q)\<close>
| ConE1: \<open>\<turnstile> (p \<^bold>\<and> q \<^bold>\<longrightarrow> p)\<close>
| ConE2: \<open>\<turnstile> (p \<^bold>\<and> q \<^bold>\<longrightarrow> q)\<close>
| ConI: \<open>\<turnstile> (p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> p \<^bold>\<and> q)\<close>
| Neg: \<open>\<turnstile> (((p \<^bold>\<longrightarrow> \<^bold>\<bottom>) \<^bold>\<longrightarrow> \<^bold>\<bottom>) \<^bold>\<longrightarrow> p)\<close>

section \<open>Soundness\<close>

theorem soundness: \<open>\<turnstile> p \<Longrightarrow> I \<Turnstile> p\<close>
  by (induct rule: Axiomatics.induct) simp_all

section \<open>Derived Rules\<close>

lemma Imp3: \<open>\<turnstile> (p \<^bold>\<longrightarrow> p)\<close>
  by (metis Imp1 Imp2 MP)

lemma Imp4: \<open>\<turnstile> ((p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> (q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> r)\<close>
  by (metis Imp1 Imp2 MP)

lemma Imp2': \<open>\<turnstile> ((p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> (p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> r)\<close>
  by (metis Imp1 Imp2 Imp3 Imp4 MP)

lemma Imp2'': \<open>\<turnstile> ((p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> r)\<close>
  by (metis Imp1 Imp2' MP)

lemma FalsityE: \<open>\<turnstile> (p \<^bold>\<longrightarrow> \<^bold>\<not> p \<^bold>\<longrightarrow> q)\<close>
proof -
  obtain r where \<open>\<turnstile> ((r \<^bold>\<longrightarrow> p) \<^bold>\<longrightarrow> \<^bold>\<not> p \<^bold>\<longrightarrow> q)\<close>
    by (metis Imp1 Imp2 MP Neg)
  then show ?thesis
    by (metis Imp1 Imp2 MP)
qed

lemma ImpE1: \<open>\<turnstile> (\<^bold>\<not> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> p)\<close>
  by (metis FalsityE Imp4 MP Neg)

lemma ImpE2: \<open>\<turnstile> (\<^bold>\<not> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> \<^bold>\<not> q)\<close>
  by (metis Imp1 Imp4 MP)

primrec imply :: \<open>form list \<Rightarrow> form \<Rightarrow> form\<close> where
  \<open>imply [] q = q\<close>
| \<open>imply (p # ps) q = (p \<^bold>\<longrightarrow> imply ps q)\<close>

lemma imply_head: \<open>\<turnstile> imply (p # ps) p\<close>
  by (induct ps) (simp add: Imp3, metis Imp1 Imp2 MP imply.simps(2))

lemma imply_Cons: \<open>\<turnstile> imply ps q \<Longrightarrow> \<turnstile> imply (p # ps) q\<close>
  by (metis Imp1 MP imply.simps(2))

lemma imply_mem: \<open>p \<in> set ps \<Longrightarrow> \<turnstile> imply ps p\<close>
  using imply_head imply_Cons by (induct ps) auto

lemma imply_MP: \<open>\<turnstile> (imply ps p \<^bold>\<longrightarrow> imply ps (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> imply ps q)\<close>
proof (induct ps)
  case Nil
  then show ?case
    by (metis Imp1 Imp2 MP imply.simps(1))
next
  case (Cons r ps)
  then show ?case
  proof -
    have \<open>\<turnstile> ((r \<^bold>\<longrightarrow> imply ps p) \<^bold>\<longrightarrow> r \<^bold>\<longrightarrow> imply ps (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> imply ps q)\<close>
      by (meson Cons.hyps Imp1 Imp2 MP)
    then have \<open>\<turnstile> ((r \<^bold>\<longrightarrow> imply ps p) \<^bold>\<longrightarrow> (r \<^bold>\<longrightarrow> imply ps (p \<^bold>\<longrightarrow> q)) \<^bold>\<longrightarrow> r \<^bold>\<longrightarrow> imply ps q)\<close>
      by (meson Imp2' Imp2'' Imp4 MP)
    then show ?thesis
      by simp
  qed
qed

lemma imply_mp': \<open>\<turnstile> imply ps p \<Longrightarrow> \<turnstile> imply ps (p \<^bold>\<longrightarrow> q) \<Longrightarrow> \<turnstile> imply ps q\<close>
  using imply_MP by (meson MP)

lemma add_imply: \<open>\<turnstile> q \<Longrightarrow> \<turnstile> imply ps q\<close>
  using imply_Cons by (induct ps) simp_all

lemma imply_append: \<open>imply (ps @ qs) r = imply ps (imply qs r)\<close>
  by (induct ps) simp_all

lemma imply_swap: \<open>\<turnstile> imply (ps @ qs) r \<Longrightarrow> \<turnstile> imply (qs @ ps) r\<close>
proof (induct qs arbitrary: ps)
  case (Cons q qs)
  then show ?case
    by (metis imply_Cons imply_head imply_mp' imply.simps(2) imply_append)
qed simp

lemma deduct: \<open>\<turnstile> imply (p # ps) q \<longleftrightarrow> \<turnstile> imply ps (p \<^bold>\<longrightarrow> q)\<close>
  using imply_swap by (metis imply.simps(1-2) imply_append)

theorem imply_weaken: \<open>\<turnstile> imply ps q \<Longrightarrow> set ps \<subseteq> set ps' \<Longrightarrow> \<turnstile> imply ps' q\<close>
proof (induct ps arbitrary: q)
  case (Cons p ps)
  note \<open>\<turnstile> imply (p # ps) q\<close>
  then have \<open>\<turnstile> imply ps (p \<^bold>\<longrightarrow> q)\<close>
    using deduct by blast
  then have \<open>\<turnstile> imply ps' (p \<^bold>\<longrightarrow> q)\<close>
    using Cons by simp
  then show ?case
    using Cons(3) by (meson imply_mem imply_mp' list.set_intros(1) subset_code(1))
qed (simp add: add_imply)

lemma cut: \<open>\<turnstile> imply ps p \<Longrightarrow> \<turnstile> imply (p # ps) q \<Longrightarrow> \<turnstile> imply ps q\<close>
  using deduct imply_mp' by blast

lemma imply4: \<open>\<turnstile> imply (p # q # ps) r \<Longrightarrow> \<turnstile> imply (q # p # ps) r\<close>
  by (metis Imp1 Imp2 MP imply.simps(2))

lemma cut': \<open>\<turnstile> imply (p # ps) r \<Longrightarrow> \<turnstile> imply (q # ps) p \<Longrightarrow> \<turnstile> imply (q # ps) r\<close>
  using imply_Cons cut imply4 by blast

lemma imply_lift: \<open>\<turnstile> (p \<^bold>\<longrightarrow> q) \<Longrightarrow> \<turnstile> (imply ps p \<^bold>\<longrightarrow> imply ps q)\<close>
proof (induct ps)
  case (Cons r ps)
  then show ?case
    by (metis Axiomatics.simps imply.simps(2))
qed simp

lemma Neg': \<open>\<turnstile> (imply ps (\<^bold>\<not> \<^bold>\<not> p) \<^bold>\<longrightarrow> imply ps p)\<close>
  using Neg imply_lift by simp

lemma Boole: \<open>\<turnstile> imply ((\<^bold>\<not> p) # ps) \<^bold>\<bottom> \<Longrightarrow> \<turnstile> imply ps p\<close>
  using deduct MP Neg' by blast

lemma imply_front: \<open>\<turnstile> imply S p \<Longrightarrow> set S - {q} \<subseteq> set S' \<Longrightarrow> \<turnstile> imply (q # S') p\<close>
  by (metis Diff_single_insert imply_weaken list.set(2))

section \<open>Consistent\<close>

definition consistent :: \<open>form set \<Rightarrow> bool\<close> where
  \<open>consistent S \<equiv> \<nexists>S'. set S' \<subseteq> S \<and> \<turnstile> imply S' \<^bold>\<bottom>\<close>

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
  then obtain S' where \<open>\<turnstile> imply S' \<^bold>\<bottom>\<close> \<open>set S' \<subseteq> (\<Union>n. extend S f n)\<close>
    unfolding consistent_def by blast
  then obtain m where \<open>set S' \<subseteq> (\<Union>n \<le> m. extend S f n)\<close>
    using UN_finite_bound by (metis List.finite_set)
  then have \<open>set S' \<subseteq> extend S f m\<close>
    using extend_bound by blast
  moreover have \<open>consistent (extend S f m)\<close>
    using assms consistent_extend by blast
  ultimately show False
    unfolding consistent_def using \<open>\<turnstile> imply S' \<^bold>\<bottom>\<close> by blast
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
  obtain k where n: \<open>f k = p\<close>
    using \<open>surj f\<close> unfolding surj_def by metis
  then have \<open>p \<notin> extend S f (Suc k)\<close>
    using \<open>p \<notin> Extend S f\<close> unfolding Extend_def by blast
  then have \<open>\<not> consistent ({p} \<union> extend S f k)\<close>
    using n by fastforce
  moreover have \<open>{p} \<union> extend S f k \<subseteq> {p} \<union> Extend S f\<close>
    unfolding Extend_def by blast
  ultimately have \<open>\<not> consistent ({p} \<union> Extend S f)\<close>
    unfolding consistent_def by fastforce
  then show False
    using \<open>consistent ({p} \<union> Extend S f)\<close> by blast
qed

section \<open>Hintikka\<close>

locale Hintikka =
  fixes H :: \<open>form set\<close>
  assumes
    NoFalsity: \<open>\<^bold>\<bottom> \<notin> H\<close> and
    Pro: \<open>Pro n \<in> H \<Longrightarrow> (\<^bold>\<not> Pro n) \<notin> H\<close> and
    ImpP: \<open>(p \<^bold>\<longrightarrow> q) \<in> H \<Longrightarrow> (\<^bold>\<not> p) \<in> H \<or> q \<in> H\<close> and
    ImpN: \<open>(\<^bold>\<not> (p \<^bold>\<longrightarrow> q)) \<in> H \<Longrightarrow> p \<in> H \<and> (\<^bold>\<not> q) \<in> H\<close> and
    DisP: \<open>(p \<^bold>\<or> q) \<in> H \<Longrightarrow> p \<in> H \<or> q \<in> H\<close> and
    DisN: \<open>(\<^bold>\<not> (p \<^bold>\<or> q)) \<in> H \<Longrightarrow> (\<^bold>\<not> p) \<in> H \<and> (\<^bold>\<not> q) \<in> H\<close> and
    ConP: \<open>(p \<^bold>\<and> q) \<in> H \<Longrightarrow> p \<in> H \<and> q \<in> H\<close> and
    ConN: \<open>(\<^bold>\<not> (p \<^bold>\<and> q)) \<in> H \<Longrightarrow> (\<^bold>\<not> p) \<in> H \<or> (\<^bold>\<not> q) \<in> H\<close>

abbreviation (input) \<open>model H n \<equiv> Pro n \<in> H\<close>

lemma Hintikka_model:
  \<open>Hintikka H \<Longrightarrow> (p \<in> H \<longrightarrow> model H \<Turnstile> p) \<and> ((\<^bold>\<not> p) \<in> H \<longrightarrow> \<not> model H \<Turnstile> p)\<close>
  by (induct p) (simp; unfold Hintikka_def, blast)+

lemma inconsistent_head:
  assumes \<open>maximal S\<close> \<open>consistent S\<close> \<open>p \<notin> S\<close>
  shows \<open>\<exists>S'. \<turnstile> imply (p # S') \<^bold>\<bottom> \<and> set S' \<subseteq> S\<close>
proof -
  obtain S' where S': \<open>\<turnstile> imply S' \<^bold>\<bottom>\<close> \<open>set S' \<subseteq> {p} \<union> S\<close> \<open>p \<in> set S'\<close>
    using assms unfolding maximal_def consistent_def by fast
  then obtain S'' where S'': \<open>\<turnstile> imply (p # S'') \<^bold>\<bottom>\<close> \<open>set S'' = set S' - {p}\<close>
    by (metis imply_front set_removeAll subset_refl)
  then show ?thesis
    using S'(2) by fast
qed

lemma Hintikka_Extend:
  assumes \<open>maximal S\<close> \<open>consistent S\<close>
  shows \<open>Hintikka S\<close>
proof
  show \<open>\<^bold>\<bottom> \<notin> S\<close>
    using assms(2) imply_head imply_mem unfolding consistent_def
    by (metis List.set_insert empty_set insert_Diff insert_is_Un singletonI sup.cobounded1)
next
  fix n
  assume \<open>Pro n \<in> S\<close>
  moreover have \<open>\<turnstile> imply [Pro n, \<^bold>\<not> Pro n] \<^bold>\<bottom>\<close>
    by (simp add: FalsityE)
  ultimately show \<open>(\<^bold>\<not> Pro n) \<notin> S\<close>
    using assms(2) unfolding consistent_def
    by (metis bot.extremum empty_set insert_subset list.set(2))
next
  fix p q
  assume *: \<open>(p \<^bold>\<longrightarrow> q) \<in> S\<close>
  show \<open>(\<^bold>\<not> p) \<in> S \<or> q \<in> S\<close>
  proof (rule disjCI, rule ccontr)
    assume **: \<open>q \<notin> S\<close>
    then obtain Sq' where Sq': \<open>\<turnstile> imply (q # Sq') \<^bold>\<bottom>\<close> \<open>set Sq' \<subseteq> S\<close>
      using assms inconsistent_head by blast

    assume \<open>(\<^bold>\<not> p) \<notin> S\<close>
    then obtain Sp' where Sp': \<open>\<turnstile> imply ((\<^bold>\<not> p) # Sp') \<^bold>\<bottom>\<close> \<open>set Sp' \<subseteq> S\<close>
      using assms inconsistent_head by blast

    obtain S' where S': \<open>set S' = set Sp' \<union> set Sq'\<close>
      by (meson set_append)
    then have \<open>\<turnstile> imply ((\<^bold>\<not> p) # S') \<^bold>\<bottom>\<close> \<open>\<turnstile> imply (q # S') \<^bold>\<bottom>\<close>
    proof -
      have \<open>set Sp' \<subseteq> set S'\<close>
        using S' by blast
      then show \<open>\<turnstile> imply ((\<^bold>\<not> p) # S') \<^bold>\<bottom>\<close>
        by (metis Sp'(1) deduct imply_weaken)
      have \<open>set Sq' \<subseteq> set S'\<close>
        using S' by blast
      then show \<open>\<turnstile> imply (q # S') \<^bold>\<bottom>\<close>
        using ** by (metis Sq'(1) deduct imply_weaken)
    qed
    then have \<open>\<turnstile> imply ((p \<^bold>\<longrightarrow> q) # S') \<^bold>\<bottom>\<close>
      using Boole imply_Cons imply_head imply_mp' cut' by metis
    moreover have \<open>set ((p \<^bold>\<longrightarrow> q) # S') \<subseteq> S\<close> if \<open>q \<notin> S\<close>
      using that *(1) S' Sp'(2) Sq'(2) by auto
    ultimately show False
      using ** assms unfolding consistent_def by blast
  qed
next
  fix p q
  assume *: \<open>(\<^bold>\<not> (p \<^bold>\<longrightarrow> q)) \<in> S\<close>
  show \<open>p \<in> S \<and> (\<^bold>\<not> q) \<in> S\<close>
  proof (rule conjI; rule ccontr)
    assume \<open>p \<notin> S\<close>
    then obtain S' where S': \<open>\<turnstile> imply (p # S') \<^bold>\<bottom>\<close> \<open>set S' \<subseteq> S\<close>
      using assms inconsistent_head by blast
    moreover have \<open>\<turnstile> imply ((\<^bold>\<not> (p \<^bold>\<longrightarrow> q)) # S') p\<close>
      using add_imply ImpE1 deduct by blast
    ultimately have \<open>\<turnstile> imply ((\<^bold>\<not> (p \<^bold>\<longrightarrow> q)) # S') \<^bold>\<bottom>\<close>
      using cut' by blast
    moreover have \<open>set ((\<^bold>\<not> (p \<^bold>\<longrightarrow> q)) # S') \<subseteq> S\<close>
      using *(1) S'(2) by fastforce
    ultimately show False
      using assms unfolding consistent_def by blast
  next
    assume \<open>(\<^bold>\<not> q) \<notin> S\<close>
    then obtain S' where S': \<open>\<turnstile> imply ((\<^bold>\<not> q) # S') \<^bold>\<bottom>\<close> \<open>set S' \<subseteq> S\<close>
      using assms inconsistent_head by blast
    moreover have \<open>\<turnstile> imply ((\<^bold>\<not> (p \<^bold>\<longrightarrow> q)) # S') (\<^bold>\<not> q)\<close>
      using add_imply ImpE2 deduct by blast
    ultimately have \<open>\<turnstile> imply ((\<^bold>\<not> (p \<^bold>\<longrightarrow> q)) # S') \<^bold>\<bottom>\<close>
      using cut' by blast
    moreover have \<open>set ((\<^bold>\<not> (p \<^bold>\<longrightarrow> q)) # S') \<subseteq> S\<close>
      using *(1) S'(2) by fastforce
    ultimately show False
      using assms unfolding consistent_def by blast
  qed
next
  fix p q
  assume *: \<open>(p \<^bold>\<or> q) \<in> S\<close>
  show \<open>p \<in> S \<or> q \<in> S\<close>
  proof (rule disjCI, rule ccontr)
    assume \<open>q \<notin> S\<close>
    then obtain Sq' where Sq': \<open>\<turnstile> imply (q # Sq') \<^bold>\<bottom>\<close> \<open>set Sq' \<subseteq> S - {q}\<close>
      using assms inconsistent_head by blast

    assume \<open>p \<notin> S\<close>
    then obtain Sp' where Sp': \<open>\<turnstile> imply (p # Sp') \<^bold>\<bottom>\<close> \<open>set Sp' \<subseteq> S - {p}\<close>
      using assms inconsistent_head by blast
    obtain S' where S': \<open>set S' = set Sp' \<union> set Sq'\<close>
      by (meson set_append)
    then have \<open>\<turnstile> imply (p # S') \<^bold>\<bottom>\<close> \<open>\<turnstile> imply (q # S') \<^bold>\<bottom>\<close>
    proof -
      have \<open>set Sp' \<subseteq> set S'\<close>
        using S' by blast
      then show \<open>\<turnstile> imply (p # S') \<^bold>\<bottom>\<close>
        by (metis Sp'(1) deduct imply_weaken)
      have \<open>set Sq' \<subseteq> set S'\<close>
        using S' by blast
      then show \<open>\<turnstile> imply (q # S') \<^bold>\<bottom>\<close>
        by (metis Sq'(1) deduct imply_weaken)
    qed
    then have \<open>\<turnstile> imply ((p \<^bold>\<or> q) # S') \<^bold>\<bottom>\<close>
      by (metis Axiomatics.simps imply.simps(2))
    moreover have \<open>set ((p \<^bold>\<or> q) # S') \<subseteq> S\<close>
      using * S' Sp'(2) Sq'(2) by auto
    ultimately show False
      using assms unfolding consistent_def by blast
  qed
next
  fix p q
  assume *: \<open>(\<^bold>\<not> (p \<^bold>\<or> q)) \<in> S\<close>
  show \<open>(\<^bold>\<not> p) \<in> S \<and> (\<^bold>\<not> q) \<in> S\<close>
  proof (rule conjI; rule ccontr)
    assume \<open>(\<^bold>\<not> p) \<notin> S\<close>
    then obtain S' where S': \<open>\<turnstile> imply ((\<^bold>\<not> p) # S') \<^bold>\<bottom>\<close> \<open>set S' \<subseteq> S - {\<^bold>\<not> p}\<close>
      using assms inconsistent_head by blast
    moreover have \<open>\<turnstile> imply ((\<^bold>\<not> (p \<^bold>\<or> q)) # S') (\<^bold>\<not> p)\<close>
      using DisI1 Imp4 add_imply deduct MP by blast
    ultimately have \<open>\<turnstile> imply ((\<^bold>\<not> (p \<^bold>\<or> q)) # S') \<^bold>\<bottom>\<close>
      using cut' by blast
    moreover have \<open>set ((\<^bold>\<not> (p \<^bold>\<or> q)) # S') \<subseteq> S\<close>
      using * S'(2) by auto
    ultimately show False
      using assms unfolding consistent_def by blast
  next
    assume \<open>(\<^bold>\<not> q) \<notin> S\<close>
    then obtain S' where S': \<open>\<turnstile> imply ((\<^bold>\<not> q) # S') \<^bold>\<bottom>\<close> \<open>set S' \<subseteq> S - {\<^bold>\<not> q}\<close>
      using assms inconsistent_head by blast
    moreover have \<open>\<turnstile> imply ((\<^bold>\<not> (p \<^bold>\<or> q)) # S') (\<^bold>\<not> q)\<close>
      using DisI2 Imp4 add_imply deduct MP by blast
    ultimately have \<open>\<turnstile> imply ((\<^bold>\<not> (p \<^bold>\<or> q)) # S') \<^bold>\<bottom>\<close>
      using cut' by blast
    moreover have \<open>set ((\<^bold>\<not> (p \<^bold>\<or> q)) # S') \<subseteq> S\<close>
      using *(1) S'(2) by auto
    ultimately show False
      using assms unfolding consistent_def by blast
  qed
next
  fix p q
  assume *: \<open>(p \<^bold>\<and> q) \<in> S\<close>
  show \<open>p \<in> S \<and> q \<in> S\<close>
  proof (rule conjI; rule ccontr)
    assume \<open>p \<notin> S\<close>
    then obtain S' where S': \<open>\<turnstile> imply (p # S') \<^bold>\<bottom>\<close> \<open>set S' \<subseteq> S - {p}\<close>
      using assms inconsistent_head by blast
    moreover have \<open>\<turnstile> imply ((p \<^bold>\<and> q) # S') p\<close>
      using ConE1 add_imply deduct by blast
    ultimately have \<open>\<turnstile> imply ((p \<^bold>\<and> q) # S') \<^bold>\<bottom>\<close>
      using cut' by blast
    moreover have \<open>set ((p \<^bold>\<and> q) # S') \<subseteq> S\<close>
      using *(1) S'(2) by auto
    ultimately show False
      using assms unfolding consistent_def by blast
  next
    assume \<open>q \<notin> S\<close>
    then obtain S' where S': \<open>\<turnstile> imply (q # S') \<^bold>\<bottom>\<close> \<open>set S' \<subseteq> S - {q}\<close>
      using assms inconsistent_head by blast
    moreover have \<open>\<turnstile> imply ((p \<^bold>\<and> q) # S') q\<close>
      using ConE2 add_imply deduct by blast
    ultimately have \<open>\<turnstile> imply ((p \<^bold>\<and> q) # S') \<^bold>\<bottom>\<close>
      using cut' by blast
    moreover have \<open>set ((p \<^bold>\<and> q) # S') \<subseteq> S\<close>
      using *(1) S'(2) S'(2) by auto
    ultimately show False
      using assms unfolding consistent_def by blast
  qed
next
  fix p q
  assume *: \<open>(\<^bold>\<not> (p \<^bold>\<and> q)) \<in> S\<close>
  show \<open>(\<^bold>\<not> p) \<in> S \<or> (\<^bold>\<not> q) \<in> S\<close>
  proof (rule disjCI, rule ccontr)
    assume \<open>(\<^bold>\<not> q) \<notin> S\<close>
    then obtain Sq' where Sq': \<open>\<turnstile> imply ((\<^bold>\<not> q) # Sq') \<^bold>\<bottom>\<close> \<open>set Sq' \<subseteq> S - {\<^bold>\<not> q}\<close>
      using assms inconsistent_head by blast

    assume \<open>(\<^bold>\<not> p) \<notin> S\<close>
    then obtain Sp' where Sp': \<open>\<turnstile> imply ((\<^bold>\<not> p) # Sp') \<^bold>\<bottom>\<close> \<open>set Sp' \<subseteq> S - {\<^bold>\<not> p}\<close>
      using assms inconsistent_head by blast

    obtain S' where S': \<open>set S' = set Sp' \<union> set Sq'\<close>
      by (meson set_append)
    then have \<open>\<turnstile> imply ((\<^bold>\<not> p) # S') \<^bold>\<bottom>\<close> \<open>\<turnstile> imply ((\<^bold>\<not> q) # S') \<^bold>\<bottom>\<close>
    proof -
      have \<open>set Sp' \<subseteq> set S'\<close>
        using S' by blast
      then show \<open>\<turnstile> imply ((\<^bold>\<not> p) # S') \<^bold>\<bottom>\<close>
        by (metis Sp'(1) deduct imply_weaken)
      have \<open>set Sq' \<subseteq> set S'\<close>
        using S' by blast
      then show \<open>\<turnstile> imply ((\<^bold>\<not> q) # S') \<^bold>\<bottom>\<close>
        by (metis Sq'(1) deduct imply_weaken)
    qed
    then have \<open>\<turnstile> imply ((\<^bold>\<not> (p \<^bold>\<and> q)) # S') \<^bold>\<bottom>\<close>
      by (metis ConI Boole add_imply imply_Cons imply_head imply_mp')
    moreover have \<open>set ((\<^bold>\<not> (p \<^bold>\<and> q)) # S') \<subseteq> S\<close>
      using *(1) S' Sp'(2) Sq'(2) by auto
    ultimately show False
      using assms unfolding consistent_def by blast
  qed
qed

section \<open>Countable Formulas\<close>

instance form :: countable by countable_datatype

section \<open>Completeness\<close>

lemma imply_completeness:
  assumes valid: \<open>\<forall>I s. list_all (\<lambda>q. I \<Turnstile> q) ps \<longrightarrow> I \<Turnstile> p\<close>
  shows \<open>\<turnstile> imply ps p\<close>
proof (rule ccontr)
  assume \<open>\<not> \<turnstile> imply ps p\<close>
  then have *: \<open>\<not> \<turnstile> imply ((\<^bold>\<not> p) # ps) \<^bold>\<bottom>\<close>
    using Boole by blast

  let ?S = \<open>set ((\<^bold>\<not> p) # ps)\<close>
  let ?H = \<open>Extend ?S from_nat\<close>

  have \<open>consistent ?S\<close>
    unfolding consistent_def using * imply_weaken by blast
  then have \<open>consistent ?H\<close> \<open>maximal ?H\<close>
    using consistent_Extend maximal_Extend surj_from_nat by blast+
  then have \<open>Hintikka ?H\<close>
    using Hintikka_Extend by blast

  have \<open>model ?H \<Turnstile> p\<close> if \<open>p \<in> ?S\<close> for p
    using that Extend_subset Hintikka_model \<open>Hintikka ?H\<close> by blast
  then have \<open>model ?H \<Turnstile> (\<^bold>\<not> p)\<close> \<open>list_all (\<lambda>p. model ?H \<Turnstile> p) ps\<close>
    unfolding list_all_def by fastforce+
  then have \<open>model ?H \<Turnstile> p\<close>
    using valid by blast
  then show False
    using \<open>model ?H \<Turnstile> (\<^bold>\<not> p)\<close> by simp
qed

theorem completeness: \<open>\<forall>I. I \<Turnstile> p \<Longrightarrow> \<turnstile> p\<close>
  using imply_completeness[where ps=\<open>[]\<close>] by simp

section \<open>Main Result\<close>

abbreviation \<open>valid p \<equiv> \<forall>I. I \<Turnstile> p\<close>

theorem main: \<open>valid p \<longleftrightarrow> \<turnstile> p\<close>
  using completeness soundness by fast

end
