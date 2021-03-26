(*
   Authors: Asta Halkjær From, Jens Carl Moesgård Eschen & Jørgen Villadsen, DTU Compute
*)

chapter \<open>Formalizing Rasiowa's Axioms for Propositional Logic\<close>

theory System_R imports Main begin

text \<open>All references are to Alonzo Church (1956): Introduction to Mathematical Logic\<close>

section \<open>Syntax / Axiomatics / Semantics\<close>

datatype form = Pro nat | Neg form | Dis form form (infix \<open>\<Or>\<close> 0)

abbreviation Imp (infix \<open>\<rightarrow>\<close> 0) where \<open>(p \<rightarrow> q) \<equiv> (Neg p \<Or> q)\<close>

text \<open>Rasiowa 1949 building on Russell 1908, Bernays 1926 and Götlind 1947 [Church page 157]\<close>

inductive Axiomatics (\<open>\<turnstile>\<close>) where
  \<open>\<turnstile> q\<close> if \<open>\<turnstile> p\<close> and \<open>\<turnstile> (p \<rightarrow> q)\<close> |
  \<open>\<turnstile> ((p \<Or> p) \<rightarrow> p)\<close> |
  \<open>\<turnstile> (p \<rightarrow> (p \<Or> q))\<close> |
  \<open>\<turnstile> ((p \<rightarrow> q) \<rightarrow> ((r \<Or> p) \<rightarrow> (q \<Or> r)))\<close>

abbreviation Truth (\<open>\<top>\<close>) where \<open>\<top> \<equiv> (undefined \<rightarrow> undefined)\<close>

theorem \<open>\<turnstile> \<top>\<close> using Axiomatics.intros by metis

primrec semantics (infix \<open>\<Turnstile>\<close> 0) where
  \<open>(I \<Turnstile> Pro n) = I n\<close> |
  \<open>(I \<Turnstile> Neg p) = (if I \<Turnstile> p then False else True)\<close> |
  \<open>(I \<Turnstile> (p \<Or> q)) = (if I \<Turnstile> p then True else (I \<Turnstile> q))\<close>

theorem \<open>I \<Turnstile> p\<close> if \<open>\<turnstile> p\<close> using that by induct auto

definition \<open>valid p \<equiv> \<forall>I. (I \<Turnstile> p)\<close>

theorem \<open>valid p = \<turnstile> p\<close> oops \<comment> \<open>Proof at end\<close>

abbreviation Falsity (\<open>\<bottom>\<close>) where \<open>\<bottom> \<equiv> Neg \<top>\<close>

theorem \<open>\<turnstile> (\<bottom> \<rightarrow> p)\<close> using Axiomatics.intros by metis

lemmas MP = Axiomatics.intros(1)
lemmas Idem = Axiomatics.intros(2)
lemmas AddR = Axiomatics.intros(3)
lemmas Swap = Axiomatics.intros(4)

section \<open>Soundness\<close>

theorem soundness: \<open>\<turnstile> p \<Longrightarrow> I \<Turnstile> p\<close>
  by (induct rule: Axiomatics.induct) auto

section \<open>Derived Rules\<close>

proposition alternative_axiom: \<open>\<turnstile> (p \<rightarrow> (p \<Or> q))\<close> if \<open>\<And>p q. \<turnstile> (p \<rightarrow> (q \<Or> p))\<close>
  by (metis MP Idem Swap that)

lemma AddL: \<open>\<turnstile> (p \<rightarrow> (q \<Or> p))\<close>
  by (metis MP Idem Swap AddR)

lemma Perm: \<open>\<turnstile> ((p \<Or> q) \<rightarrow> (q \<Or> p))\<close>
  by (metis Idem AddL AddR Swap MP)

lemma SwapCon: \<open>\<turnstile> ((p \<rightarrow> (q \<Or> r)) \<rightarrow> (p \<rightarrow> (r \<Or> q)))\<close>
  by (meson MP Perm Swap)

lemma SubR: \<open>\<turnstile> ((p \<rightarrow> q) \<rightarrow> ((r \<Or> p) \<rightarrow> (r \<Or> q)))\<close>
  by (meson MP SwapCon Swap)

text \<open>Russell 1908 and Bernays 1926 [Church page 157]\<close>

inductive RB (\<open>\<tturnstile>\<close>) where
  \<open>\<tturnstile> q\<close> if \<open>\<tturnstile> p\<close> and \<open>\<tturnstile> (p \<rightarrow> q)\<close> |
  \<open>\<tturnstile> ((p \<Or> p) \<rightarrow> p)\<close> |
  \<open>\<tturnstile> (p \<rightarrow> (q \<Or> p))\<close> |
  \<open>\<tturnstile> ((p \<Or> q) \<rightarrow> (q \<Or> p))\<close> |
  \<open>\<tturnstile> ((p \<rightarrow> q) \<rightarrow> ((r \<Or> p) \<rightarrow> (r \<Or> q)))\<close>

theorem Axiomatics_RB: \<open>\<turnstile> p \<longleftrightarrow> \<tturnstile> p\<close>
proof
  show \<open>\<turnstile> p\<close> if \<open>\<tturnstile> p\<close>
    using that by induct (use SubR Axiomatics.intros in meson)+
  show \<open>\<tturnstile> p\<close> if \<open>\<turnstile> p\<close>
    using that by induct (use RB.intros in meson)+
qed

lemma SwapAnte: \<open>\<turnstile> (((p \<Or> q) \<rightarrow> r) \<rightarrow> ((q \<Or> p) \<rightarrow> r))\<close>
  by (metis AddR Idem MP Perm Swap)

lemma SubL: \<open>\<turnstile> ((p \<rightarrow> q) \<rightarrow> ((p \<Or> r) \<rightarrow> (q \<Or> r)))\<close>
  by (meson MP SwapAnte Swap)

lemma AddM: \<open>\<turnstile> ((p \<Or> q) \<rightarrow> ((p \<Or> r) \<Or> q))\<close>
  by (meson SubL MP AddR)

lemma Church1: \<open>\<turnstile> ((p \<Or> (p \<Or> q)) \<rightarrow> (p \<Or> q))\<close>
  by (meson Idem MP SubL SubR AddR)

lemma Church2: \<open>\<turnstile> (p \<Or> ((p \<Or> q) \<rightarrow> q))\<close>
  by (metis Church1 MP Swap AddL AddM)

lemma Imp1: \<open>\<turnstile> (p \<rightarrow> p)\<close>
  by (metis Idem AddL AddR Swap MP)

lemma Neg': \<open>\<turnstile> ((p \<Or> q) \<rightarrow> (Neg q \<rightarrow> p))\<close>
  using Imp1 MP Swap by blast

lemma Tran: \<open>\<turnstile> ((p \<rightarrow> q) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> r)))\<close>
  by (meson Neg' SubL MP)

lemma Church3: \<open>\<turnstile> ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> (q \<rightarrow> (p \<rightarrow> r)))\<close>
  by (meson Church2 Tran MP)

lemma Neg: \<open>\<turnstile> ((p \<rightarrow> \<bottom>) \<rightarrow> Neg p)\<close>
  by (metis Church3 Imp1 MP Perm)

lemma ImpER: \<open>\<turnstile> ((p \<Or> (q \<rightarrow> r)) \<rightarrow> (q \<rightarrow> (p \<Or> r)))\<close>
  using SubR by (metis Church2 MP)

lemma SubR': \<open>\<turnstile> ((p \<Or> q) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> (p \<Or> r)))\<close>
  using SubR Church3 MP by blast

lemma SubL': \<open>\<turnstile> ((p \<Or> q) \<rightarrow> ((p \<rightarrow> r) \<rightarrow> (r \<Or> q)))\<close>
  using SubL Church3 MP by blast

lemma FalsityE': \<open>\<turnstile> ((p \<Or> q) \<rightarrow> ((Neg p \<Or> q) \<rightarrow> q))\<close>
  by (meson SubR SubL' MP Idem)

lemma FalsityE'': \<open>\<turnstile> ((Neg p \<Or> r) \<rightarrow> ((p \<Or> q) \<rightarrow> (q \<Or> r)))\<close>
  by (meson ImpER MP SubR' SwapAnte)

lemma FalsityEImpER: \<open>\<turnstile> ((Neg p \<Or> r) \<rightarrow> ((p \<Or> q) \<rightarrow> ((Neg q \<Or> r) \<rightarrow> r)))\<close>
  using FalsityE'' FalsityE' by (meson SubR MP)

lemma DisE: \<open>\<turnstile> ((p \<rightarrow> r) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> ((p \<Or> q) \<rightarrow> r)))\<close>
  using FalsityEImpER by (meson MP ImpER Tran)

lemma Imp2: \<open>\<turnstile> ((p \<Or> (q \<rightarrow> r)) \<rightarrow> ((p \<Or> q) \<rightarrow> (p \<Or> r)))\<close>
  using DisE SubR MP AddL AddR by metis

lemma Imp2': \<open>\<turnstile> ((p \<rightarrow> q) \<rightarrow> ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> (p \<rightarrow> r)))\<close>
  by (metis AddL Imp2 Tran MP)

primrec imply :: \<open>form list \<Rightarrow> form \<Rightarrow> form\<close> where
  \<open>imply [] q = q\<close>
| \<open>imply (p # ps) q = (p \<rightarrow> imply ps q)\<close>

lemma imply_head: \<open>\<turnstile> (imply (p # ps) p)\<close>
  by (induct ps) (simp add: Imp1, metis AddL Imp2 MP imply.simps(2))

lemma imply_Cons: \<open>\<turnstile> (imply ps q) \<Longrightarrow> \<turnstile> (imply (p # ps) q)\<close>
  by (metis AddL MP imply.simps(2))

lemma imply_mem: \<open>p \<in> set ps \<Longrightarrow> \<turnstile> (imply ps p)\<close>
  using imply_head imply_Cons by (induct ps) auto

lemma imply_MP: \<open>\<turnstile> (imply ps p \<rightarrow> (imply ps (p \<rightarrow> q) \<rightarrow> imply ps q))\<close>
proof (induct ps)
  case Nil
  then show ?case
    by (simp add: Church2)
next
  case (Cons r ps)
  then show ?case
  proof -
    have \<open>\<turnstile> ((r \<rightarrow> imply ps p) \<rightarrow> (r \<rightarrow> (imply ps (p \<rightarrow> q) \<rightarrow> imply ps q)))\<close>
      by (meson Cons.hyps AddL Imp2 MP)
    then have \<open>\<turnstile> ((r \<rightarrow> imply ps p) \<rightarrow> ((r \<rightarrow> imply ps (p \<rightarrow> q)) \<rightarrow> (r \<rightarrow> imply ps q)))\<close>
      by (meson Imp2' Church3 Tran MP)
    then show ?thesis
      by simp
  qed
qed

lemma imply_mp': \<open>\<turnstile> (imply ps p) \<Longrightarrow> \<turnstile> (imply ps (p \<rightarrow> q)) \<Longrightarrow> \<turnstile> (imply ps q)\<close>
  using imply_MP by (meson MP)

lemma add_imply: \<open>\<turnstile> q \<Longrightarrow> \<turnstile> (imply ps q)\<close>
  using imply_Cons by (induct ps) simp_all

lemma imply_append: \<open>imply (ps @ qs) r = imply ps (imply qs r)\<close>
  by (induct ps) simp_all

lemma imply_swap: \<open>\<turnstile> (imply (ps @ qs) r) \<Longrightarrow> \<turnstile> (imply (qs @ ps) r)\<close>
proof (induct qs arbitrary: ps)
  case (Cons q qs)
  then show ?case
    by (metis imply_Cons imply_head imply_mp' imply.simps(2) imply_append)
qed simp

lemma deduct: \<open>\<turnstile> (imply (p # ps) q) \<longleftrightarrow> \<turnstile> (imply ps (p \<rightarrow> q))\<close>
  using imply_swap by (metis imply.simps(1-2) imply_append)

theorem imply_weaken: \<open>\<turnstile> (imply ps q) \<Longrightarrow> set ps \<subseteq> set ps' \<Longrightarrow> \<turnstile> (imply ps' q)\<close>
proof (induct ps arbitrary: q)
  case (Cons p ps)
  note \<open>\<turnstile> (imply (p # ps) q)\<close>
  then have \<open>\<turnstile> (imply ps (p \<rightarrow> q))\<close>
    using deduct by blast
  then have \<open>\<turnstile> (imply ps' (p \<rightarrow> q))\<close>
    using Cons by simp
  then show ?case
    using Cons(3) by (meson imply_mem imply_mp' list.set_intros(1) subset_code(1))
qed (simp add: add_imply)

lemma cut: \<open>\<turnstile> (imply ps p) \<Longrightarrow> \<turnstile> (imply (p # ps) q) \<Longrightarrow> \<turnstile> (imply ps q)\<close>
  using deduct imply_mp' by blast

lemma imply4: \<open>\<turnstile> (imply (p # q # ps) r) \<Longrightarrow> \<turnstile> (imply (q # p # ps) r)\<close>
  by (metis ImpER MP imply.simps(2))

lemma cut': \<open>\<turnstile> (imply (p # ps) r) \<Longrightarrow> \<turnstile> (imply (q # ps) p) \<Longrightarrow> \<turnstile> (imply (q # ps) r)\<close>
  using imply_Cons cut imply4 by blast

lemma imply_lift: \<open>\<turnstile> (p \<rightarrow> q) \<Longrightarrow> \<turnstile> (imply ps p \<rightarrow> imply ps q)\<close>
  by (metis Imp1 add_imply imply.simps(2) imply_mp')

lemma DNeg: \<open>\<turnstile> (Neg (Neg p) \<rightarrow> p)\<close>
  by (metis Idem AddR Swap MP)

lemma imply_DNeg: \<open>\<turnstile> (imply ps (Neg (Neg p)) \<rightarrow> imply ps p)\<close>
  using DNeg imply_lift by simp

lemma Boole: \<open>\<turnstile> (imply ((Neg p) # ps) \<bottom>) \<Longrightarrow> \<turnstile> (imply ps p)\<close>
  by (meson Neg MP imply_DNeg deduct imply_lift)

lemma imply_front: \<open>\<turnstile> (imply S p) \<Longrightarrow> set S - {q} \<subseteq> set S' \<Longrightarrow> \<turnstile> (imply (q # S') p)\<close>
  by (metis Diff_single_insert imply_weaken list.set(2))

lemma FalsityE: \<open>\<turnstile> (p \<rightarrow> (Neg p \<rightarrow> q))\<close>
  using AddM Imp1 MP Perm by blast

section \<open>Consistent\<close>

definition consistent :: \<open>form set \<Rightarrow> bool\<close> where
  \<open>consistent S \<equiv> \<nexists>S'. set S' \<subseteq> S \<and> \<turnstile> (imply S' \<bottom>)\<close>

lemma UN_finite_bound:
  assumes \<open>finite p\<close> \<open>p \<subseteq> (\<Union>n. f n)\<close>
  shows \<open>\<exists>m :: nat. p \<subseteq> (\<Union>n \<le> m. f n)\<close>
  using assms
proof (induct rule: finite_induct)
  case (insert x p)
  then obtain m where \<open>p \<subseteq> (\<Union>n \<le> m. f n)\<close>
    by fast
  then have \<open>p \<subseteq> (\<Union>n \<le> (m + k). f n)\<close> for k
    by fastforce
  moreover obtain m' where \<open>x \<in> f m'\<close>
    using insert(4) by blast
  ultimately have \<open>{x} \<union> p \<subseteq> (\<Union>n \<le> m + m'. f n)\<close>
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
  then obtain S' where \<open>\<turnstile> (imply S' \<bottom>)\<close> \<open>set S' \<subseteq> (\<Union>n. extend S f n)\<close>
    unfolding consistent_def by blast
  then obtain m where \<open>set S' \<subseteq> (\<Union>n \<le> m. extend S f n)\<close>
    using UN_finite_bound by (metis List.finite_set)
  then have \<open>set S' \<subseteq> extend S f m\<close>
    using extend_bound by blast
  moreover have \<open>consistent (extend S f m)\<close>
    using assms consistent_extend by blast
  ultimately show False
    unfolding consistent_def using \<open>\<turnstile> (imply S' \<bottom>)\<close> by blast
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
    NoFalsity: \<open>\<bottom> \<notin> H\<close> and
    ProP: \<open>Pro n \<in> H \<Longrightarrow> (Neg (Pro n)) \<notin> H\<close> and
    DisP: \<open>(p \<Or> q) \<in> H \<Longrightarrow> p \<in> H \<or> q \<in> H\<close> and
    DisN: \<open>(Neg (p \<Or> q)) \<in> H \<Longrightarrow> (Neg p) \<in> H \<and> (Neg q) \<in> H\<close> and
    NegN: \<open>(Neg (Neg p)) \<in> H \<Longrightarrow> p \<in> H\<close>

abbreviation (input) \<open>model H n \<equiv> Pro n \<in> H\<close>

lemma Hintikka_model:
  \<open>Hintikka H \<Longrightarrow> (p \<in> H \<longrightarrow> (model H \<Turnstile> p)) \<and> ((Neg p) \<in> H \<longrightarrow> \<not> (model H \<Turnstile> p))\<close>
  by (induct p) (simp; unfold Hintikka_def, blast)+

lemma inconsistent_head:
  assumes \<open>maximal S\<close> \<open>consistent S\<close> \<open>p \<notin> S\<close>
  shows \<open>\<exists>S'. \<turnstile> (imply (p # S') \<bottom>) \<and> set S' \<subseteq> S\<close>
proof -
  obtain S' where S': \<open>\<turnstile> (imply S' \<bottom>)\<close> \<open>set S' \<subseteq> {p} \<union> S\<close> \<open>p \<in> set S'\<close>
    using assms unfolding maximal_def consistent_def by fast
  then obtain S'' where S'': \<open>\<turnstile> (imply (p # S'') \<bottom>)\<close> \<open>set S'' = set S' - {p}\<close>
    by (metis imply_front set_removeAll subset_refl)
  then show ?thesis
    using S'(2) by fast
qed

lemma Hintikka_Extend:
  assumes \<open>maximal S\<close> \<open>consistent S\<close>
  shows \<open>Hintikka S\<close>
proof
  show \<open>\<bottom> \<notin> S\<close>
    using assms(2) imply_head imply_mem unfolding consistent_def
    by (metis List.set_insert empty_set insert_Diff insert_is_Un singletonI sup.cobounded1)
next
  fix n
  assume \<open>Pro n \<in> S\<close>
  moreover have \<open>\<turnstile> (imply [Pro n, Neg (Pro n)] \<bottom>)\<close>
    by (simp add: FalsityE)
  ultimately show \<open>(Neg (Pro n)) \<notin> S\<close>
    using assms(2) unfolding consistent_def
    by (metis bot.extremum empty_set insert_subset list.set(2))
next
  fix p q
  assume *: \<open>(p \<Or> q) \<in> S\<close>
  show \<open>p \<in> S \<or> q \<in> S\<close>
  proof (rule disjCI, rule ccontr)
    assume **: \<open>q \<notin> S\<close>
    then obtain Sq' where Sq': \<open>\<turnstile> (imply (q # Sq') \<bottom>)\<close> \<open>set Sq' \<subseteq> S\<close>
      using assms inconsistent_head by blast
    assume \<open>p \<notin> S\<close>
    then obtain Sp' where Sp': \<open>\<turnstile> (imply (p # Sp') \<bottom>)\<close> \<open>set Sp' \<subseteq> S\<close>
      using assms inconsistent_head by blast
    obtain S' where S': \<open>set S' = set Sp' \<union> set Sq'\<close> \<open>set S' \<subseteq> S\<close>
      using Sq'(2) Sp'(2) by (metis le_sup_iff set_union)
    then have \<open>\<turnstile> (imply (p # S') \<bottom>)\<close> \<open>\<turnstile> (imply (q # S') \<bottom>)\<close>
      using Sq' Sp' deduct imply_weaken by simp_all
    then have \<open>\<turnstile> (imply ((p \<Or> q) # S') \<bottom>)\<close>
      by (metis DisE MP imply.simps(2))
    moreover have \<open>set ((p \<Or> q) # S') \<subseteq> S\<close>
      using * S' Sp'(2) Sq'(2) by auto
    ultimately show False
      using assms unfolding consistent_def by blast
  qed
next
  fix p q
  assume *: \<open>(Neg (p \<Or> q)) \<in> S\<close>
  show \<open>(Neg p) \<in> S \<and> (Neg q) \<in> S\<close>
  proof (rule conjI; rule ccontr)
    assume \<open>(Neg p) \<notin> S\<close>
    then obtain S' where S': \<open>\<turnstile> (imply ((Neg p) # S') \<bottom>)\<close> \<open>set S' \<subseteq> S - {Neg p}\<close>
      using assms inconsistent_head by blast
    moreover have \<open>\<turnstile> (imply ((Neg (p \<Or> q)) # S') (Neg p))\<close>
      using Idem AddR Tran add_imply deduct MP by metis
    ultimately have \<open>\<turnstile> (imply ((Neg (p \<Or> q)) # S') \<bottom>)\<close>
      using cut' by blast
    moreover have \<open>set ((Neg (p \<Or> q)) # S') \<subseteq> S\<close>
      using * S'(2) by auto
    ultimately show False
      using assms unfolding consistent_def by blast
  next
    assume \<open>(Neg q) \<notin> S\<close>
    then obtain S' where S': \<open>\<turnstile> (imply ((Neg q) # S') \<bottom>)\<close> \<open>set S' \<subseteq> S - {Neg q}\<close>
      using assms inconsistent_head by blast
    moreover have \<open>\<turnstile> (imply ((Neg (p \<Or> q)) # S') (Neg q))\<close>
      using Idem AddR AddL Tran add_imply deduct MP Neg' by metis
    ultimately have \<open>\<turnstile> (imply ((Neg (p \<Or> q)) # S') \<bottom>)\<close>
      using cut' by blast
    moreover have \<open>set ((Neg (p \<Or> q)) # S') \<subseteq> S\<close>
      using *(1) S'(2) by auto
    ultimately show False
      using assms unfolding consistent_def by blast
  qed
next
  fix p
  assume *: \<open>(Neg (Neg p)) \<in> S\<close>
  show \<open>p \<in> S\<close>
  proof (rule ccontr)
    assume \<open>p \<notin> S\<close>
    then obtain SNA where SNA: \<open>\<turnstile> (imply (p # SNA) \<bottom>)\<close> \<open>set SNA \<subseteq> S\<close>
      using assms inconsistent_head by blast
    from * obtain SA where SA: \<open>\<turnstile> (imply SA p)\<close> \<open>set SA \<subseteq> S\<close>
      using imply_DNeg MP
      by (metis empty_set empty_subsetI imply_head insert_absorb insert_mono list.simps(15))
    obtain S' where S': \<open>set S' = set SA \<union> set SNA\<close> \<open>set S' \<subseteq> S\<close>
      using SA(2) SNA(2) by (metis Un_subset_iff set_union)
    with SNA SA have \<open>\<turnstile> (imply (p # S') \<bottom>)\<close> \<open>\<turnstile> (imply S' p)\<close>
      using deduct imply_weaken by simp_all
    with S' assms show \<open>False\<close> unfolding consistent_def
      using cut by meson
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
  \<open>form_of_btree (Leaf n) = undefined\<close>
| \<open>form_of_btree (Branch (Leaf 0) (Leaf n)) = Pro n\<close>
| \<open>form_of_btree (Branch (Leaf (Suc 0)) (Branch t1 t2)) =
     Dis (form_of_btree t1) (form_of_btree t2)\<close>
| \<open>form_of_btree (Branch (Leaf 0) (Branch t _)) = Neg (form_of_btree t)\<close>
| \<open>form_of_btree (Branch (Leaf (Suc 0)) (Leaf _)) = undefined\<close>
| \<open>form_of_btree (Branch (Leaf (Suc (Suc _))) _) = undefined\<close>
| \<open>form_of_btree (Branch (Branch _ _) _) = undefined\<close>

primrec btree_of_form :: \<open>form \<Rightarrow> btree\<close> where
  \<open>btree_of_form (Pro n) = Branch (Leaf 0) (Leaf n)\<close>
| \<open>btree_of_form (Neg p) = Branch (Leaf 0) (Branch (btree_of_form p) (Leaf 0))\<close>
| \<open>btree_of_form (Dis p q) = Branch (Leaf (Suc 0))
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
  assumes valid: \<open>\<forall>I s. list_all (\<lambda>q. (I \<Turnstile> q)) ps \<longrightarrow> (I \<Turnstile> p)\<close>
  shows \<open>\<turnstile> (imply ps p)\<close>
proof (rule ccontr)
  assume \<open>\<not> \<turnstile> (imply ps p)\<close>
  then have *: \<open>\<not> \<turnstile> (imply ((Neg p) # ps) \<bottom>)\<close>
    using Boole by blast

  let ?S = \<open>set ((Neg p) # ps)\<close>
  let ?H = \<open>Extend ?S from_nat\<close>

  have \<open>consistent ?S\<close>
    unfolding consistent_def using * imply_weaken by blast
  then have \<open>consistent ?H\<close> \<open>maximal ?H\<close>
    using consistent_Extend maximal_Extend surj_from_nat by blast+
  then have \<open>Hintikka ?H\<close>
    using Hintikka_Extend by blast

  have \<open>model ?H \<Turnstile> p\<close> if \<open>p \<in> ?S\<close> for p
    using that Extend_subset Hintikka_model \<open>Hintikka ?H\<close> by blast
  then have \<open>model ?H \<Turnstile> (Neg p)\<close> \<open>list_all (\<lambda>p. (model ?H \<Turnstile> p)) ps\<close>
    unfolding list_all_def by fastforce+
  then have \<open>model ?H \<Turnstile> p\<close>
    using valid by blast
  then show False
    using \<open>model ?H \<Turnstile> (Neg p)\<close> by simp
qed

theorem completeness: \<open>\<forall>I. (I \<Turnstile> p) \<Longrightarrow> \<turnstile> p\<close>
  using imply_completeness[where ps=\<open>[]\<close>] by simp

section \<open>Main Result\<close>

theorem main: \<open>valid p = \<turnstile> p\<close>
proof
  assume \<open>valid p\<close>
  with completeness show \<open>\<turnstile> p\<close>
    unfolding valid_def .
next
  assume \<open>\<turnstile> p\<close>
  with soundness show \<open>valid p\<close>
    unfolding valid_def by (intro allI)
qed

section \<open>Using Unnecessary Axiom in Principia Mathematica (PM) by Whitehead and Russell 1910\<close>

text \<open>First appeared in Russell 1908 and derived from the other axioms in Bernays 1926 (system RB)\<close>

inductive PM (\<open>\<then>\<close>) where
  \<open>\<then> q\<close> if \<open>\<then> p\<close> and \<open>\<then> (p \<rightarrow> q)\<close> |
  \<open>\<then> ((p \<Or> p) \<rightarrow> p)\<close> |
  \<open>\<then> (p \<rightarrow> (q \<Or> p))\<close> |
  \<open>\<then> ((p \<Or> q) \<rightarrow> (q \<Or> p))\<close> |
  \<open>\<then> ((p \<Or> (q \<Or> r)) \<rightarrow> (q \<Or> (p \<Or> r)))\<close> |
  \<open>\<then> ((p \<rightarrow> q) \<rightarrow> ((r \<Or> p) \<rightarrow> (r \<Or> q)))\<close>

proposition PM_extends_RB: \<open>\<tturnstile> p \<Longrightarrow> \<then> p\<close>
  by (induct rule: RB.induct) (auto intro: PM.intros)

theorem equivalence: \<open>\<then> p \<longleftrightarrow> \<turnstile> p\<close>
proof
  have *: \<open>\<turnstile> ((p \<Or> (q \<Or> r)) \<rightarrow> (q \<Or> (p \<Or> r)))\<close> for p q r
    using completeness by simp
  show \<open>\<turnstile> p\<close> if \<open>\<then> p\<close>
    using that by induct (use * SubR Axiomatics.intros in meson)+
  show \<open>\<then> p\<close> if \<open>\<turnstile> p\<close>
    using that by induct (use PM.intros in meson)+
qed

corollary associativity:
  \<open>\<then> (((p \<Or> q) \<Or> r) \<rightarrow> (p \<Or> (q \<Or> r)))\<close>
  \<open>\<then> ((p \<Or> (q \<Or> r)) \<rightarrow> ((p \<Or> q) \<Or> r))\<close>
  using equivalence completeness by simp_all

end
