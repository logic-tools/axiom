(*
   Authors: Asta Halkjær From & Jørgen Villadsen, DTU Compute
*)

chapter \<open>Formalizing Wajsberg's Axioms for Propositional Logic\<close>

theory System_W imports Main begin

text \<open>All references are to Alonzo Church (1956): Introduction to Mathematical Logic\<close>

section \<open>Syntax / Axiomatics / Semantics\<close>

datatype form = Falsity (\<open>\<bottom>\<close>) | Pro nat | Imp form form (infix \<open>\<rightarrow>\<close> 0)

text \<open>Wajsberg 1937 building on work by Frege, Tarski and Bernays [Church page 159]\<close>

inductive Axiomatics (\<open>\<turnstile>\<close>) where
  \<open>\<turnstile> q\<close> if \<open>\<turnstile> p\<close> and \<open>\<turnstile> (p \<rightarrow> q)\<close> |
  \<open>\<turnstile> (p \<rightarrow> (q \<rightarrow> p))\<close> |
  \<open>\<turnstile> ((p \<rightarrow> q) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> r)))\<close> |
  \<open>\<turnstile> (((p \<rightarrow> q) \<rightarrow> p) \<rightarrow> p)\<close> |
  \<open>\<turnstile> (\<bottom> \<rightarrow> p)\<close>

abbreviation Truth (\<open>\<top>\<close>) where \<open>\<top> \<equiv> (\<bottom> \<rightarrow> \<bottom>)\<close>

theorem \<open>\<turnstile> \<top>\<close> using Axiomatics.intros(5) .

primrec semantics (infix \<open>\<Turnstile>\<close> 0) where
  \<open>(I \<Turnstile> \<bottom>) = False\<close> |
  \<open>(I \<Turnstile> (Pro n)) = I n\<close> |
  \<open>(I \<Turnstile> (p \<rightarrow> q)) = (if I \<Turnstile> p then I \<Turnstile> q else True)\<close>

theorem \<open>I \<Turnstile> p\<close> if \<open>\<turnstile> p\<close> using that by induct auto

definition \<open>valid p \<equiv> \<forall>I. (I \<Turnstile> p)\<close>

theorem \<open>valid p = \<turnstile> p\<close> oops \<comment> \<open>Proof at end\<close>

abbreviation (input) \<open>Neg p \<equiv> (p \<rightarrow> \<bottom>)\<close>

lemmas MP = Axiomatics.intros(1)
lemmas Imp1 = Axiomatics.intros(2)
lemmas Tran = Axiomatics.intros(3)
lemmas Clas = Axiomatics.intros(4)
lemmas Expl = Axiomatics.intros(5)

section \<open>Soundness\<close>

theorem soundness: \<open>\<turnstile> p \<Longrightarrow> I \<Turnstile> p\<close>
  by (induct rule: Axiomatics.induct) auto

section \<open>Derived Rules\<close>

lemma Chu1: \<open>\<turnstile> ((p \<rightarrow> (p \<rightarrow> q)) \<rightarrow> (p \<rightarrow> q))\<close>
  by (meson Tran Clas MP)

lemma Chu2: \<open>\<turnstile> (p \<rightarrow> ((p \<rightarrow> q) \<rightarrow> q))\<close>
  by (meson Chu1 Imp1 Tran MP)

lemma Chu3: \<open>\<turnstile> ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> (q \<rightarrow> (p \<rightarrow> r)))\<close>
  by (meson Chu2 Tran MP)

lemma Chu4: \<open>\<turnstile> ((q \<rightarrow> r) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)))\<close>
  by (meson Chu3 Tran MP)

lemma Imp2: \<open>\<turnstile> ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)))\<close>
  by (meson Chu4 Chu1 MP Chu3)

lemma Imp3: \<open>\<turnstile> (p \<rightarrow> p)\<close>
  by (meson Imp1 Tran Clas MP)

lemma Neg: \<open>\<turnstile> (((p \<rightarrow> \<bottom>) \<rightarrow> \<bottom>) \<rightarrow> p)\<close>
  by (meson Chu4 Clas Expl MP)

text \<open>Wajsberg 1939 building on work by Frege [Church page 163]\<close>

inductive FW (\<open>\<tturnstile>\<close>) where
  \<open>\<tturnstile> q\<close> if \<open>\<tturnstile> p\<close> and \<open>\<tturnstile> (p \<rightarrow> q)\<close> |
  \<open>\<tturnstile> (p \<rightarrow> (q \<rightarrow> p))\<close> |
  \<open>\<tturnstile> ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)))\<close> |
  \<open>\<tturnstile> (((p \<rightarrow> \<bottom>) \<rightarrow> \<bottom>) \<rightarrow> p)\<close>

theorem Axiomatics_FW: \<open>\<turnstile> p \<longleftrightarrow> \<tturnstile> p\<close>
proof
  have *: \<open>\<tturnstile> ((p \<rightarrow> q) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> r)))\<close> for p q r
    by (metis FW.intros(1-3))
  then have **: \<open>\<tturnstile> (((p \<rightarrow> q) \<rightarrow> p) \<rightarrow> p)\<close> for p q
    by (metis FW.intros(1-4))
  show \<open>\<turnstile> p\<close> if \<open>\<tturnstile> p\<close>
    using that by induct (use Imp1 Imp2 Neg Axiomatics.intros in meson)+
  show \<open>\<tturnstile> p\<close> if \<open>\<turnstile> p\<close>
    using that by induct (use * ** FW.intros in meson)+
qed

lemma Neg1: \<open>\<turnstile> (p \<rightarrow> (Neg p \<rightarrow> q))\<close>
  by (meson Chu3 Chu4 Expl MP)

lemma Neg2: \<open>\<turnstile> (Neg (p \<rightarrow> q) \<rightarrow> p)\<close>
  by (metis Neg1 Tran MP Neg)

lemma Neg3: \<open>\<turnstile> (Neg (p \<rightarrow> q) \<rightarrow> Neg q)\<close>
  by (metis Imp1 Tran MP)

primrec imply :: \<open>form list \<Rightarrow> form \<Rightarrow> form\<close> where
  \<open>imply [] q = q\<close>
| \<open>imply (p # ps) q = (p \<rightarrow> imply ps q)\<close>

lemma imply_head: \<open>\<turnstile> (imply (p # ps) p)\<close>
  by (induct ps) (simp add: Imp3, metis Imp1 Imp2 MP imply.simps(2))

lemma imply_Cons: \<open>\<turnstile> (imply ps q) \<Longrightarrow> \<turnstile> (imply (p # ps) q)\<close>
  by (metis Imp1 MP imply.simps(2))

lemma imply_mem: \<open>p \<in> set ps \<Longrightarrow> \<turnstile> (imply ps p)\<close>
  using imply_head imply_Cons by (induct ps) auto

lemma imply_MP: \<open>\<turnstile> (imply ps p \<rightarrow> (imply ps (p \<rightarrow> q) \<rightarrow> imply ps q))\<close>
proof (induct ps)
  case Nil
  then show ?case
    by (metis Imp1 Imp2 MP imply.simps(1))
next
  case (Cons r ps)
  then show ?case
  proof -
    have \<open>\<turnstile> ((r \<rightarrow> imply ps p) \<rightarrow> (r \<rightarrow> (imply ps (p \<rightarrow> q) \<rightarrow> imply ps q)))\<close>
      by (meson Cons.hyps Imp1 Imp2 MP)
    then have \<open>\<turnstile> ((r \<rightarrow> imply ps p) \<rightarrow> ((r \<rightarrow> imply ps (p \<rightarrow> q)) \<rightarrow> (r \<rightarrow> imply ps q)))\<close>
      by (meson Imp2 Tran MP)
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
  by (metis Imp1 Imp2 MP imply.simps(2))

lemma cut': \<open>\<turnstile> (imply (p # ps) r) \<Longrightarrow> \<turnstile> (imply (q # ps) p) \<Longrightarrow> \<turnstile> (imply (q # ps) r)\<close>
  using imply_Cons cut imply4 by blast

lemma imply_lift: \<open>\<turnstile> (p \<rightarrow> q) \<Longrightarrow> \<turnstile> (imply ps p \<rightarrow> imply ps q)\<close>
proof (induct ps)
  case (Cons r ps)
  then show ?case
    by (metis MP Chu4 imply.simps(2))
qed simp

lemma Neg': \<open>\<turnstile> (imply ps (Neg (Neg p)) \<rightarrow> imply ps p)\<close>
  using Neg imply_lift by simp

lemma Boole: \<open>\<turnstile> (imply ((Neg p) # ps) \<bottom>) \<Longrightarrow> \<turnstile> (imply ps p)\<close>
  using deduct MP Neg' by blast

lemma imply_front: \<open>\<turnstile> (imply S p) \<Longrightarrow> set S - {q} \<subseteq> set S' \<Longrightarrow> \<turnstile> (imply (q # S') p)\<close>
  by (metis Diff_single_insert imply_weaken list.set(2))

section \<open>Consistent\<close>

definition consistent :: \<open>form set \<Rightarrow> bool\<close> where
  \<open>consistent S \<equiv> \<nexists>S'. set S' \<subseteq> S \<and> \<turnstile> (imply S' \<bottom>)\<close>

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

lemma extend_chain: \<open>extend S f n \<subseteq> extend S f (Suc n)\<close>
  by auto

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
  obtain n where n: \<open>f n = p\<close>
    using \<open>surj f\<close> unfolding surj_def by metis
  then have \<open>p \<notin> extend S f (Suc n)\<close>
    using \<open>p \<notin> Extend S f\<close> unfolding Extend_def by blast
  then have \<open>\<not> consistent ({p} \<union> extend S f n)\<close>
    using n by fastforce
  moreover have \<open>p \<notin> extend S f n\<close>
    using \<open>p \<notin> extend S f (Suc n)\<close> extend_chain by blast
  then have \<open>{p} \<union> extend S f n \<subseteq> {p} \<union> Extend S f\<close>
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
    (\<forall>n. Pro n \<in> H \<longrightarrow> (Neg (Pro n)) \<notin> H) \<and>
    (\<forall>p q. (p \<rightarrow> q) \<in> H \<longrightarrow> (Neg p) \<in> H \<or> q \<in> H) \<and>
    (\<forall>p q. (Neg (p \<rightarrow> q)) \<in> H \<longrightarrow> p \<in> H \<and> (Neg q) \<in> H)\<close>

abbreviation (input) \<open>model H n \<equiv> Pro n \<in> H\<close>

lemma hintikka_model: \<open>hintikka H \<Longrightarrow>
                        (p \<in> H \<longrightarrow> (model H \<Turnstile> p)) \<and> ((Neg p) \<in> H \<longrightarrow> \<not> (model H \<Turnstile> p))\<close>
  by (induct p) (simp; unfold hintikka_def, blast)+

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
  assume \<open>Pro n \<in> S\<close> \<open>(Neg (Pro n)) \<in> S\<close>
  moreover have \<open>\<turnstile> (imply [Pro n, Neg (Pro n)] \<bottom>)\<close>
    by (simp add: Neg1)
  ultimately show False
    using assms(2) unfolding consistent_def
    by (metis bot.extremum empty_set insert_subset list.set(2))
next
  fix p q
  assume *: \<open>(p \<rightarrow> q) \<in> S\<close> \<open>q \<notin> S\<close>
  then obtain Sq' where Sq': \<open>\<turnstile> (imply (q # Sq') \<bottom>)\<close> \<open>set Sq' \<subseteq> S\<close>
    using assms inconsistent_head by blast

  show \<open>(Neg p) \<in> S\<close>
  proof (rule ccontr)
    assume \<open>(Neg p) \<notin> S\<close>
    then obtain Sp' where Sp': \<open>\<turnstile> (imply ((Neg p) # Sp') \<bottom>)\<close> \<open>set Sp' \<subseteq> S\<close>
      using assms inconsistent_head by blast

    obtain S' where S': \<open>set S' = set Sp' \<union> set Sq'\<close>
      by (meson set_append)
    then have \<open>\<turnstile> (imply ((Neg p) # S') \<bottom>)\<close> \<open>\<turnstile> (imply (q # S') \<bottom>)\<close>
    proof -
      have \<open>set Sp' \<subseteq> set S'\<close>
        using S' by blast
      then show \<open>\<turnstile> (imply ((Neg p) # S') \<bottom>)\<close>
        by (metis Sp'(1) deduct imply_weaken)
      have \<open>set Sq' \<subseteq> set S'\<close>
        using S' by blast
      then show \<open>\<turnstile> (imply (q # S') \<bottom>)\<close>
        by (metis Sq'(1) deduct imply_weaken)
    qed
    then have \<open>\<turnstile> (imply ((p \<rightarrow> q) # S') \<bottom>)\<close>
      using Boole imply_Cons imply_head imply_mp' cut' by metis
    moreover have \<open>set ((p \<rightarrow> q) # S') \<subseteq> S\<close>
      using *(1) S' Sp'(2) Sq'(2) by auto
    ultimately show False
      using assms unfolding consistent_def by blast
  qed
next
  fix p q
  assume *: \<open>(Neg (p \<rightarrow> q)) \<in> S\<close>
  show \<open>p \<in> S\<close>
  proof (rule ccontr)
    assume \<open>p \<notin> S\<close>
    then obtain S' where S': \<open>\<turnstile> (imply (p # S') \<bottom>)\<close> \<open>set S' \<subseteq> S\<close>
      using assms inconsistent_head by blast
    moreover have \<open>\<turnstile> (imply ((Neg (p \<rightarrow> q)) # S') p)\<close>
      using add_imply Neg2 deduct by blast
    ultimately have \<open>\<turnstile> (imply ((Neg (p \<rightarrow> q)) # S') \<bottom>)\<close>
      using cut' by blast
    moreover have \<open>set ((Neg (p \<rightarrow> q)) # S') \<subseteq> S\<close>
      using *(1) S'(2) by fastforce
    ultimately show False
      using assms unfolding consistent_def by blast
  qed
next
  fix p q
  assume *: \<open>(Neg (p \<rightarrow> q)) \<in> S\<close>
  show \<open>(Neg q) \<in> S\<close>
  proof (rule ccontr)
    assume \<open>(Neg q) \<notin> S\<close>
    then obtain S' where S': \<open>\<turnstile> (imply ((Neg q) # S') \<bottom>)\<close> \<open>set S' \<subseteq> S\<close>
      using assms inconsistent_head by blast
    moreover have \<open>\<turnstile> (imply ((Neg (p \<rightarrow> q)) # S') (Neg q))\<close>
      using add_imply Neg3 deduct by blast
    ultimately have \<open>\<turnstile> (imply ((Neg (p \<rightarrow> q)) # S') \<bottom>)\<close>
      using cut' by blast
    moreover have \<open>set ((Neg (p \<rightarrow> q)) # S') \<subseteq> S\<close>
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
| \<open>form_of_btree (Branch (Leaf 0) (Leaf n)) = Pro n\<close>
| \<open>form_of_btree (Branch (Leaf (Suc 0)) (Branch t1 t2)) =
     Imp (form_of_btree t1) (form_of_btree t2)\<close>
| \<open>form_of_btree (Leaf (Suc _)) = undefined\<close>
| \<open>form_of_btree (Branch (Leaf 0) (Branch _ _)) = undefined\<close>
| \<open>form_of_btree (Branch (Leaf (Suc 0)) (Leaf _)) = undefined\<close>
| \<open>form_of_btree (Branch (Leaf (Suc (Suc _))) _) = undefined\<close>
| \<open>form_of_btree (Branch (Branch _ _) _) = undefined\<close>

primrec btree_of_form :: \<open>form \<Rightarrow> btree\<close> where
  \<open>btree_of_form Falsity = Leaf 0\<close>
| \<open>btree_of_form (Pro n) = Branch (Leaf 0) (Leaf n)\<close>
| \<open>btree_of_form (Imp p q) = Branch (Leaf (Suc 0))
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
  then have \<open>hintikka ?H\<close>
    using hintikka_Extend by blast

  have \<open>model ?H \<Turnstile> p\<close> if \<open>p \<in> ?S\<close> for p
    using that Extend_subset hintikka_model \<open>hintikka ?H\<close> by blast
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

section \<open>Using Shortest Axiom for Implicational Logic - Łukasiewicz 1936/1937\<close>

text \<open>Łukasiewicz 1948 building on work by Wajsberg, Tarski and Bernays [Church page 159]\<close>

inductive WL (\<open>\<then>\<close>) where
  \<open>\<then> q\<close> if \<open>\<then> p\<close> and \<open>\<then> (p \<rightarrow> q)\<close> |
  \<open>\<then> (((p \<rightarrow> q) \<rightarrow> r) \<rightarrow> ((r \<rightarrow> p) \<rightarrow> (s \<rightarrow> p)))\<close> |
  \<open>\<then> (\<bottom> \<rightarrow> p)\<close>

abbreviation (input) C :: \<open>form \<Rightarrow> form \<Rightarrow> form\<close> (\<open>C _ _\<close> [0, 0] 1) where \<open>(C p q) \<equiv> (p \<rightarrow> q)\<close>

lemma l1: \<open>\<then> (C C C p q r C C r p C s p)\<close>
  using WL.intros(2) .

lemma l2: \<open>\<then> (C C C C r p C s p C p q C r C p q)\<close>
  using l1 by (meson WL.intros(1))

lemma l3: \<open>\<then> (C C C r C p q C C r p C s p C t C C r p C s p)\<close>
  using l1 l2 by (meson WL.intros(1))

lemma l4: \<open>\<then> (C C C p q p C s p)\<close>
  using l3 l1 by (meson WL.intros(1))

lemma l5: \<open>\<then> (C C C s p C p q C r C p q)\<close>
  using l1 l4 by (meson WL.intros(1))

lemma l6: \<open>\<then> (C C C r C p q C s p C t C s p)\<close>
  using l1 l5 by (meson WL.intros(1))

lemma l7: \<open>\<then> (C C C t C s p C r C p q C u C r C p q)\<close>
  using l1 l6 by (meson WL.intros(1))

lemma l8: \<open>\<then> (C C C s q p C q p)\<close>
  using l7 l1 by (meson WL.intros(1))

lemma l9: \<open>\<then> (C r C C r p C s p)\<close>
  using l8 l1 by (meson WL.intros(1))

lemma l10: \<open>\<then> (C C C C C r q p C s p r C t r)\<close>
  using l1 l9 by (meson WL.intros(1))

lemma l11: \<open>\<then> (C C C t r C C C r q p C s p C u C C C r q p C s p)\<close>
  using l1 l10 by (meson WL.intros(1))

lemma l12: \<open>\<then> (C C C u C C C r q p C s p C t r C v C t r)\<close>
  using l1 l11 by (meson WL.intros(1))

lemma l13: \<open>\<then> (C C C v C t r C u C C C r q p C s p C w C u C C C r q p C s p)\<close>
  using l1 l12 by (meson WL.intros(1))

lemma l14: \<open>\<then> (C C C t r C s p C C C r q p C s p)\<close>
  using l13 l1 by (meson WL.intros(1))

lemma l15: \<open>\<then> (C C C r q C s p C C r p C s p)\<close>
  using l14 l1 by (meson WL.intros(1))

lemma l16: \<open>\<then> (C C r C s p C C C r q p C s p)\<close>
  using l15 l9 by (meson WL.intros(1))

lemma l17: \<open>\<then> (C C C C C p q r t C s p C C r p C s p)\<close>
  using l16 l1 by (meson WL.intros(1))

lemma l18: \<open>\<then> (C C C C r p C s p C C C p q r t C u C C C p q r t)\<close>
  using l1 l17 by (meson WL.intros(1))

lemma l19: \<open>\<then> (C C C C s p q C r p C C C p q r C s p)\<close>
  using l18 by (meson WL.intros(1))

lemma l20: \<open>\<then> (C C C C r p p C s p C C C p q r C s p)\<close>
  using l14 l19 by (meson WL.intros(1))

lemma l21: \<open>\<then> (C C C C p r q q C C q r C p r)\<close>
  using l20 l15 by (meson WL.intros(1))

lemma l22: \<open>\<then> (C p p)\<close>
  using l5 l4 by (meson WL.intros(1))

lemma l23: \<open>\<then> (C C C p q r C C r p p)\<close>
  using l20 l22 by (meson WL.intros(1))

lemma l24: \<open>\<then> (C r C C r p p)\<close>
  using l8 l23 by (meson WL.intros(1))

lemma l25: \<open>\<then> (C C p q C C C p r q q)\<close>
  using l15 l24 by (meson WL.intros(1))

lemma l26: \<open>\<then> (C C C C p q C C q r C p r C C C p r q q C C C p r q q)\<close>
  using l25 by (meson WL.intros(1))

lemma l27: \<open>\<then> (C p C q p)\<close>
  using l8 by (meson WL.intros(1))

lemma l28: \<open>\<then> (C C C p q p p)\<close>
  using l25 l22 by (meson WL.intros(1))

lemma l29: \<open>\<then> (C C p q C C q r C p r)\<close>
  using l21 l26 by (meson WL.intros(1))

theorem equivalence: \<open>\<then> p \<longleftrightarrow> \<turnstile> p\<close>
proof
  have *: \<open>\<turnstile> (((p \<rightarrow> q) \<rightarrow> r) \<rightarrow> ((r \<rightarrow> p) \<rightarrow> (s \<rightarrow> p)))\<close> for p q r s
    using completeness by simp
  show \<open>\<turnstile> p\<close> if \<open>\<then> p\<close>
    using that by induct (auto simp: * intro: Axiomatics.intros)
  show \<open>\<then> p\<close> if \<open>\<turnstile> p\<close>
    using that by induct (auto simp: l27 l28 l29 intro: WL.intros)
qed

end
