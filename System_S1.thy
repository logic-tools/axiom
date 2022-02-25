(*
   Authors: Asta Halkjær From, Agnes Moesgård Eschen & Jørgen Villadsen, DTU Compute
*)

theory System_S1 imports System_L1 begin

text \<open>System S1 from Boleslaw Sobocinski: Axiomatization of a Conjunctive-Negative Calculus
                                          of Propositions (1954)\<close>

text \<open>Derivations are taken from: On Axiom Systems of Propositional Calculi. XI
                                  by Kashiko Tanaka (1965)\<close>

inductive S1 (\<open>\<SS>\<^sub>1\<close>) where
  S1_MP: \<open>\<SS>\<^sub>1 q\<close> if \<open>\<SS>\<^sub>1 p\<close> and \<open>\<SS>\<^sub>1 (p \<rightarrow> q)\<close> |
  S1_1:  \<open>\<SS>\<^sub>1 ((\<sim> p) \<rightarrow> (p \<rightarrow> q))\<close> |
  S1_2:  \<open>\<SS>\<^sub>1 (p \<rightarrow> (q \<rightarrow> (r \<rightarrow> p)))\<close> |
  S1_3:  \<open>\<SS>\<^sub>1 (((\<sim> p) \<rightarrow> r) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> r)))\<close>

lemma S1_4: \<open>\<SS>\<^sub>1 ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> ((q \<rightarrow> p) \<rightarrow> (q \<rightarrow> r)))\<close>
  using S1_1 S1_3 S1_MP by metis

lemma S1_5: \<open>\<SS>\<^sub>1 ((q \<rightarrow> p) \<rightarrow> (q \<rightarrow> (r \<rightarrow> p)))\<close>
  using S1_2 S1_4 S1_MP by metis

lemma S1_6: \<open>\<SS>\<^sub>1 ((\<sim> p) \<rightarrow> (s \<rightarrow> (p \<rightarrow> q)))\<close>
  using S1_1 S1_5 S1_MP by metis

lemma S1_7: \<open>\<SS>\<^sub>1 ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> (q \<rightarrow> (p \<rightarrow> r)))\<close>
  using S1_3 S1_5 S1_6 S1_MP by metis

lemma S1_8: \<open>\<SS>\<^sub>1 (q \<rightarrow> ((q \<rightarrow> p) \<rightarrow> (r \<rightarrow> p)))\<close>
  using S1_5 S1_7 S1_MP by metis

lemma S1_9: \<open>\<SS>\<^sub>1 ((p \<rightarrow> q) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> r)))\<close>
  using S1_3 S1_6 S1_8 S1_MP by metis

lemma S1_10: \<open>\<SS>\<^sub>1 ((p \<rightarrow> q) \<rightarrow> (s \<rightarrow> (p \<rightarrow> q)))\<close>
  using S1_2 S1_3 S1_6 S1_MP by metis

lemma S1_11: \<open>\<SS>\<^sub>1 ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> q))\<close>
  using S1_4 S1_10 S1_MP by metis

lemma S1_12: \<open>\<SS>\<^sub>1 ((q \<rightarrow> (q \<rightarrow> r)) \<rightarrow> (q \<rightarrow> r))\<close>
  using S1_4 S1_11 S1_MP by metis

lemma S1_13: \<open>\<SS>\<^sub>1 (p \<rightarrow> (q \<rightarrow> p))\<close>
  using S1_2 S1_12 S1_MP by metis

lemma S1_14: \<open>\<SS>\<^sub>1 (p \<rightarrow> p)\<close>
  using S1_12 S1_13 S1_MP by metis

lemma S1_15: \<open>\<SS>\<^sub>1 (p \<rightarrow> ((\<sim> p) \<rightarrow> q))\<close>
  using S1_1 S1_7 S1_MP by metis

lemma S1_16: \<open>\<SS>\<^sub>1 ((\<sim> (\<sim> p)) \<rightarrow> p)\<close>
  using S1_3 S1_13 S1_14 S1_15 S1_MP by metis

lemma S1_17: \<open>\<SS>\<^sub>1 (((\<sim> p) \<rightarrow> p) \<rightarrow> p)\<close>
  using S1_3 S1_14 S1_16 S1_MP by metis

theorem S1_iff_L1: \<open>\<SS>\<^sub>1 p \<longleftrightarrow> \<turnstile> p\<close>
proof
  have L1_S1_1: \<open>\<turnstile> ((\<sim> p) \<rightarrow> (p \<rightarrow> q))\<close> for p q
    using L1_completeness by simp
  have L1_S1_2: \<open>\<turnstile> (p \<rightarrow> (q \<rightarrow> (r \<rightarrow> p)))\<close> for p q r
    using L1_completeness by simp
  have L1_S1_3: \<open>\<turnstile> (((\<sim> p) \<rightarrow> r) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> r)))\<close> for p q r
    using L1_completeness by simp
  show \<open>\<turnstile> p\<close> if \<open>\<SS>\<^sub>1 p\<close>
    using that by (induct) (metis MP, metis L1_S1_1, metis L1_S1_2, metis L1_S1_3)
  show \<open>\<SS>\<^sub>1 p\<close> if \<open>\<turnstile> p\<close>
    using that by (induct) (metis S1_MP, metis S1_9, metis S1_17, metis S1_15)
qed

theorem S1_soundness: \<open>\<SS>\<^sub>1 p \<Longrightarrow> I \<Turnstile> p\<close>
  by (induct rule: S1.induct) auto

theorem S1_completeness: \<open>\<forall>I. (I \<Turnstile> p) \<Longrightarrow> \<SS>\<^sub>1 p\<close>
  using S1_iff_L1 by (simp add: L1_completeness)

section \<open>Soundness and Completeness\<close>

theorem main: \<open>valid p = \<SS>\<^sub>1 p\<close>
  unfolding valid_def using S1_soundness S1_completeness by blast

lemmas S1 = S1.intros main

end
