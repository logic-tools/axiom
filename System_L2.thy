(*
   Authors: Asta Halkjær From, Agnes Moesgård Eschen & Jørgen Villadsen, DTU Compute
*)

theory System_L2 imports System_L1 begin

text \<open>System L2 from Jan Lukasiewicz: ???\<close>

text \<open>Derivations are taken from: On Axiom Systems of Propositional Calculi. XII
                                  by Yoshinari Arai (1965)\<close>

inductive L2 (\<open>\<LL>\<^sub>2\<close>) where
  L2_MP: \<open>\<LL>\<^sub>2 q\<close> if \<open>\<LL>\<^sub>2 p\<close> and \<open>\<LL>\<^sub>2 (p \<rightarrow> q)\<close> |
  L2_1:  \<open>\<LL>\<^sub>2 (((p \<rightarrow> q) \<rightarrow> r) \<rightarrow> ((\<sim> p) \<rightarrow> r))\<close> |
  L2_2:  \<open>\<LL>\<^sub>2 (((p \<rightarrow> q) \<rightarrow> r) \<rightarrow> (q \<rightarrow> r))\<close> |
  L2_3:  \<open>\<LL>\<^sub>2 (((\<sim> p) \<rightarrow> r) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> r)))\<close>

lemma L2_4: \<open>\<LL>\<^sub>2 (p \<rightarrow> (q \<rightarrow> p))\<close>
  using L2_2 L2_MP by metis

lemma L2_5: \<open>\<LL>\<^sub>2 ((\<sim> p) \<rightarrow> (s \<rightarrow> (p \<rightarrow> p)))\<close>
  using L2_1 L2_4 L2_MP by metis

lemma L2_6: \<open>\<LL>\<^sub>2 (p \<rightarrow> p)\<close>
  using L2_3 L2_4 L2_5 L2_MP by metis

lemma L2_7: \<open>\<LL>\<^sub>2 ((\<sim> p) \<rightarrow> (p \<rightarrow> q))\<close>
  using L2_1 L2_6 L2_MP by metis

lemma L2_8: \<open>\<LL>\<^sub>2 ((q \<rightarrow> (p \<rightarrow> r)) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)))\<close>
  using L2_3 L2_7 L2_MP by metis

lemma L2_9: \<open>\<LL>\<^sub>2 ((\<sim> q) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)))\<close>
  using L2_1 L2_8 L2_MP by metis

lemma L2_10: \<open>\<LL>\<^sub>2 (r \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)))\<close>
  using L2_2 L2_4 L2_MP by metis

lemma L2_11: \<open>\<LL>\<^sub>2 ((q \<rightarrow> r) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)))\<close>
  using L2_3 L2_9 L2_10 L2_MP by metis

lemma L2_12: \<open>\<LL>\<^sub>2 (p \<rightarrow> (q \<rightarrow> (r \<rightarrow> p)))\<close>
  using L2_2 L2_4 L2_MP by metis

lemma L2_13: \<open>\<LL>\<^sub>2 ((q \<rightarrow> p) \<rightarrow> (q \<rightarrow> (r \<rightarrow> p)))\<close>
  using L2_8 L2_12 L2_MP by metis

lemma L2_14: \<open>\<LL>\<^sub>2 ((\<sim> p) \<rightarrow> (s \<rightarrow> (p \<rightarrow> q)))\<close>
  using L2_7 L2_13 L2_MP by metis

lemma L2_15: \<open>\<LL>\<^sub>2 ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> (q \<rightarrow> (p \<rightarrow> r)))\<close>
  using L2_3 L2_13 L2_14 L2_MP by metis

lemma L2_16: \<open>\<LL>\<^sub>2 ((p \<rightarrow> q) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> r)))\<close>
  using L2_11 L2_15 L2_MP by metis

lemma L2_17: \<open>\<LL>\<^sub>2 (p \<rightarrow> ((\<sim> p) \<rightarrow> q))\<close>
  using L2_7 L2_15 L2_MP by metis

lemma L2_18: \<open>\<LL>\<^sub>2 ((\<sim> (\<sim> p)) \<rightarrow> p)\<close>
  using L2_3 L2_4 L2_6 L2_17 L2_MP by metis

lemma L2_19: \<open>\<LL>\<^sub>2 (((\<sim> p) \<rightarrow> p) \<rightarrow> p)\<close>
  using L2_3 L2_6 L2_18 L2_MP by metis

theorem L2_iff_L1: \<open>\<LL>\<^sub>2 p \<longleftrightarrow> \<turnstile> p\<close>
proof
  have L1_L2_1: \<open>\<turnstile> (((p \<rightarrow> q) \<rightarrow> r) \<rightarrow> ((\<sim> p) \<rightarrow> r))\<close> for p q r
    using L1_completeness by simp
  have L1_L2_2: \<open>\<turnstile> (((p \<rightarrow> q) \<rightarrow> r) \<rightarrow> (q \<rightarrow> r))\<close> for p q r
    using L1_completeness by simp
  have L1_L2_3: \<open>\<turnstile> (((\<sim> p) \<rightarrow> r) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> r)))\<close> for p q r
    using L1_completeness by simp
  show \<open>\<turnstile> p\<close> if \<open>\<LL>\<^sub>2 p\<close>
    using that by (induct) (metis MP, metis L1_L2_1, metis L1_L2_2, metis L1_L2_3)
  show \<open>\<LL>\<^sub>2 p\<close> if \<open>\<turnstile> p\<close>
    using that by (induct) (metis L2_MP, metis L2_16, metis L2_19, metis L2_17)
qed

theorem L2_soundness: \<open>\<LL>\<^sub>2 p \<Longrightarrow> I \<Turnstile> p\<close>
  by (induct rule: L2.induct) auto

theorem L2_completeness: \<open>\<forall>I. (I \<Turnstile> p) \<Longrightarrow> \<LL>\<^sub>2 p\<close>
  using L2_iff_L1 by (simp add: L1_completeness)

section \<open>Soundness and Completeness\<close>

theorem main: \<open>valid p = \<LL>\<^sub>2 p\<close>
  unfolding valid_def using L2_soundness L2_completeness by blast

lemmas L2 = L2.intros main

end
