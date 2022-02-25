(*
   Authors: Asta Halkjær From, Agnes Moesgård Eschen & Jørgen Villadsen, DTU Compute
*)

theory System_S0 imports System_L1 begin

text \<open>System S1 from Boleslaw Sobocinski: Note on a Problem of Paul Barnays (1955) \<close>

text \<open>Derivations are taken from the above paper\<close>

inductive S0 (\<open>\<SS>\<^sub>0\<close>) where
  S0_MP: \<open>\<SS>\<^sub>0 q\<close> if \<open>\<SS>\<^sub>0 p\<close> and \<open>\<SS>\<^sub>0 (p \<rightarrow> q)\<close> |
  S0_1:  \<open>\<SS>\<^sub>0 (p \<rightarrow> (q \<rightarrow> (r \<rightarrow> (s \<rightarrow> p))))\<close> |
  S0_2:  \<open>\<SS>\<^sub>0 ((\<sim> q) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)))\<close> |
  S0_3:  \<open>\<SS>\<^sub>0 (((\<sim> p) \<rightarrow> q) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> q))\<close>

lemma S0_4: \<open>\<SS>\<^sub>0 ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> (r \<rightarrow> q)))\<close>
  using S0_1 S0_2 S0_3 S0_MP by metis

lemma S0_5: \<open>\<SS>\<^sub>0 ((p \<rightarrow> q) \<rightarrow> (s \<rightarrow> (p \<rightarrow> (r \<rightarrow> q))))\<close>
  using S0_4 S0_MP by metis

lemma S0_6: \<open>\<SS>\<^sub>0 ((p \<rightarrow> q) \<rightarrow> (v \<rightarrow> (s \<rightarrow> (p \<rightarrow> (r \<rightarrow> q)))))\<close>
  using S0_4 S0_5 S0_MP by metis

lemma S0_7: \<open>\<SS>\<^sub>0 ((s \<rightarrow> (p \<rightarrow> q)) \<rightarrow> (s \<rightarrow> (p \<rightarrow> (r \<rightarrow> q))))\<close>
  using S0_2 S0_3 S0_6 S0_MP by metis

lemma S0_8: \<open>\<SS>\<^sub>0 ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> (s \<rightarrow> (r \<rightarrow> q))))\<close>
  using S0_4 S0_7 S0_MP by metis

lemma S0_9: \<open>\<SS>\<^sub>0 ((\<sim> q) \<rightarrow> (s \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r))))\<close>
  using S0_2 S0_4 S0_MP by metis

lemma S0_10: \<open>\<SS>\<^sub>0 (q \<rightarrow> ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> (p \<rightarrow> r)))\<close>
  using S0_3 S0_8 S0_9 S0_MP by metis

lemma S0_11: \<open>\<SS>\<^sub>0 ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> (q \<rightarrow> (p \<rightarrow> r)))\<close>
  using S0_10 S0_MP by metis

lemma S0_12: \<open>\<SS>\<^sub>0 (p \<rightarrow> (r \<rightarrow> (s \<rightarrow> p)))\<close>
  using S0_1 S0_11 S0_MP by metis

lemma S0_13: \<open>\<SS>\<^sub>0 (p \<rightarrow> (s \<rightarrow> p))\<close>
  using S0_11 S0_12 S0_MP by metis

lemma S0_14: \<open>\<SS>\<^sub>0 (p \<rightarrow> p)\<close>
  using S0_11 S0_13 S0_MP by metis

lemma S0_15: \<open>\<SS>\<^sub>0 (p \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (s \<rightarrow> (r \<rightarrow> q))))\<close>
  using S0_8 S0_11 S0_MP by metis

lemma S0_16: \<open>\<SS>\<^sub>0 ((q \<rightarrow> r) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)))\<close>
  using S0_3 S0_9 S0_15 S0_MP by metis

lemma S0_17: \<open>\<SS>\<^sub>0 ((p \<rightarrow> q) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> r)))\<close>
  using S0_11 S0_16 S0_MP by metis

lemma S0_18: \<open>\<SS>\<^sub>0 (((\<sim> p) \<rightarrow> p) \<rightarrow> p)\<close>
  using S0_3 S0_11 S0_14 S0_17 S0_MP by metis

lemma S0_19: \<open>\<SS>\<^sub>0 ((\<sim> p) \<rightarrow> (p \<rightarrow> q))\<close>
  using S0_2 S0_11 S0_14 S0_18 S0_MP by metis

lemma S0_20: \<open>\<SS>\<^sub>0 (p \<rightarrow> ((\<sim> p) \<rightarrow> q))\<close>
  using S0_11 S0_19 S0_MP by metis

theorem S0_if_L1: \<open>\<SS>\<^sub>0 p\<close> if \<open>\<turnstile> p\<close> using that
  by (induct) (metis S0.intros(1), metis S0_17, metis S0_18, metis S0_20)

theorem S0_soundness: \<open>\<SS>\<^sub>0 p \<Longrightarrow> I \<Turnstile> p\<close>
  by (induct rule: S0.induct) auto

theorem S0_completeness: \<open>\<forall>I. (I \<Turnstile> p) \<Longrightarrow> \<SS>\<^sub>0 p\<close>
  using S0_if_L1 by (simp add: L1_completeness)

section \<open>Soundness and Completeness\<close>

theorem main: \<open>valid p = \<SS>\<^sub>0 p\<close>
  unfolding valid_def using S0_soundness S0_completeness by blast

lemmas S0 = S0.intros main

end
