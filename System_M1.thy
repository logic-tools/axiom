(*
   Authors: Asta Halkjær From, Agnes Moesgård Eschen & Jørgen Villadsen, DTU Compute
*)

theory System_M1 imports System_L1 begin

text \<open>Mendelson\<close>

inductive M (\<open>\<MM>\<close>) where
  M_MP: \<open>\<MM> q\<close> if \<open>\<MM> p\<close> and \<open>\<MM> (p \<rightarrow> q)\<close> |
  M_1:  \<open>\<MM> (p \<rightarrow> (q \<rightarrow> p))\<close> |
  M_2:  \<open>\<MM> ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)))\<close> |
  M_3:  \<open>\<MM> (((\<sim> p) \<rightarrow> (\<sim> q)) \<rightarrow> (((\<sim> p) \<rightarrow> q) \<rightarrow> p))\<close>

lemma M_4: \<open>\<MM> ((\<sim> p) \<rightarrow> (((\<sim> q) \<rightarrow> (\<sim> p)) \<rightarrow> (p \<rightarrow> q)))\<close>
  using M_1 M_2 M_3 M_MP by metis

lemma M_5: \<open>\<MM> ((\<sim> p) \<rightarrow> (p \<rightarrow> q))\<close>
  using M_1 M_2 M_4 M_MP by metis

lemma M_6: \<open>\<MM> (((\<sim> q) \<rightarrow> q) \<rightarrow> ((\<sim> q) \<rightarrow> p))\<close>
  using M_2 M_5 M_MP by metis

lemma M_7: \<open>\<MM> (q \<rightarrow> (((\<sim> q) \<rightarrow> q) \<rightarrow> ((\<sim> q) \<rightarrow> p)))\<close>
  using M_1 M_6 M_MP by metis

lemma M_8: \<open>\<MM> (q \<rightarrow> ((\<sim> q) \<rightarrow> p))\<close>
  using M_1 M_2 M_7 M_MP by metis

lemma M_9: \<open>\<MM> (p \<rightarrow> ((\<sim> p) \<rightarrow> q))\<close>
  using M_8.

lemma M_10: \<open>\<MM> ((q \<rightarrow> r) \<rightarrow> ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r))))\<close>
  using M_1 M_2 M_MP by metis

lemma M_11: \<open>\<MM> ((q \<rightarrow> r) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)))\<close>
  using M_1 M_2 M_10 M_MP by metis

lemma M_12: \<open>\<MM> (((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> q)) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> r)))\<close>
  using M_2 M_11 M_MP by metis

lemma M_13: \<open>\<MM> ((p \<rightarrow> q) \<rightarrow> (((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> q)) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> r))))\<close>
  using M_1 M_12 M_MP by metis

lemma M_14: \<open>\<MM> ((p \<rightarrow> q) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> r)))\<close>
  using M_1 M_2 M_13 M_MP by metis

lemma M_15: \<open>\<MM> (((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> (p \<rightarrow> q)) \<rightarrow> ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> (p \<rightarrow> r)))\<close>
  using M_2 M_MP by metis

lemma M_16: \<open>\<MM> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> p))\<close>
  using M_1 M_2 M_MP by metis

lemma M_17: \<open>\<MM> (p \<rightarrow> p)\<close>
  using M_1 M_16 M_MP by metis

lemma M_18: \<open>\<MM> ((p \<rightarrow> (p \<rightarrow> q)) \<rightarrow> (p \<rightarrow> p))\<close>
  using M_1 M_17 M_MP by metis (* under substitution this lemma is the same as M_16 *)

lemma M_19: \<open>\<MM> ((p \<rightarrow> (p \<rightarrow> q)) \<rightarrow> (p \<rightarrow> q))\<close>
  using M_15 M_18 M_MP by metis

lemma M_20: \<open>\<MM> (((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)) \<rightarrow> ((q \<rightarrow> (p \<rightarrow> q)) \<rightarrow> (q \<rightarrow> (p \<rightarrow> r))))\<close>
  using M_11.

lemma M_21: \<open>\<MM> (((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)) \<rightarrow> (q \<rightarrow> (p \<rightarrow> q)))\<close>
  using M_1 M_MP by metis

lemma M_22: \<open>\<MM> (((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)) \<rightarrow> (q \<rightarrow> (p \<rightarrow> r)))\<close>
  using M_2 M_20 M_21 M_MP by metis

lemma M_23: \<open>\<MM> ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> (q \<rightarrow> (p \<rightarrow> r)))\<close>
  using M_2 M_11 M_22 M_MP by metis

lemma M_24: \<open>\<MM> (((\<sim> q) \<rightarrow> (\<sim> p)) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> r)))\<close>
  using M_3 M_11 M_14 M_MP oops

lemma M_25: \<open>\<MM> (((\<sim> q) \<rightarrow> q) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> r)))\<close>
  using M_6 M_11 M_MP oops

lemma M_26: \<open>\<MM> (((\<sim> q) \<rightarrow> q) \<rightarrow> (((\<sim> q) \<rightarrow> q) \<rightarrow> q))\<close>
  using M_17 M_23 M_MP by (metis M_1 M_3)

lemma M_27: \<open>\<MM> (((\<sim> p) \<rightarrow> p) \<rightarrow> p)\<close>
  using M_19 M_26 M_MP by metis

theorem M_iff_L1: \<open>\<MM> p \<longleftrightarrow> \<turnstile> p\<close>
proof
  have L1_M_1: \<open>\<turnstile> (p \<rightarrow> (q \<rightarrow> p))\<close> for p q
    using L1_completeness by simp
  have L1_M_2: \<open>\<turnstile> ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)))\<close> for p q r
    using L1_completeness by simp
  have L1_M_3: \<open>\<turnstile> (((\<sim> p) \<rightarrow> (\<sim> q)) \<rightarrow> (((\<sim> p) \<rightarrow> q) \<rightarrow> p))\<close> for p q
    using L1_completeness by simp
  show \<open>\<turnstile> p\<close> if \<open>\<MM> p\<close>
    using that by (induct) (metis MP, metis L1_M_1, metis L1_M_2, metis L1_M_3)
  show \<open>\<MM> p\<close> if \<open>\<turnstile> p\<close>
    using that by (induct) (metis M_MP, metis M_14, metis M_27, metis M_9)
qed

theorem M_soundness: \<open>\<MM> p \<Longrightarrow> I \<Turnstile> p\<close>
  by (induct rule: M.induct) auto

theorem M_completeness: \<open>\<forall>I. (I \<Turnstile> p) \<Longrightarrow> \<MM> p\<close>
  using M_iff_L1 by (simp add: L1_completeness)

section \<open>Soundness and Completeness\<close>

theorem main: \<open>valid p = \<MM> p\<close>
  unfolding valid_def using M_soundness M_completeness by blast

lemmas M1 = M.intros main

end
