(*
   Authors: Asta Halkjær From, Agnes Moesgård Eschen & Jørgen Villadsen, DTU Compute
*)

(* Mendelson Variant (Church) *)

theory System_M0 imports System_L1 begin

inductive M0 (\<open>\<MM>\<^sub>0\<close>) where
  M0_MP: \<open>\<MM>\<^sub>0 q\<close> if \<open>\<MM>\<^sub>0 p\<close> and \<open>\<MM>\<^sub>0 (p \<rightarrow> q)\<close> |
  M0_1:  \<open>\<MM>\<^sub>0 (p \<rightarrow> (q \<rightarrow> p))\<close> |
  M0_2:  \<open>\<MM>\<^sub>0 ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)))\<close> |
  M0_3:  \<open>\<MM>\<^sub>0 (((\<sim> p) \<rightarrow> q) \<rightarrow> (((\<sim> p) \<rightarrow> (\<sim> q)) \<rightarrow> p))\<close>

lemma M0_4: \<open>\<MM>\<^sub>0 ((\<sim> p) \<rightarrow> (((\<sim> q) \<rightarrow> (\<sim> p)) \<rightarrow> (p \<rightarrow> q)))\<close>
  using M0_1 M0_2 M0_3 M0_MP by metis

lemma M0_5: \<open>\<MM>\<^sub>0 ((\<sim> p) \<rightarrow> (p \<rightarrow> q))\<close>
  using M0_1 M0_2 M0_4 M0_MP by metis

lemma M0_6: \<open>\<MM>\<^sub>0 (((\<sim> q) \<rightarrow> q) \<rightarrow> ((\<sim> q) \<rightarrow> p))\<close>
  using M0_2 M0_5 M0_MP by metis

lemma M0_7: \<open>\<MM>\<^sub>0 (q \<rightarrow> (((\<sim> q) \<rightarrow> q) \<rightarrow> ((\<sim> q) \<rightarrow> p)))\<close>
  using M0_1 M0_6 M0_MP by metis

lemma M0_8: \<open>\<MM>\<^sub>0 (q \<rightarrow> ((\<sim> q) \<rightarrow> p))\<close>
  using M0_1 M0_2 M0_7 M0_MP by metis

lemma M0_10: \<open>\<MM>\<^sub>0 ((q \<rightarrow> r) \<rightarrow> ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r))))\<close>
  using M0_1 M0_2 M0_MP by metis

lemma M0_11: \<open>\<MM>\<^sub>0 ((q \<rightarrow> r) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)))\<close>
  using M0_1 M0_2 M0_10 M0_MP by metis

lemma M0_12: \<open>\<MM>\<^sub>0 (((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> q)) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> r)))\<close>
  using M0_2 M0_11 M0_MP by metis

lemma M0_13: \<open>\<MM>\<^sub>0 ((p \<rightarrow> q) \<rightarrow> (((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> q)) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> r))))\<close>
  using M0_1 M0_12 M0_MP by metis

lemma M0_14: \<open>\<MM>\<^sub>0 ((p \<rightarrow> q) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> r)))\<close>
  using M0_1 M0_2 M0_13 M0_MP by metis

lemma M0_15: \<open>\<MM>\<^sub>0 (((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> (p \<rightarrow> q)) \<rightarrow> ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> (p \<rightarrow> r)))\<close>
  using M0_2 M0_MP by metis

lemma M0_16: \<open>\<MM>\<^sub>0 ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> p))\<close>
  using M0_1 M0_2 M0_MP by metis

lemma M0_17: \<open>\<MM>\<^sub>0 (p \<rightarrow> p)\<close>
  using M0_1 M0_16 M0_MP by metis

lemma M0_19: \<open>\<MM>\<^sub>0 ((p \<rightarrow> (p \<rightarrow> q)) \<rightarrow> (p \<rightarrow> q))\<close>
  using M0_15 M0_16 M0_MP by metis

lemma M0_21: \<open>\<MM>\<^sub>0 (((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)) \<rightarrow> (q \<rightarrow> (p \<rightarrow> q)))\<close>
  using M0_1 M0_MP by metis

lemma M0_22: \<open>\<MM>\<^sub>0 (((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)) \<rightarrow> (q \<rightarrow> (p \<rightarrow> r)))\<close>
  using M0_1 M0_14 M0_MP by blast

lemma M0_23: \<open>\<MM>\<^sub>0 ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> (q \<rightarrow> (p \<rightarrow> r)))\<close>
  using M0_2 M0_11 M0_22 M0_MP by metis

lemma M0_26: \<open>\<MM>\<^sub>0 (((\<sim> q) \<rightarrow> q) \<rightarrow> (((\<sim> q) \<rightarrow> q) \<rightarrow> q))\<close>
  using M0_17 M0_23 M0_MP by (metis M0_1 M0_3)

lemma M0_27: \<open>\<MM>\<^sub>0 (((\<sim> p) \<rightarrow> p) \<rightarrow> p)\<close>
  using M0_19 M0_26 M0_MP by metis

theorem M0_iff_L1: \<open>\<MM>\<^sub>0 p \<longleftrightarrow> \<turnstile> p\<close>
proof
  have L1_M0_1: \<open>\<turnstile> (p \<rightarrow> (q \<rightarrow> p))\<close> for p q
    using L1_completeness by simp
  have L1_M0_2: \<open>\<turnstile> ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)))\<close> for p q r
    using L1_completeness by simp
  have L1_M0_3: \<open>\<turnstile> (((\<sim> p) \<rightarrow> q) \<rightarrow> (((\<sim> p) \<rightarrow> (\<sim> q)) \<rightarrow> p))\<close> for p q
    using L1_completeness by simp
  show \<open>\<turnstile> p\<close> if \<open>\<MM>\<^sub>0 p\<close>
    using that by (induct) (metis MP, metis L1_M0_1, metis L1_M0_2, metis L1_M0_3)
  show \<open>\<MM>\<^sub>0 p\<close> if \<open>\<turnstile> p\<close>
    using that by (induct) (metis M0_MP, metis M0_14, metis M0_27, metis M0_8)
qed

theorem M0_soundness: \<open>\<MM>\<^sub>0 p \<Longrightarrow> I \<Turnstile> p\<close>
  by (induct rule: M0.induct) auto

theorem M0_completeness: \<open>\<forall>I. (I \<Turnstile> p) \<Longrightarrow> \<MM>\<^sub>0 p\<close>
  using M0_iff_L1 by (simp add: L1_completeness)

section \<open>Soundness and Completeness\<close>

theorem main: \<open>valid p = \<MM>\<^sub>0 p\<close>
  unfolding valid_def using M0_soundness M0_completeness by blast

lemmas M0 = M0.intros main

end
