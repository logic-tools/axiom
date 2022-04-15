(*
  Authors: Asta Halkjær From, Agnes Moesgård Eschen & Jørgen Villadsen, DTU Compute
*)

theory LT4 imports System_L1 begin

text \<open>System from Jan Lukasiewicz and Alfred Tarski (1930): Untersuchungen über den Aussagenkalkül\<close>

text \<open>Inspired by Shotaro Tanaka (1965): On Axiom Systems of Propositional Calculi. XIII\<close>

inductive LT (\<open>\<tturnstile>\<close>) where
  LT_MP: \<open>\<tturnstile> q\<close> if \<open>\<tturnstile> p\<close> and \<open>\<tturnstile> (p \<rightarrow> q)\<close> |
  LT_3: \<open>\<tturnstile> (p \<rightarrow> (q \<rightarrow> p))\<close> |
  LT_4: \<open>\<tturnstile> ((\<sim> r \<rightarrow> (s \<rightarrow> \<sim> t)) \<rightarrow> ((r \<rightarrow> (s \<rightarrow> u)) \<rightarrow> ((t \<rightarrow> s) \<rightarrow> (t \<rightarrow> u))))\<close>

lemma LT_5: \<open>\<tturnstile> ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)))\<close>
  using LT_3 LT_4 LT_MP by metis

lemma LT_15: \<open>\<tturnstile> (((p \<rightarrow> q) \<rightarrow> r) \<rightarrow> (q \<rightarrow> r))\<close>
  using LT_3 LT_5 LT_MP by metis

lemma LT_11: \<open>\<tturnstile> ((p \<rightarrow> q) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> r)))\<close>
  using LT_3 LT_5 LT_MP by metis

lemma LT_20: \<open>\<tturnstile> ((\<sim> p \<rightarrow> p) \<rightarrow> p)\<close>
  using LT_4 LT_15 LT_MP by metis

lemma LT_21: \<open>\<tturnstile> (p \<rightarrow> (\<sim> p \<rightarrow> q))\<close>
  using LT_4 LT_15 LT_MP by metis

theorem LT_iff_L1: \<open>\<tturnstile> p \<longleftrightarrow> \<turnstile> p\<close>
proof
  have L1_LT_3: \<open>\<turnstile> (p \<rightarrow> (q \<rightarrow> p))\<close> for p q
    using L1_completeness by simp
  have L1_LT_4: \<open>\<turnstile> ((\<sim> r \<rightarrow> (s \<rightarrow> \<sim> t)) \<rightarrow> ((r \<rightarrow> (s \<rightarrow> u)) \<rightarrow> ((t \<rightarrow> s) \<rightarrow> (t \<rightarrow> u))))\<close> for r s t u
    using L1_completeness by simp
  show \<open>\<turnstile> p\<close> if \<open>\<tturnstile> p\<close>
    using that by (induct) (metis MP, metis L1_LT_3, metis L1_LT_4)
  show \<open>\<tturnstile> p\<close> if \<open>\<turnstile> p\<close>
    using that by (induct) (metis LT_MP, metis LT_11, metis LT_20, metis LT_21)
qed

theorem LT_soundness: \<open>\<tturnstile> p \<Longrightarrow> I \<Turnstile> p\<close>
  by (induct rule: LT.induct) auto

theorem LT_completeness: \<open>\<forall>I. (I \<Turnstile> p) \<Longrightarrow> \<tturnstile> p\<close>
  using LT_iff_L1 by (simp add: L1_completeness)

section \<open>Soundness and Completeness\<close>

theorem main: \<open>valid p = \<tturnstile> p\<close>
  unfolding valid_def using LT_soundness LT_completeness by blast

lemmas LT = LT.intros main

end
