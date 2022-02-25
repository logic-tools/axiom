(*
   Authors: Asta Halkjær From, Agnes Moesgård Eschen & Jørgen Villadsen, DTU Compute
*)

theory System_L0 imports System_L1 begin

inductive L0 (\<open>\<LL>\<^sub>0\<close>) where
  \<open>\<LL>\<^sub>0 q\<close> if \<open>\<LL>\<^sub>0 p\<close> and \<open>\<LL>\<^sub>0 (p \<rightarrow> q)\<close> |
  \<open>\<LL>\<^sub>0 ((p \<rightarrow> q) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> r)))\<close> |
  \<open>\<LL>\<^sub>0 (((\<sim> p) \<rightarrow> q) \<rightarrow> ((q \<rightarrow> p) \<rightarrow> p))\<close> |
  \<open>\<LL>\<^sub>0 (p \<rightarrow> ((\<sim> p) \<rightarrow> q))\<close>

lemma L0_lemma: \<open>\<LL>\<^sub>0 (((\<sim> p) \<rightarrow> p) \<rightarrow> p)\<close>
  by (metis L0.intros)

theorem L0_soundness: \<open>\<LL>\<^sub>0 p \<Longrightarrow> I \<Turnstile> p\<close>
  by (induct rule: L0.induct) (simp, simp, metis semantics.simps(2,3), simp)

theorem L0_completeness: \<open>\<forall>I. (I \<Turnstile> p) \<Longrightarrow> \<LL>\<^sub>0 p\<close>
  by (metis (full_types) L0_lemma L1_completeness L0.simps Axiomatics.inducts)

section \<open>Soundness and Completeness\<close>

theorem main: \<open>valid p = \<LL>\<^sub>0 p\<close>
  unfolding valid_def using L0_soundness L0_completeness by blast

lemmas L0 = L0.intros main

end
