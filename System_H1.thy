(*
   Authors: Asta Halkjær From, Agnes Moesgård Eschen & Jørgen Villadsen, DTU Compute
*)

theory System_H1 imports System_L1 begin

text \<open>System H from David Hilbert: Die logischen Grundlagen der Mathematik (1922)\<close>

text \<open>Derivations are taken from: On Axiom Systems of Propositional Calculi. I
                                  by Yasuyuki Imai and Kiyoshi Iseki (1965)\<close>

inductive H (\<open>\<HH>\<close>) where
  H_MP: \<open>\<HH> q\<close> if \<open>\<HH> p\<close> and \<open>\<HH> (p \<rightarrow> q)\<close> |
  H_1:  \<open>\<HH> (p \<rightarrow> (q \<rightarrow> p))\<close> |
  H_2:  \<open>\<HH> ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> (q \<rightarrow> (p \<rightarrow> r)))\<close> |
  H_3:  \<open>\<HH> ((q \<rightarrow> r) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)))\<close> |
  H_4:  \<open>\<HH> (p \<rightarrow> ((\<sim> p) \<rightarrow> q))\<close> |
  H_5:  \<open>\<HH> ((p \<rightarrow> q) \<rightarrow> (((\<sim> p) \<rightarrow> q) \<rightarrow> q))\<close>

lemma H_6: \<open>\<HH> ((p \<rightarrow> q) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> r)))\<close>
  using H_2 H_3 H_MP by metis

lemma H_7: \<open>\<HH> (q \<rightarrow> (p \<rightarrow> p))\<close>
  using H_2 H_1 H_MP by metis

lemma H_8: \<open>\<HH> (p \<rightarrow> p)\<close>
  using H_1 H_7 H_MP by metis

lemma H_9: \<open>\<HH> (((\<sim> p) \<rightarrow> p) \<rightarrow> p)\<close>
  using H_5 H_8 H_MP by metis

theorem H_iff_L1: \<open>\<HH> p \<longleftrightarrow> \<turnstile> p\<close>
proof
  have L1_H_1: \<open>\<turnstile> (p \<rightarrow> (q \<rightarrow> p))\<close> for p q
    using L1_completeness by simp
  have L1_H_2: \<open>\<turnstile> ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> (q \<rightarrow> (p \<rightarrow> r)))\<close> for p q r
    using L1_completeness by simp
  have L1_H_3: \<open>\<turnstile> ((q \<rightarrow> r) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)))\<close> for p q r
    using L1_completeness by simp
  have L1_H_4: \<open>\<turnstile> (p \<rightarrow> ((\<sim> p) \<rightarrow> q))\<close> for p q
    using L1_completeness by simp
  have L1_H_5: \<open>\<turnstile> ((p \<rightarrow> q) \<rightarrow> (((\<sim> p) \<rightarrow> q) \<rightarrow> q))\<close> for p q
    using L1_completeness by simp
  show \<open>\<turnstile> p\<close> if \<open>\<HH> p\<close>
    using that by (induct) (metis MP, metis L1_H_1, metis L1_H_2,
        metis L1_H_3, metis L1_H_4, metis L1_H_5)
  show \<open>\<HH> p\<close> if \<open>\<turnstile> p\<close>
    using that by (induct) (metis H_MP, metis H_6, metis H_9, metis H_4)
qed

theorem H_soundness: \<open>\<HH> p \<Longrightarrow> I \<Turnstile> p\<close>
  by (induct rule: H.induct) auto

theorem H_completeness: \<open>\<forall>I. (I \<Turnstile> p) \<Longrightarrow> \<HH> p\<close>
  using H_iff_L1 by (simp add: L1_completeness)

section \<open>Soundness and Completeness\<close>

theorem main: \<open>valid p = \<HH> p\<close>
  unfolding valid_def using H_soundness H_completeness by blast

lemmas H1 = H.intros main

end
